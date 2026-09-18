import Lean
import Leant2.Core.Types
import Leant2.Native.Transaction
/-!
# Construction search (unified proposal, Sections 5, 7, 15)

A depth-bounded search over a list of obligations. Every alternative runs
inside a saved state and is committed only if the *whole* continuation
(`children ++ rest`) succeeds: the continuation discipline of Decision 2.2.

Each obligation carries its own remaining depth (the depth of the subterm
that may fill it); children of a rule get one less than their parent, and
sibling obligations keep theirs.

Rules, in the order tried on each goal:
introduction; invertible destructuring of single-constructor locals;
reflexivity; exact locals; type frontier for `Sort`-valued goals; projections
of local structure values as heads; constructors of the target's inductive
head; application of locals (most recent first); bounded case analysis on
multi-constructor locals; head-filtered providers; the proof portfolio on
closed propositions.

The search enumerates candidates: the leaf callback decides whether to stop.
-/
namespace Leant2

open Lean Meta Elab

/-- A provider with the head constant of its conclusion, if the conclusion is
constant-headed; `none` means the conclusion is a variable (or a sort). For
variable-headed providers, `argHeads` lists the constant heads of the
explicit argument types: such a provider is tried only when some local has one
of those heads (demand-directed retrieval, Section 9). -/
structure Provider where
  name : Name
  head : Option Name
  argHeads : Array Name := #[]
  /-- Bypass the demand filter (eliminators such as `Empty.elim`). -/
  always : Bool := false
  /-- Number of explicit arguments; providers are tried in increasing order. -/
  arity : Nat := 0
  deriving Inhabited

structure SearchConfig where
  maxDepth : Nat := 10
  maxSplits : Nat := 2
  /-- Global constants that may be applied. -/
  providers : Array Provider := #[]
  /-- Closed types tried for `Sort`-valued holes. -/
  typeFrontier : Array Expr := #[]
  /-- Allow `Classical.em` and friends as providers. -/
  classical : Bool := false
  /-- Run the proof portfolio on closed propositions. -/
  proofPortfolio : Bool := true
  /-- Try structural recursion on recursive inductive locals before constructors
  and providers (used when a behavioral contract is present, Section 17). -/
  recursionFirst : Bool := false
  /-- The contract `fun f => P f`, when there is one. -/
  contract : Option Expr := none
  /-- Precomputed deciders for the contract's conjuncts (left to right):
  each is `fun f => C_i f` with `fun f => inst_i` when `C_i f` is decidable. -/
  residual : Array (Expr × Option Expr) := #[]
  /-- The root hole of the current pass (a `Subtype` when a contract is present). -/
  root : Option MVarId := none

/-- Leaf callback: receives the search state with all goals assigned and
returns `true` to stop the search. -/
abbrev Leaf := SearchM Bool

/-- An obligation with its remaining depth and whether it has already been
deferred once (Section 15.1.3: type-argument holes and holes whose type still
contains metavariables are scheduled after their siblings, which usually
determine them). -/
structure Goal where
  mvar : MVarId
  depth : Nat
  /-- How many times this goal has been deferred. Type-argument holes may be
  deferred twice so that an instance sibling (itself deferred once while its
  type is open) can determine them. -/
  deferred : Nat := 0
  /-- Locals that may not be applied again below this goal: a Church-encoded
  list folded once is not folded again inside its own step or seed. -/
  consumed : List FVarId := []

/-- Run one alternative. If it does not stop the search, restore the state so
the next alternative starts from the same point. -/
def alternative (act : SearchM Bool) : SearchM Bool := do
  let saved : Meta.SavedState ← Meta.saveState
  try
    if ← act then return true
  catch e =>
    if isInterrupt e then throw e
    if leant2.traceNodes.get (← getOptions) then
      IO.println s!"[leant2]     alternative failed with: {← e.toMessageData.toString}"
  saved.restore
  return false

/-- Names never used as providers even when discovered. -/
def forbiddenProviders : Array Name :=
  #[``sorryAx, ``lcProof, ``lcUnreachable, ``Lean.ofReduceBool, ``Lean.ofReduceNat,
    ``Classical.choice, ``Classical.choose, ``Classical.choose_spec, ``Classical.propDecidable]

/-- Compute the conclusion head of a constant. -/
def mkProvider (n : Name) : MetaM (Option Provider) := do
  let some ci := (← getEnv).find? n | return none
  let ty ← instantiateMVars ci.type
  let (concl, argHeads, arity) ← forallTelescopeReducing ty fun xs b => do
    let b ← whnfR b
    let mut hs : Array Name := #[]
    let mut arity := 0
    for x in xs do
      let xt ← whnfR (← inferType x)
      if let .const c _ := xt.getAppFn then hs := hs.push c
      if (← x.fvarId!.getBinderInfo).isExplicit then arity := arity + 1
    return (b.getAppFn, hs, arity)
  let head := match concl with
    | .const c _ => some c
    | _ => none
  -- type constructors and predicates (`Wrap : Type 1 → Type`, `P : Nat → Prop`) are
  -- not term providers; type holes are filled by the frontier instead
  if concl.isSort then return none
  return some { name := n, head, argHeads, arity }

/-- Build providers, ordered by increasing explicit arity (stable). -/
def mkProviders (ns : Array Name) (always := false) : MetaM (Array Provider) := do
  let mut out := #[]
  for n in ns do
    if forbiddenProviders.contains n then continue
    if let some p ← mkProvider n then out := out.push { p with always }
  return out.insertionSort fun a b => a.arity < b.arity

/-- Constants the classical lane adds. `absurd` is deliberately absent: an
arbitrary `Prop` hole explodes the search. -/
def classicalProviders : MetaM (Array Provider) :=
  mkProviders #[``Classical.em, ``Classical.byContradiction, ``False.elim] (always := true)

/-- Self-time profile of the search rules, printed by the lane trace. -/
initialize profTimers : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]

/-- Accumulate the wall time of a non-recursive step under `k` (nanoseconds). -/
def timed (k : String) (act : SearchM α) : SearchM α := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let dt := (← IO.monoNanosNow) - t0
  profTimers.modify fun a =>
    match a.findIdx? (·.1 == k) with
    | some i => a.modify i fun (k, v) => (k, v + dt)
    | none => a.push (k, dt)
  return r

private def isTypeSort (e : Expr) : MetaM Bool := do
  match ← whnfR e with
  | .sort _ => return true
  | _ => return false

/-- Types invented from the local context: local type variables, types of
locals, and one level of arrows over them (Church-style folds with a function
accumulator instantiate a result type at `R -> R`). -/
private def localFrontier (locals : Array LocalDecl) : MetaM (Array Expr) := do
  let mut frontier : Array Expr := #[]
  for decl in locals do
    let dty ← instantiateMVars decl.type
    if (← whnfR dty).isSort then
      unless frontier.contains decl.toExpr do frontier := frontier.push decl.toExpr
    else if ← isTypeSort (← inferType dty) then
      unless frontier.contains dty do frontier := frontier.push dty
  let base := frontier
  for a in base do
    for b in base do
      let arrow ← mkArrow a b
      unless frontier.contains arrow do frontier := frontier.push arrow
  return frontier

/-- Instantiate metavariables *including* delayed assignments whose pending
hole is still open. The result may mention metavariables whose local
contexts no longer match; it is used for reduction only, never assigned. -/
partial def instantiatePartial (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let rec go (e : Expr) : MetaM Expr := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let args ← args.mapM go
      if let .mvar m := f then
        if let some da ← getDelayedMVarAssignment? m then
          if args.size ≥ da.fvars.size then
            let pv ← go (← instantiateMVars (mkMVar da.mvarIdPending))
            let body := (pv.abstract da.fvars).instantiateRevRange 0 da.fvars.size args
            return mkAppN body (args.extract da.fvars.size args.size)
      return mkAppN (← go f) args
    | .lam n t b bi => return .lam n (← go t) (← go b) bi
    | .forallE n t b bi => return .forallE n (← go t) (← go b) bi
    | .letE n t v b nd => return .letE n (← go t) (← go v) (← go b) nd
    | .mdata d b => return .mdata d (← go b)
    | .proj s i b => return .proj s i (← go b)
    | .mvar m =>
      if let some da ← getDelayedMVarAssignment? m then
        if da.fvars.isEmpty then return ← go (← instantiateMVars (mkMVar da.mvarIdPending))
      return e
    | _ => return e
  go e

/-- Result of evaluating the contract on a (possibly partial) program. -/
inductive Residual where
  | refuted
  | proved (pf : Expr)
  | stuck

/-- Left-to-right conjuncts of a right- or left-nested `And` chain. -/
partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then conjuncts (e.getArg! 0) ++ conjuncts (e.getArg! 1) else #[e]

/-- Precompute the residual deciders of a contract `fun f => P f` at `T`. -/
def mkResidual (contract : Expr) (ty : Expr) : MetaM (Array (Expr × Option Expr)) :=
  withLocalDecl `f .default ty fun f => do
    let body := (contract.beta #[f])
    let mut out := #[]
    for c in conjuncts body do
      let inst? : Option Expr ← (do
        try synthInstance? (mkApp (mkConst ``Decidable) c)
        catch e => if isInterrupt e then throw e else pure none : MetaM (Option Expr))
      let inst? ← inst?.mapM fun i => do mkLambdaFVars #[f] (← instantiateMVars i)
      out := out.push (← mkLambdaFVars #[f] c, inst?)
    return out

/-- The program a root hole currently holds: `Subtype.val` of the partially
instantiated root (including delayed assignments), or the root itself. -/
def rootProgram (cfg : SearchConfig) : MetaM (Option Expr) := do
  let some root := cfg.root | return none
  let p ← instantiatePartial (mkMVar root)
  if cfg.contract.isSome then
    if p.isAppOfArity ``Subtype.mk 4 then return some (p.getArg! 2) else return none
  return some p

/-- Decide a closed-or-partial decidable proposition by kernel reduction, which
evaluates recursors and literals natively and is stuck (not failing) on open
holes. `none` when reduction does not reach a Boolean constant. -/
def kernelDecide (t inst : Expr) : MetaM (Option Bool × Option Expr) := do
  let e := mkApp2 (mkConst ``Decidable.decide) t inst
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r =>
    if r.isConstOf ``Bool.true then return (some true, none)
    if r.isConstOf ``Bool.false then return (some false, none)
    return (none, some r)
  | .error _ => return (none, none)

/-- Rebuild the `And` tree of a contract from leaf proofs, left to right. -/
private partial def buildAndProof (proofs : Array (Option Expr)) (t : Expr) (k : Nat) : Expr × Nat :=
  if t.isAppOfArity ``And 2 then
    let (l, k) := buildAndProof proofs (t.getArg! 0) k
    let (r, k) := buildAndProof proofs (t.getArg! 1) k
    (mkApp4 (mkConst ``And.intro) (t.getArg! 0) (t.getArg! 1) l r, k)
  else (proofs[k]!.get!, k + 1)

/-- Evaluate the precomputed conjunct deciders on `p`. A conjunct reducing to
`false` refutes; when every conjunct reduces to `true` the proof is assembled
(the contract's `And` nesting is rebuilt from `cfg.contract`). Conjuncts
without a decider, or stuck on open holes, leave the result `stuck`. -/
def evalResidual (cfg : SearchConfig) (p : Expr) : SearchM Residual := do
  let mut proofs : Array (Option Expr) := #[]
  let mut blockers : Array MVarId := #[]
  for (pred, inst?) in cfg.residual do
    let some inst := inst? | proofs := proofs.push none; continue
    let t := pred.beta #[p]
    let i := inst.beta #[p]
    let (r, stuck?) ← kernelDecide t i
    if r == some false then return .refuted
    if let some stuck := stuck? then
      blockers := blockers ++ (stuck.collectMVars {}).result
    if r == some true && !p.hasExprMVar then
      proofs := proofs.push (some (mkApp3 (mkConst ``of_decide_eq_true) t i
        (mkApp2 (mkConst ``Eq.refl [Level.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true))))
    else proofs := proofs.push none
  if p.hasExprMVar then
    -- remember where evaluation stopped; the check is repeated only once one of
    -- these holes is filled
    (← read).residualBlockers.set blockers
    return .stuck
  if proofs.any (·.isNone) then return .stuck
  let some contract := cfg.contract | return .stuck
  let (pf, _) := buildAndProof proofs (contract.beta #[p]) 0
  return .proved pf

/-- Residual evaluation of a pending contract goal (Section 10): a conjunct
that already reduces to `false` on the partial program refutes the branch.
Uses the precomputed deciders when present, otherwise generic decision. -/
partial def partialRefute (cfg : SearchConfig) (t : Expr) : SearchM Bool := do
  if !cfg.residual.isEmpty then
    -- still stuck on the same open holes: nothing new to decide. A blocker that
    -- no longer exists (rolled back) or is assigned (directly, or through its
    -- delayed pending hole) means the program moved on.
    let blockers ← (← read).residualBlockers.get
    if !blockers.isEmpty then
      let mut same := true
      for m in blockers do
        match (← getMCtx).findDecl? m with
        | none => same := false; break
        | some _ => pure ()
        if ← m.isAssigned then same := false; break
        if let some da ← getDelayedMVarAssignment? m then
          if ← da.mvarIdPending.isAssigned then same := false; break
      if same then return false
    let some p ← timed "residual.instantiate" (rootProgram cfg) | return false
    let r ← timed "residual.decide" (evalResidual cfg p)
    if leant2.traceNodes.get (← getOptions) then
      IO.println s!"[leant2]     residual {if r matches .refuted then "REFUTED" else "stuck"} {(← ppExpr p).pretty 100000}"
    return r matches .refuted
  let t := (← instantiatePartial t).headBeta
  if t.isAppOfArity ``And 2 then
    if ← partialRefute cfg (t.getArg! 0) then return true
    return ← partialRefute cfg (t.getArg! 1)
  let inst? : Option Expr ← (do
    try synthInstance? (mkApp (mkConst ``Decidable) t)
    catch e => if isInterrupt e then throw e else pure none : MetaM (Option Expr))
  let some inst := inst? | return false
  return (← kernelDecide t inst).1 == some false

/-- The tactic part of the portfolio on a closed goal; messages the tactics
log are discarded. -/
def tacticProve (g : MVarId) : MetaM Bool := do
  let savedMsgs := (← getThe Core.State).messages
  let r ← Term.TermElabM.run' do
    let stx ← `(tactic| first | rfl | decide | (simp) | omega)
    -- heartbeat timeouts inside a tactic are runtime exceptions: a failed
    -- attempt, not a failed query
    tryCatchRuntimeEx
      (do let gs ← Tactic.run g (Tactic.evalTactic stx); return gs.isEmpty)
      (fun e => do if e.isInterrupt then throw e else return false)
  modifyThe Core.State fun s => { s with messages := savedMsgs }
  return r

/-- Try to close a *closed* `Prop` goal (no metavariables, no locals) with a
small tactic portfolio. Messages the tactics log are discarded. -/
def proofPortfolio (cfg : SearchConfig) (g : MVarId) : SearchM Bool := do
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar || t.hasFVar then return false
  -- `False` has no proof and `True` is a constructor: not worth a tactic run
  if t.isConstOf ``False || t.isConstOf ``True then return false
  unless ← isProp t do return false
  charge fun l => { l with proofAttempts := l.proofAttempts + 1 }
  -- the contract goal of a closed program: precomputed conjunct deciders
  if let some contract := cfg.contract then
    if !cfg.residual.isEmpty then
      if let some p ← rootProgram cfg then
        if leant2.traceNodes.get (← getOptions) then
          IO.println s!"[leant2]     program {(← ppExpr p).pretty 100000}"
        if !p.hasExprMVar && t == (contract.beta #[p]) then
          if (← (← read).refutedPrograms.get).contains p then return false
          match ← evalResidual cfg p with
          | .refuted => (← read).refutedPrograms.modify (·.insert p); return false
          | .proved pf => g.assign pf; return true
          | .stuck => pure ()
  -- fast path: a decidable closed proposition is decided by reduction; `false`
  -- refutes the candidate outright, so no further tactic is attempted
  let inst? : Option Expr ← (do
    try synthInstance? (mkApp (mkConst ``Decidable) t)
    catch e => if isInterrupt e then throw e else pure none : MetaM (Option Expr))
  if let some inst := inst? then
    match (← kernelDecide t inst).1 with
    | some true =>
      let pf := mkApp3 (mkConst ``of_decide_eq_true) t inst
        (mkApp2 (mkConst ``Eq.refl [Level.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true))
      g.assign pf
      return true
    | some false => return false
    | none => pure ()
  tacticProve g


/-- `forall R : Sort, ... -> R`: the shape of a Church-encoded datum, whose
result is the quantified type itself. -/
private def isChurchEliminator (ty : Expr) : MetaM Bool := do
  match ty with
  | .forallE _ bty _ _ =>
    unless (← whnfR bty).isSort do return false
    forallTelescopeReducing ty fun xs b => return xs.size > 1 && b == xs[0]!
  | _ => return false

private def localsToTry : MetaM (Array LocalDecl) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    out := out.push d
  return out.reverse -- most recent first

private def applyCfg : ApplyConfig :=
  { newGoals := .all, synthAssignedInstances := false, allowSynthFailures := true }

/-- Inductive info of a local's (whnf) type, if any. -/
private def inductiveOfLocal (decl : LocalDecl) : MetaM (Option InductiveVal) := do
  let dty ← whnfR (← instantiateMVars decl.type)
  if let .const iname _ := dty.getAppFn then
    if let some (.inductInfo ii) := (← getEnv).find? iname then return some ii
  return none

/-- A local whose type is a non-recursive single-constructor inductive without
indices can be destructured without loss (Prod, And, Iff, Sigma, Subtype...). -/
private def isInvertible (ii : InductiveVal) : Bool :=
  ii.ctors.length == 1 && !ii.isRec && ii.numIndices == 0

mutual
/-- Structural recursion on a recursive inductive local (Section 17): the
recursor with a constant motive; each constructor branch receives its
induction hypotheses as recursive-call capabilities. Bounded like a split. -/
partial def structuralRecursion (cfg : SearchConfig) (leaf : Leaf) (splits d : Nat)
    (g : MVarId) (locals : Array LocalDecl) (rest : List Goal) (consumed : List FVarId := [])
    : SearchM Bool := do
  if splits = 0 then return false
  for decl in locals do
    if let some ii ← inductiveOfLocal decl then
      unless ii.isRec && ii.numIndices == 0 && ii.name != ``Nat do continue
      if ← alternative (do
          let subgoals ← g.induction decl.fvarId (mkRecName ii.name)
          search cfg leaf (splits - 1)
            (subgoals.toList.map (fun s => { mvar := s.mvarId, depth := d, consumed }) ++ rest)) then
        return true
  return false

/-- The search over a goal list. -/
partial def search (cfg : SearchConfig) (leaf : Leaf) (splits : Nat) :
    List Goal → SearchM Bool
  | [] => leaf
  | goal :: rest => do
    let g := goal.mvar
    let depth := goal.depth
    if ← g.isAssigned then return ← search cfg leaf splits rest
    checkDeadline
    g.withContext do
    let target ← instantiateMVars (← g.getType)
    if leant2.traceNodes.get (← getOptions) then
      IO.println s!"[leant2]     node {← ppExpr target} depth {depth} splits {splits} rest {rest.length}"
    -- a proposition about open holes (the contract on a partial program) is
    -- decided once the holes are filled: it yields to every other obligation
    -- (class goals are not such propositions: an instance determines type holes)
    let isResidual (t : Expr) : MetaM Bool := do
      if !t.hasExprMVar then return false
      unless ← isProp t do return false
      return (← isClass? t).isNone
    if !rest.isEmpty && (← isResidual target) then
      let mut other := false
      for r in rest do
        unless ← isResidual (← instantiateMVars (← r.mvar.getType)) do other := true; break
      if other then return ← search cfg leaf splits (rest ++ [goal])
    -- deferral: let sibling obligations determine type arguments and open types
    if !rest.isEmpty then
      let targetW ← whnfR target
      -- a type former (`Type → Type`) is a type hole too
      let isSortGoal ← timed "deferral" (forallTelescopeReducing targetW fun _ b => do return (← whnfR b).isSort)
      let mvarHeaded := targetW.getAppFn.isMVar
      -- limits: a hole typed by a bare metavariable waits longest (its type hole must
      -- come first); a type hole waits for rigid-headed siblings (instances) that
      -- can determine it; a rigid-headed open goal waits once.
      let limit := if mvarHeaded then 3 else if isSortGoal then 2 else 1
      if goal.deferred < limit && (isSortGoal || target.hasExprMVar) then
        return ← search cfg leaf splits (rest ++ [{ goal with deferred := goal.deferred + 1 }])
    -- residual evaluation: a pending contract elsewhere in the list that already
    -- reduces to `false` prunes this branch before any further construction
    if cfg.recursionFirst then  -- i.e. a contract is present
      let refuted ← timed "residual" do
        let mut refuted := false
        for pending in rest do
          let pty ← instantiateMVars (← pending.mvar.getType)
          if pty.hasExprMVar && (← isProp pty) then
            if ← partialRefute cfg pty then refuted := true; break
        pure refuted
      if refuted then return false
    charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
    let targetW ← whnfR target
    let d := depth - 1
    let consumed := goal.consumed
    let cont (children : List MVarId) : SearchM Bool :=
      search cfg leaf splits (children.map (fun m => { mvar := m, depth := d, consumed }) ++ rest)
    -- like `cont`, but the children may not apply `fv` again
    let contConsuming (fv : FVarId) (children : List MVarId) : SearchM Bool :=
      search cfg leaf splits
        (children.map (fun m => { mvar := m, depth := d, consumed := fv :: consumed }) ++ rest)
    let applyHead (e : Expr) : SearchM Bool := alternative do
      charge fun l => { l with unifications := l.unifications + 1 }
      let children ← timed "apply" (g.apply e applyCfg)
      cont children
    let locals ← timed "locals" localsToTry
    -- 0. exact locals first: the exact-term lane runs before eta-expansion, so a
    -- function-typed hole is filled by a matching local rather than introduced
    for decl in locals do
      if ← alternative (do
          charge fun l => { l with unifications := l.unifications + 1 }
          if ← timed "exact" (isDefEq (← inferType decl.toExpr) target) then
            g.assign decl.toExpr
            cont []
          else return false) then return true
    -- leaves (exact locals) are free; everything below consumes depth
    if depth = 0 then return false
    -- 1. introduction (default transparency, so that `Not` and similar unfold).
    -- Invertible, hence free of depth cost.
    if (← timed "intro" (whnf target)).isForall then
      return ← alternative do
        let (_, g') ← timed "intro" g.intro1P
        search cfg leaf splits ({ mvar := g', depth, consumed } :: rest)
    -- 2. invertible destructuring (does not consume depth or splits)
    for decl in locals do
      if let some ii ← inductiveOfLocal decl then
        -- class instances are taken apart by projection (rule 6): `inst.out`
        -- rather than `C.casesOn inst fun out => ...`
        if isInvertible ii && !isClass (← getEnv) ii.name then
          if ← alternative (do
              let subgoals ← g.cases decl.fvarId
              search cfg leaf splits
                (subgoals.toList.map (fun s => { mvar := s.mvarId, depth, consumed }) ++ rest)) then
            return true
          -- destructuring failed (e.g. Prop into data): fall through
  -- 2b. classical case split on a Prop variable, early: `cases (Classical.em p)`.
  -- Bounded by `splits`, so it multiplies the search by at most 2^splits.
    if cfg.classical && splits > 0 then
      for decl in locals do
        let dty ← instantiateMVars decl.type
        unless dty.isProp do continue
        if ← alternative (do
            let em ← mkAppM ``Classical.em #[decl.toExpr]
            let ty ← inferType em
            let g' ← g.assert (← mkFreshUserName `h) ty em
            let (h, g'') ← g'.intro1P
            let subgoals ← g''.cases h
            search cfg leaf (splits - 1)
              (subgoals.toList.map (fun s => { mvar := s.mvarId, depth := d, consumed }) ++ rest)) then
          return true
    -- 2c. structural recursion first, under a contract, at the outermost level
    -- only (nested recursion remains a late alternative, rule 9d)
    let recurseNow := cfg.recursionFirst && !targetW.isSort && splits == cfg.maxSplits
    if recurseNow then
      if ← structuralRecursion cfg leaf splits d g locals rest consumed then return true
    -- 3. reflexivity
    if targetW.isAppOfArity ``Eq 3 then
      if ← alternative (do g.refl; cont []) then return true
    let targetIsSort ← isTypeSort target
    -- 3b. closed class goals: Lean's own instance resolution (canonical instance mode)
    if !target.hasExprMVar then
      if (← isClass? target).isSome then
        if ← alternative (do
            match ← synthInstance? target with
            | some inst => g.assign inst; cont []
            | none => return false) then return true
    if targetIsSort then
      -- type invention: types of locals first, then the closed frontier
      let frontier ← localFrontier locals
      for t in frontier ++ cfg.typeFrontier do
        if ← alternative (do
            if ← isDefEq (← inferType t) target then
              g.assign t; cont []
            else return false) then return true
      -- a universe-polymorphic unit fits any sort (`Type 1`, `Sort u`, `Prop`)
      if ← alternative (do
          let u ← mkConstWithFreshMVarLevels ``PUnit
          if ← isDefEq (← inferType u) target then
            g.assign u; cont []
          else return false) then return true
    -- 6. projections of local structure values, applied as heads
    for decl in locals do
      let dty ← whnfR (← instantiateMVars decl.type)
      if let .const sname _ := dty.getAppFn then
        if isStructure (← getEnv) sname then
          for field in getStructureFields (← getEnv) sname do
            let p? ← attempt (mkProjection decl.toExpr field)
            if let some p := p? then
              if ← applyHead p then return true
    -- 6. constructors of the target's inductive head
    let targetHead : Option Name := match targetW.getAppFn with
      | .const c _ => some c
      | _ => none
    if let some iname := targetHead then
      if let some (.inductInfo ii) := (← getEnv).find? iname then
        for c in ii.ctors do
          if ← applyHead (← mkConstWithFreshMVarLevels c) then return true
    if !targetIsSort then
      -- 7. application of locals (default transparency: `¬p` is a function)
      for decl in locals do
        if consumed.contains decl.fvarId then continue
        let dty ← whnf (← instantiateMVars decl.type)
        unless dty.isForall do continue
        -- a Church-encoded datum (`forall R, ... -> R`) is an eliminator: it is
        -- not applied again inside its own continuation arguments
        let eliminator ← isChurchEliminator dty
        if ← alternative (do
            charge fun l => { l with unifications := l.unifications + 1 }
            let children ← timed "apply" (g.apply decl.toExpr applyCfg)
            if eliminator then contConsuming decl.fvarId children else cont children) then
          return true
      -- 7a. polymorphic locals instantiated at the accumulator type `T -> T` for
      -- the target `T` before application: `apply` cannot see that
      -- `xs (T -> T) step seed x` has one more argument than `xs T step seed`
      if !target.hasExprMVar then
        let acc ← mkArrow target target
        for decl in locals do
          if consumed.contains decl.fvarId then continue
          let dty ← whnf (← instantiateMVars decl.type)
          let .forallE _ bty body _ := dty | continue
          unless (← whnfR bty).isSort do continue
          let eliminator ← isChurchEliminator dty
          if ← alternative (do
              unless ← isDefEq (← inferType acc) bty do return false
              let inst := body.instantiate1 acc
              unless (← whnf inst).isForall do return false
              charge fun l => { l with unifications := l.unifications + 1 }
              let children ← g.apply (mkApp decl.toExpr acc) applyCfg
              if eliminator then contConsuming decl.fvarId children else cont children) then
            return true
      -- 7b. bounded forward application: when every argument of a local function is
      -- an exact local, name the result so that it can be destructured or projected
      -- (`match f x with | (a, s) => ...`). Costs one depth unit.
      for decl in locals do
        let dty ← whnf (← instantiateMVars decl.type)
        unless dty.isForall do continue
        if ← alternative (do
            let (args, _, resTy) ← forallMetaTelescopeReducing dty
            if args.isEmpty || args.size > 3 then return false
            for a in args do
              let aty ← instantiateMVars (← inferType a)
              let mut filled := false
              for l in locals do
                if l.fvarId == decl.fvarId then continue
                if ← isDefEq (← inferType l.toExpr) aty then
                  if ← isDefEq a l.toExpr then filled := true; break
              unless filled do return false
            let resTy ← instantiateMVars resTy
            -- only results that can be taken apart are worth naming
            let some hn := (← whnfR resTy).getAppFn.constName? | return false
            let some (.inductInfo _) := (← getEnv).find? hn | return false
            let val ← instantiateMVars (mkAppN decl.toExpr args)
            let g' ← g.assert (← mkFreshUserName `h) resTy val
            let (_, g'') ← g'.intro1P
            search cfg leaf splits ({ mvar := g'', depth := d, consumed } :: rest)) then return true
      -- 9. providers, head-filtered: a constant-headed conclusion must match the
      -- target head; a variable-headed provider needs a local demanding one of its
      -- argument heads
      let provs ← if cfg.classical then do pure (cfg.providers ++ (← classicalProviders))
                  else pure cfg.providers
      let localHeads ← locals.filterMapM fun decl => do
        let dty ← whnfR (← instantiateMVars decl.type)
        return match dty.getAppFn with | .const c _ => some c | _ => none
      for p in provs do
        match p.head with
        | some h =>
          match targetHead with
          | some th => if h != th then continue
          | none => continue
        | none =>
          if !p.always && !p.argHeads.isEmpty && !p.argHeads.any localHeads.contains then continue
        if ← applyHead (← mkConstWithFreshMVarLevels p.name) then return true
      -- 9b. forward application of argument-less providers whose result is a
      -- structure (`box {a} [Choice a] : a × Unit`): name the result so that its
      -- projections become heads. Instance arguments are scheduled first.
      for p in provs do
        let some h := p.head | continue
        unless isStructure (← getEnv) h do continue
        if ← alternative (do
            let c ← mkConstWithFreshMVarLevels p.name
            let cty ← inferType c
            let (args, binfos, resTy) ← forallMetaTelescopeReducing cty
            if args.isEmpty || binfos.any (·.isExplicit) then return false
            let val := mkAppN c args
            let resTy ← instantiateMVars resTy
            let g' ← g.assert (← mkFreshUserName `h) resTy val
            let (_, g'') ← g'.intro1P
            let mut instGoals : List Goal := []
            let mut otherGoals : List Goal := []
            for a in args do
              let aty ← instantiateMVars (← inferType a)
              let goal : Goal := { mvar := a.mvarId!, depth := d, deferred := 3, consumed }
              if (← isClass? aty).isSome then instGoals := instGoals ++ [goal]
              else otherGoals := otherGoals ++ [goal]
            search cfg leaf splits (instGoals ++ otherGoals ++ [{ mvar := g'', depth := d, consumed }] ++ rest))
          then return true
      -- 9c. bounded case analysis on multi-constructor locals, after providers so
      -- that library applications (`List.map f xs`) are found before case splits
      if splits > 0 then
        for decl in locals do
          if let some ii ← inductiveOfLocal decl then
            if isInvertible ii || ii.name == ``Nat then continue
            if ← alternative (do
                let subgoals ← g.cases decl.fvarId
                search cfg leaf (splits - 1)
                  (subgoals.toList.map (fun s => { mvar := s.mvarId, depth := d, consumed }) ++ rest)) then
              return true
      -- 9d. structural recursion as a late alternative, top level only (nested
      -- recursion is not attempted: it multiplies the search without payoff here)
      if !recurseNow && splits == cfg.maxSplits then
        if ← structuralRecursion cfg leaf splits d g locals rest consumed then return true
      -- 10. proof portfolio on closed propositions
      if cfg.proofPortfolio then
        if ← alternative (do if ← timed "portfolio" (proofPortfolio cfg g) then cont [] else return false) then
          return true
    return false
end

end Leant2
