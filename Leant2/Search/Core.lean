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

/-- Run one alternative. If it does not stop the search, restore the state so
the next alternative starts from the same point. -/
def alternative (act : SearchM Bool) : SearchM Bool := do
  let saved : Meta.SavedState ← Meta.saveState
  try
    if ← act then return true
  catch e =>
    if isInterrupt e then throw e
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

private def isTypeSort (e : Expr) : MetaM Bool := do
  match ← whnfR e with
  | .sort _ => return true
  | _ => return false

/-- Try to close a *closed* `Prop` goal (no metavariables, no locals) with a
small tactic portfolio. Messages the tactics log are discarded. -/
def proofPortfolio (g : MVarId) : SearchM Bool := do
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar || t.hasFVar then return false
  -- `False` has no proof and `True` is a constructor: not worth a tactic run
  if t.isConstOf ``False || t.isConstOf ``True then return false
  unless ← isProp t do return false
  charge fun l => { l with proofAttempts := l.proofAttempts + 1 }
  -- fast path: a decidable closed proposition is decided by reduction; `false`
  -- refutes the candidate outright, so no further tactic is attempted
  let inst? : Option Expr ← (do
    try synthInstance? (mkApp (mkConst ``Decidable) t)
    catch e => if isInterrupt e then throw e else pure none : MetaM (Option Expr))
  if let some inst := inst? then
    let d := mkApp2 (mkConst ``Decidable.decide) t inst
    let r ← withDefault (whnf d)
    if r.isConstOf ``Bool.true then
      let pf := mkApp3 (mkConst ``of_decide_eq_true) t inst
        (mkApp2 (mkConst ``Eq.refl [Level.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true))
      g.assign pf
      return true
    if r.isConstOf ``Bool.false then return false
  let savedMsgs := (← getThe Core.State).messages
  let r ← Term.TermElabM.run' do
    let stx ← `(tactic| first | rfl | decide | (simp) | omega)
    try
      let gs ← Tactic.run g (Tactic.evalTactic stx)
      return gs.isEmpty
    catch _ => return false
  modifyThe Core.State fun s => { s with messages := savedMsgs }
  return r

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

/-- Residual evaluation of a pending contract (Section 18.2): split a
conjunction and decide each conjunct by reduction, even when other holes are
still open. A conjunct that reduces to `false` refutes every completion of
the current partial program, so the branch can be abandoned now. -/
partial def partialRefute (t : Expr) : SearchM Bool := do
  let t := (← instantiatePartial t).headBeta
  if t.isAppOfArity ``And 2 then
    if ← partialRefute (t.getArg! 0) then return true
    return ← partialRefute (t.getArg! 1)
  let inst? : Option Expr ← (do
    try synthInstance? (mkApp (mkConst ``Decidable) t)
    catch e => if isInterrupt e then throw e else pure none : MetaM (Option Expr))
  let some inst := inst? | return false
  let r ← (do
    try withDefault (whnf (mkApp2 (mkConst ``Decidable.decide) t inst))
    catch e => if isInterrupt e then throw e else pure (mkConst ``Bool.true) : MetaM Expr)
  return r.isConstOf ``Bool.false

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
    (g : MVarId) (locals : Array LocalDecl) (rest : List Goal) : SearchM Bool := do
  if splits = 0 then return false
  for decl in locals do
    if let some ii ← inductiveOfLocal decl then
      unless ii.isRec && ii.numIndices == 0 && ii.name != ``Nat do continue
      if ← alternative (do
          let subgoals ← g.induction decl.fvarId (mkRecName ii.name)
          search cfg leaf (splits - 1)
            (subgoals.toList.map (fun s => { mvar := s.mvarId, depth := d }) ++ rest)) then
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
    if depth = 0 then return false
    checkDeadline
    g.withContext do
    let target ← instantiateMVars (← g.getType)
    -- deferral: let sibling obligations determine type arguments and open types
    if !rest.isEmpty then
      let targetW ← whnfR target
      -- a type former (`Type → Type`) is a type hole too
      let isSortGoal ← forallTelescopeReducing targetW fun _ b => do return (← whnfR b).isSort
      let mvarHeaded := targetW.getAppFn.isMVar
      -- limits: a hole typed by a bare metavariable waits longest (its type hole must
      -- come first); a type hole waits for rigid-headed siblings (instances) that
      -- can determine it; a rigid-headed open goal waits once.
      let limit := if mvarHeaded then 3 else if isSortGoal then 2 else 1
      if goal.deferred < limit && (isSortGoal || target.hasExprMVar) then
        return ← search cfg leaf splits (rest ++ [{ goal with deferred := goal.deferred + 1 }])
    -- residual evaluation: a pending contract elsewhere in the list that already
    -- reduces to `false` prunes this branch before any further construction
    for pending in rest do
      let pty ← instantiateMVars (← pending.mvar.getType)
      if pty.hasExprMVar && (← isProp pty) then
        if ← partialRefute pty then return false
    charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
    let targetW ← whnfR target
    let d := depth - 1
    let cont (children : List MVarId) : SearchM Bool :=
      search cfg leaf splits (children.map (fun m => { mvar := m, depth := d }) ++ rest)
    let applyHead (e : Expr) : SearchM Bool := alternative do
      charge fun l => { l with unifications := l.unifications + 1 }
      let children ← g.apply e applyCfg
      cont children
    let locals ← localsToTry
    -- 0. exact locals first: the exact-term lane runs before eta-expansion, so a
    -- function-typed hole is filled by a matching local rather than introduced
    for decl in locals do
      if ← alternative (do
          charge fun l => { l with unifications := l.unifications + 1 }
          if ← isDefEq (← inferType decl.toExpr) target then
            g.assign decl.toExpr
            cont []
          else return false) then return true
    -- 1. introduction (default transparency, so that `Not` and similar unfold).
    -- Invertible, hence free of depth cost.
    if (← whnf target).isForall then
      return ← alternative do
        let (_, g') ← g.intro1P
        search cfg leaf splits ({ mvar := g', depth } :: rest)
    -- 2. invertible destructuring (does not consume depth or splits)
    for decl in locals do
      if let some ii ← inductiveOfLocal decl then
        if isInvertible ii then
          if ← alternative (do
              let subgoals ← g.cases decl.fvarId
              search cfg leaf splits
                (subgoals.toList.map (fun s => { mvar := s.mvarId, depth }) ++ rest)) then
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
              (subgoals.toList.map (fun s => { mvar := s.mvarId, depth := d }) ++ rest)) then
          return true
    -- 2c. structural recursion first, under a contract, at the outermost level
    -- only (nested recursion remains a late alternative, rule 9d)
    let recurseNow := cfg.recursionFirst && !targetW.isSort && splits == cfg.maxSplits
    if recurseNow then
      if ← structuralRecursion cfg leaf splits d g locals rest then return true
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
      let mut frontier : Array Expr := #[]
      for decl in locals do
        let dty ← instantiateMVars decl.type
        if ← isTypeSort (← inferType dty) then
          unless frontier.contains dty do frontier := frontier.push dty
      for t in frontier ++ cfg.typeFrontier do
        if ← alternative (do
            if ← isDefEq (← inferType t) target then
              g.assign t; cont []
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
        let dty ← whnf (← instantiateMVars decl.type)
        unless dty.isForall do continue
        if ← applyHead decl.toExpr then return true
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
            search cfg leaf splits ({ mvar := g'', depth := d } :: rest)) then return true
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
              let goal : Goal := { mvar := a.mvarId!, depth := d, deferred := 3 }
              if (← isClass? aty).isSome then instGoals := instGoals ++ [goal]
              else otherGoals := otherGoals ++ [goal]
            search cfg leaf splits (instGoals ++ otherGoals ++ [{ mvar := g'', depth := d }] ++ rest))
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
                  (subgoals.toList.map (fun s => { mvar := s.mvarId, depth := d }) ++ rest)) then
              return true
      -- 9d. structural recursion as a late alternative, top level only (nested
      -- recursion is not attempted: it multiplies the search without payoff here)
      if !recurseNow && splits == cfg.maxSplits then
        if ← structuralRecursion cfg leaf splits d g locals rest then return true
      -- 10. proof portfolio on closed propositions
      if cfg.proofPortfolio then
        if ← alternative (do if ← proofPortfolio g then cont [] else return false) then
          return true
    return false
end

end Leant2
