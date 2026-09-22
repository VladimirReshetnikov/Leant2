import Lean
import Leant2.Core.Types
import Leant2.Native.Transaction
import Leant2.Native.Pruning
import Leant2.Proof.Local
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
closed propositions and bounded proof search in local contexts.

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
  /-- Trust policy for negative pruning as well as final acceptance. -/
  profile : Profile := .standard
  /-- Closed predicate/decider dependency judgments, guarded by policy and env. -/
  pruningEvidenceCache : Option PruningEvidenceCacheRef := none
  /-- Closed types tried for `Sort`-valued holes. -/
  typeFrontier : Array Expr := #[]
  /-- Allow `Classical.em` and friends as providers. -/
  classical : Bool := false
  /-- Run the closed-contract portfolio and bounded local proof service. -/
  proofPortfolio : Bool := true
  /-- Try structural recursion on recursive inductive locals before constructors
  and providers (used when a behavioral contract is present, Section 17). -/
  recursionFirst : Bool := false
  /-- The contract `fun f => P f`, when there is one. -/
  contract : Option Expr := none
  /-- Precomputed deciders for the contract's conjuncts (left to right):
  each is `fun f => C_i f` with `fun f => inst_i` when `C_i f` is decidable. -/
  residual : Array (Expr × Option Expr) := #[]
  /-- Finer necessary conditions used only to prune partial programs. -/
  observations : Array Observation := #[]
  /-- Optional query-owned pruning before expanding an unassigned goal. The
  callback must preserve native state and justify every `true`; unsupported
  shapes return `false`. It receives the current scoped resource context.
  Ordinary queries leave this absent. -/
  partialPruner : Option (MVarId → SearchM Bool) := none
  /-- The root hole of the current pass (a `Subtype` when a contract is present). -/
  root : Option MVarId := none
  /-- Rules disabled for experiments (`leant2.skipRules`). -/
  skip : List String := []

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
  /-- The bounded Nat/indexed rule is available only at the outer function
  body, after introductions and invertible context setup. Ordinary term
  applications and constructors clear it; the root contract's `Subtype`
  constructor passes it only to its program field. -/
  allowExtendedRecursion : Bool := false
  /-- Permit one bounded Nat guard on this program path. Only the actual root
  contract constructor enables the flag for its program field. Ordinary data
  construction preserves it; proof/type/instance goals and guard children clear
  it. This permission is independent of outer-induction eligibility. -/
  allowNatGuards : Bool := false
  /-- One early bounded composition prefix on an actual outer nonindexed
  program-induction minor. Free setup preserves it; ordinary construction clears it. -/
  tryBranchComposition : Bool := false

/-- Record a named elapsed span when this query has a collector. Nested spans
retain inclusive and exclusive time; interrupted spans finalize as well. -/
def timed (k : String) (act : SearchM α) : SearchM α := do
  let ctx ← read
  Profiling.span ctx.profile k (act.run ctx)

/-- Run one alternative. If it does not stop the search, restore the state so
the next alternative starts from the same point. -/
def alternative (act : SearchM Bool) : SearchM Bool := do
  let saved : Meta.SavedState ← timed "alt.save" Meta.saveState
  let (result, _) ← tryFinally' (do
    try
      act
    catch e =>
      if isInterrupt e then throw e
      if leant2.traceNodes.get (← getOptions) then
        IO.println s!"[leant2]     alternative failed with: {← e.toMessageData.toString}"
      return false) fun result? => do
    unless result? == some true do
      timed "alt.restore" saved.restore
  return result

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
  if !e.hasExprMVar then return e
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

/-- A stuck typeclass input is an ordinary deferred probe. Lean's
`trySynthInstance` handles its documented `isDefEqStuck` control exception;
unrelated internal exceptions and native resource limits still propagate. -/
private def probeInstance? (type : Expr) : MetaM (Option Expr) := do
  try
    match ← trySynthInstance type with
    | .some inst => return some inst
    | .none | .undef => return none
  catch e =>
    if isInterrupt e then throw e
    return none

/-- Precompute the residual deciders of a contract `fun f => P f` at `T`. -/
def mkResidual (contract : Expr) (ty : Expr) : MetaM (Array (Expr × Option Expr)) :=
  withLocalDecl `f .default ty fun f => do
    let body := (contract.beta #[f])
    let mut out := #[]
    for c in conjuncts body do
      let inst? ← probeInstance? (mkApp (mkConst ``Decidable) c)
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
  if p.hasExprMVar && !cfg.observations.isEmpty then
    let ctx ← read
    let (report, cache) ← evalObservations cfg.observations p
      (← ctx.observationCache.get) instantiatePartial (checkDeadline.run ctx)
      (fun predicate decider =>
        falseEvidenceAllowed cfg.profile predicate decider cfg.pruningEvidenceCache)
    ctx.observationCache.set cache
    ctx.observationReport.set report
    if leant2.traceNodes.get (← getOptions) then
      IO.println s!"[leant2]     observations {repr report.statuses} reductions {report.reductions} reused {report.reused}"
    return if report.refuted then .refuted else .stuck
  let mut proofs : Array (Option Expr) := #[]
  for (pred, inst?) in cfg.residual do
    let some inst := inst? | proofs := proofs.push none; continue
    let t := pred.beta #[p]
    let i := inst.beta #[p]
    let (r, _) ← kernelDecide t i
    if r == some false &&
        (← falseEvidenceAllowed cfg.profile pred inst cfg.pruningEvidenceCache) then
      return .refuted
    if r == some true && !p.hasExprMVar then
      proofs := proofs.push (some (mkApp3 (mkConst ``of_decide_eq_true) t i
        (mkApp2 (mkConst ``Eq.refl [Level.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true))))
    else proofs := proofs.push none
  if p.hasExprMVar then
    return .stuck
  if proofs.any (·.isNone) then return .stuck
  let some contract := cfg.contract | return .stuck
  let (pf, _) := buildAndProof proofs (contract.beta #[p]) 0
  return .proved pf

/-- Preserve the existing query-local closed-program refutation accounting.
The caller owns eligibility and its proof-attempt charge. IO-backed refutations
remain valid when an alternative restores its metavariable assignments. -/
private def evalClosedProgram (cfg : SearchConfig) (program : Expr) : SearchM Residual := do
  if leant2.traceNodes.get (← getOptions) then
    IO.println s!"[leant2]     program {(← ppExpr program).pretty 100000}"
  let refuted := (← read).refutedPrograms
  if (← refuted.get).contains program then return .refuted
  let result ← evalResidual cfg program
  checkDeadline
  if result matches .refuted then
    charge fun l => { l with rejected := l.rejected + 1 }
    refuted.modify (·.insert program)
  return result

/-- Check only the exact closed contract of a natively completed root program.
`none` is ineligible, and `.stuck` preserves ordinary proof search. This path
does not expose partial/delayed root assignments or evaluate observations.
Proof assignment and the unchanged continuation belong to the caller's
alternative, not to this evaluator. Local contexts use the local proof service.
-/
def evalClosedRootContract (cfg : SearchConfig) (g : MVarId)
    : SearchM (Option Residual) := g.withContext do
  if !cfg.proofPortfolio || cfg.residual.isEmpty || !(← getLCtx).isEmpty then return none
  let some contract := cfg.contract | return none
  let some root := cfg.root | return none
  let target ← instantiateMVars (← g.getType)
  let closed := fun e : Expr => !e.hasMVar && !e.hasFVar && !e.hasLooseBVars && !e.hasSorry
  unless closed target do return none
  unless ← isProp target do return none
  -- Deliberately native instantiation only. The proof field may remain a hole;
  -- the program, its type, and the actual predicate must already be closed.
  let rootValue ← instantiateMVars (mkMVar root)
  unless rootValue.isAppOfArity ``Subtype.mk 4 do return none
  let program := rootValue.getArg! 2
  let programType := rootValue.getArg! 0
  let actualContract := rootValue.getArg! 1
  let contract ← instantiateMVars contract
  unless closed program && closed programType && closed contract && closed actualContract do return none
  unless actualContract == contract do return none
  unless closed (← instantiateMVars (← inferType program)) do return none
  unless target == contract.beta #[program] do return none
  checkDeadline
  charge fun l => { l with proofAttempts := l.proofAttempts + 1 }
  return some (← evalClosedProgram cfg program)

/-- Residual evaluation of a pending contract goal (Section 10): a conjunct
that already reduces to `false` on the partial program refutes the branch.
Uses the precomputed deciders when present, otherwise generic decision. -/
partial def partialRefute (cfg : SearchConfig) (t : Expr) : SearchM Bool := do
  if !cfg.residual.isEmpty then
    let some p ← timed "residual.instantiate" (rootProgram cfg) | return false
    let r ← timed "residual.decide" (evalResidual cfg p)
    if leant2.traceNodes.get (← getOptions) then
      IO.println s!"[leant2]     residual {if r matches .refuted then "REFUTED" else "stuck"} {(← ppExpr p).pretty 100000}"
    return r matches .refuted
  let t := (← instantiatePartial t).headBeta
  if t.isAppOfArity ``And 2 then
    if ← partialRefute cfg (t.getArg! 0) then return true
    return ← partialRefute cfg (t.getArg! 1)
  let inst? ← probeInstance? (mkApp (mkConst ``Decidable) t)
  let some inst := inst? | return false
  return (← kernelDecide t inst).1 == some false &&
    (← falseEvidenceAllowed cfg.profile t inst cfg.pruningEvidenceCache)

/-- The tactic part of the portfolio on a closed goal; messages the tactics
log are discarded. -/
def tacticProve (g : MVarId) : MetaM Bool := do
  let saved : Meta.SavedState ← Meta.saveState
  let savedMsgs := (← getThe Core.State).messages
  let (result, _) ← tryFinally' (Term.TermElabM.run' do
      let stx ← `(tactic| first | rfl | decide | (simp) | omega)
      tryCatchRuntimeEx
        (do let gs ← Tactic.run g (Tactic.evalTactic stx); return gs.isEmpty)
        (fun e => do
          if e.isMaxHeartbeat || e.isMaxRecDepth then return false
          if isInterrupt e then throw e
          return false)) fun result? => do
    if result? == some true then
      modifyThe Core.State fun s => { s with messages := savedMsgs }
    else
      saved.restore
  return result

/-- Local propositions use the isolated proof service. Goals with no local
context retain the closed-contract evaluator and its refutation accounting. -/
def proofPortfolio (cfg : SearchConfig) (g : MVarId) (exactContractTried : Bool := false)
    : SearchM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if !(← getLCtx).isEmpty then
    if t.hasExprMVar then return false
    unless ← isProp t do return false
    match ← LocalProof.discharge g with
    | .solved _ => return true
    | .unresolved | .unsupportedDependency | .resourceExhausted => return false
  if t.hasMVar || t.hasFVar then return false
  -- `False` has no proof and `True` is a constructor: not worth a tactic run
  if t.isConstOf ``False || t.isConstOf ``True then return false
  unless ← isProp t do return false
  charge fun l => { l with proofAttempts := l.proofAttempts + 1 }
  -- the contract goal of a closed program: precomputed conjunct deciders
  unless exactContractTried do
    if let some contract := cfg.contract then
      if !cfg.residual.isEmpty then
        if let some p ← rootProgram cfg then
          if !p.hasExprMVar && t == (contract.beta #[p]) then
            match ← evalClosedProgram cfg p with
            | .refuted => return false
            | .proved pf => g.assign pf; return true
            | .stuck => pure ()
  -- A false decision prunes only when its evidence obeys the query profile.
  -- Otherwise ordinary tactics may still provide an admissible proof.
  let inst? ← probeInstance? (mkApp (mkConst ``Decidable) t)
  if let some inst := inst? then
    match (← kernelDecide t inst).1 with
    | some true =>
      let pf := mkApp3 (mkConst ``of_decide_eq_true) t inst
        (mkApp2 (mkConst ``Eq.refl [Level.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true))
      g.assign pf
      return true
    | some false =>
      if ← falseEvidenceAllowed cfg.profile t inst cfg.pruningEvidenceCache then
        if cfg.contract.isSome then charge fun l => { l with rejected := l.rejected + 1 }
        return false
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

/-- A Church eliminator with an argument that threads the result type, such
as the step `A -> R -> R` of a list or `R -> R` of a numeral: the shape whose
folds may need an accumulator (`R := T -> T`). Maybes, eithers, booleans and
pairs never do. -/
private def isRecursiveEliminator (ty : Expr) : MetaM Bool := do
  unless ← isChurchEliminator ty do return false
  forallTelescopeReducing ty fun xs _ => do
    let r := xs[0]!
    for x in xs[1:] do
      let xt ← whnfR (← inferType x)
      let threads ← forallTelescopeReducing xt fun ys b => do
        unless b == r do return false
        for y in ys do
          if (← inferType y).containsFVar r.fvarId! then return true
        return false
      if threads then return true
    return false

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

/-- Transport branch-local search metadata through native induction's
dependency reversion. Discard locals which do not survive in this branch. -/
private def inductionConsumed (subgoal : InductionSubgoal) (consumed : List FVarId)
    : MetaM (List FVarId) := do
  let lctx := (← subgoal.mvarId.getDecl).lctx
  return consumed.filterMap fun id =>
    match subgoal.subst.get id with
    | .fvar id => if (lctx.find? id).isSome then some id else none
    | _ => none

/-- The first guard grammar is deliberately finite: at most four most-recent
Nat locals, one orientation of each pairwise comparison, then zero tests.
Ordering the selected locals oldest first makes the usual two-argument guard
`a ≤ b`. No arbitrary literals, applications, or assumed example environments
are introduced here. This is a bounded A1 grammar extension, not abduction. -/
def natGuardPredicates (locals : Array LocalDecl) (check : MetaM Unit := pure ())
    : MetaM (Array Expr) := do
  let mut values : Array Expr := #[]
  for decl in locals do
    check
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.hasExprMVar then continue
    unless (← whnfR ty).isConstOf ``Nat do continue
    values := values.push decl.toExpr
    if values.size == 4 then break
  let ordered := values.reverse
  let mut predicates := #[]
  for i in [:ordered.size] do
    for j in [i + 1:ordered.size] do
      -- Preserve the overloaded relation head used to index the native
      -- Decidable instance. A bare Nat.le application is definitionally equal,
      -- but native typeclass retrieval does not find its instance at that key.
      predicates := predicates.push (← mkAppM ``LE.le #[ordered[i]!, ordered[j]!])
  for value in ordered do
    predicates := predicates.push (← mkEq value (mkNatLit 0))
  -- Native case analysis leaves precisely these positive/negative hypotheses.
  -- Avoid repeating an already-known guard without unifying any input holes.
  predicates.filterM fun predicate => do
    check
    let positive ← whnfR predicate
    let negative ← whnfR (mkNot predicate)
    for decl in locals do
      check
      let ty ← instantiateMVars decl.type
      if ty.hasExprMVar then continue
      let ty ← whnfR ty
      if ty == positive || ty == negative then return false
    return true

/-- A native constructive split with the same whole-continuation transaction
contract as every search alternative. Only successful continuation commits.
Ordinary failures restore; native/resource/internal exceptions restore before
escaping. The two arguments of `next` are the positive and negative branches. -/
def splitNatGuard (g : MVarId) (predicate : Expr)
    (next : MVarId → MVarId → SearchM Bool) : SearchM Bool :=
  alternative do
    checkDeadline
    let some decider ← probeInstance? (mkApp (mkConst ``Decidable) predicate)
      | return false
    let decider ← instantiateMVars decider
    if decider.hasExprMVar then return false
    charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
    let (positive, negative) ← timed "guards.split"
      (g.byCasesDec predicate decider (← mkFreshUserName `hGuard))
    next positive.mvarId negative.mvarId

/-!
Bounded composition of native induction branches. A finite one-head/two-head
prefix uses native application and the original continuation. Scoped quotas
reserve work for the second grade and the ordinary search fallback.
-/
namespace BranchComposition

/-- Diagnostic seam: production calls use these fixed proposed bounds. -/
structure Limits where
  attempts : Nat := 2048
  callbacks : Nat := 128
  continuationRules : Nat := 4096
  maxSliceMs : Nat := 500
  deriving Inhabited, Repr

structure Counters where
  attempts : Nat := 0
  seeds : Nat := 0
  heads : Nat := 0
  validations : Nat := 0
  completeBodies : Nat := 0
  callbacks : Nat := 0
  continuation : Ledger := {}
  deriving Inhabited, Repr

structure Stats where
  total : Counters := {}
  grades : Array Counters := #[{}, {}]
  entered : Array Bool := #[false, false]
  deriving Inhabited, Repr

private def addLedger (a b : Ledger) : Ledger := {
  ruleApplications := a.ruleApplications + b.ruleApplications
  unifications := a.unifications + b.unifications
  proofAttempts := a.proofAttempts + b.proofAttempts
  candidates := a.candidates + b.candidates
  rejected := a.rejected + b.rejected }

private def subLedger (a b : Ledger) : Ledger := {
  ruleApplications := a.ruleApplications - b.ruleApplications
  unifications := a.unifications - b.unifications
  proofAttempts := a.proofAttempts - b.proofAttempts
  candidates := a.candidates - b.candidates
  rejected := a.rejected - b.rejected }

private inductive AttemptKind where
  | seed | head | validation

private structure Run where
  cfg : SearchConfig
  root : MVarId
  originalType : Expr
  locals : Array LocalDecl
  limits : Limits
  stats : IO.Ref Stats
  grade : Nat
  gradeAttempts : Nat
  gradeCallbacks : Nat
  activeStart : IO.Ref (Option Ledger)
  stop : SearchM Unit
  next : SearchM Bool

private def record (r : Run) (f : Counters → Counters) : SearchM Unit := do
  r.stats.modify fun s => { s with total := f s.total, grades := s.grades.modify r.grade f }

private def admitAttempt (r : Run) (kind : AttemptKind) : SearchM Unit := do
  checkDeadline
  let s ← r.stats.get
  if s.total.attempts >= r.limits.attempts ||
      (s.grades[r.grade]!).attempts >= r.gradeAttempts then r.stop
  record r fun c => { c with
    attempts := c.attempts + 1
    seeds := c.seeds + (match kind with | .seed => 1 | _ => 0)
    heads := c.heads + (match kind with | .head => 1 | _ => 0)
    validations := c.validations + (match kind with | .validation => 1 | _ => 0) }
  charge fun l => { l with unifications := l.unifications + 1 }

private def admitCallback (r : Run) : SearchM Unit := do
  checkDeadline
  let s ← r.stats.get
  if s.total.callbacks >= r.limits.callbacks ||
      (s.grades[r.grade]!).callbacks >= r.gradeCallbacks then r.stop
  record r fun c => { c with callbacks := c.callbacks + 1 }

/-- Native apply may solve dictionaries. Only its remaining rigid data goals
belong to this grammar; this helper never launches proof/instance/type search. -/
private def dataType? (type : Expr) : MetaM (Option Expr) := do
  let type ← instantiateMVars type
  if type.hasExprMVar then return none
  let type ← whnfR type
  if type.isSort || type.isForall then return none
  if ← isProp type then return none
  if (← isClass? type).isSome then return none
  return some type

private def completed (r : Run) (credit : Nat) : SearchM Bool := do
  if credit != 0 then return false
  record r fun c => { c with completeBodies := c.completeBodies + 1 }
  r.root.withContext do
    checkDeadline
    unless ← r.root.isAssignedOrDelayedAssigned do return false
    let value ← instantiateMVars (mkMVar r.root)
    if value.hasExprMVar || value.hasLooseBVars || value.hasSorry then return false
    let lctx ← getLCtx
    unless (collectFVars {} value).fvarIds.all (fun id => (lctx.find? id).isSome) do
      return false
    admitAttempt r .validation
    check value
    unless ← isDefEq (← inferType value) (← instantiateMVars r.originalType) do
      return false
    admitCallback r
    let ledger := (← read).ledger
    r.activeStart.set (some (← ledger.get))
    let (found, _) ← tryFinally' (do
      checkDeadline
      let found ← r.next
      if found then
        -- Acceptance may have escaped to IO storage and requested an immediate
        -- stop. No owned/inherited heuristic quota may reverse that stop.
        withTheReader SearchCtx (fun ctx => { ctx with scopedBudgetCheck := none }) checkDeadline
      else
        checkDeadline
      return found) fun _ => do
        if let some start ← r.activeStart.get then
          let delta := subLedger (← ledger.get) start
          record r fun c => { c with continuation := addLedger c.continuation delta }
        r.activeStart.set none
    return found

private def constructors (target : Expr) : MetaM (List Name) := do
  let .const name _ := target.getAppFn | return []
  let some (.inductInfo info) := (← getEnv).find? name | return []
  if isClass (← getEnv) name then return []
  return info.ctors

private def unassignedData? (children : List MVarId) : SearchM (Option (List MVarId)) := do
  let mut remaining := []
  for child in children do
    checkDeadline
    if ← child.isAssignedOrDelayedAssigned then continue
    let usable ← child.withContext do dataType? (← child.getType)
    if usable.isNone then return none
    remaining := remaining ++ [child]
  return some remaining

/-- Credits are shared across the entire worklist, never copied per sibling.
Only completed calls the original continuation; arguments use this filler. -/
private partial def fill (r : Run) (todo : List (MVarId × Nat)) (credit : Nat)
    : SearchM Bool := do
  match todo with
  | [] => completed r credit
  | (g, depth) :: tail =>
    if ← g.isAssignedOrDelayedAssigned then return ← fill r tail credit
    g.withContext do
      checkDeadline
      charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
      let some target ← dataType? (← g.getType) | return false
      let matchCount ← IO.mkRef 0
      for decl in r.locals do
        checkDeadline
        if (← matchCount.get) >= 8 then break
        if decl.isImplementationDetail || ((← getLCtx).find? decl.fvarId).isNone then continue
        let type ← instantiateMVars decl.type
        if type.hasExprMVar then continue
        if let some value := decl.value? (allowNondep := true) then
          if (← instantiateMVars value).hasExprMVar then continue
        if ← alternative (do
            admitAttempt r .seed
            unless ← isDefEq type target do return false
            matchCount.modify (· + 1)
            g.assign decl.toExpr
            fill r tail credit) then return true
      let ctors ← constructors target
      -- Probe the same free constructor leaves as depth-zero search. Every
      -- apply is charged, including rejected probes of non-nullary constructors.
      for name in ctors do
        if ← alternative (do
            admitAttempt r .head
            let children ← g.apply (← mkConstWithFreshMVarLevels name) applyCfg
            let remaining ← children.filterM fun child => do
              return !(← child.isAssignedOrDelayedAssigned)
            unless remaining.isEmpty do return false
            fill r tail credit) then return true
      if credit == 0 || depth == 0 then return false
      let targetHead := target.getAppFn.constName?
      let mut providers : Array Name := #[]
      unless r.cfg.skip.contains "9" do
        for provider in r.cfg.providers do
          checkDeadline
          if provider.head.isNone || provider.head != targetHead || provider.arity > 2 then continue
          providers := providers.push provider.name
          if providers.size == 16 then break
      let heads := providers.toList.map (fun name => (name, false)) ++
        ctors.map (fun name => (name, true))
      for (name, isConstructor) in heads do
        if ← alternative (do
            admitAttempt r .head
            let children ← g.apply (← mkConstWithFreshMVarLevels name) applyCfg
            let some remaining ← unassignedData? children | return false
            if isConstructor && remaining.isEmpty then return false
            fill r (remaining.map (fun child => (child, depth - 1)) ++ tail) (credit - 1)) then
          return true
      return false

/-- Bounded early branch composition. The caller supplies provenance by invoking
this only for an eligible native outer induction minor; the direct API is an
internal test seam. The production caller uses default limits and original next.

The stats are inclusive continuation deltas, not self-time. Nested tiers are
already included in an outer continuation and must not be summed again.
-/
def run (cfg : SearchConfig) (g : MVarId) (depth : Nat) (locals : Array LocalDecl)
    (next : SearchM Bool) (limits : Limits := {})
    (stats? : Option (IO.Ref Stats) := none) : SearchM Bool := alternative do
  checkDeadline
  if cfg.contract.isNone || cfg.skip.contains "composition" || depth == 0 then return false
  let start ← IO.monoMsNow
  let ctx ← read
  let slice := match ctx.deadline with
    | some deadline => min limits.maxSliceMs ((deadline - start) / 4)
    | none => limits.maxSliceMs
  if slice == 0 then return false
  let totalDeadline := start + slice
  let originalType ← instantiateMVars (← g.getType)
  unless (← g.withContext (dataType? originalType)).isSome do return false
  let stats ← match stats? with
    | some stats => pure stats
    | none => IO.mkRef ({} : Stats)
  -- A supplied diagnostics reference is an output for this invocation, not a
  -- cache of old assignments/counters. Nested invocations allocate their own.
  stats.set {}
  for grade in [0, 1] do
    let activeStart ← IO.mkRef (none : Option Ledger)
    let gradeAttempts := if grade == 0 then limits.attempts / 4 else limits.attempts
    let gradeCallbacks := if grade == 0 then limits.callbacks / 4 else limits.callbacks
    let gradeRules := if grade == 0 then limits.continuationRules / 4 else limits.continuationRules
    let gradeDeadline := if grade == 0 then start + slice / 4 else totalDeadline
    stats.modify fun s => { s with entered := s.entered.set! grade true }
    let exhausted : MetaM Bool := do
      let now ← IO.monoMsNow
      if now >= totalDeadline || now >= gradeDeadline then return true
      let s ← stats.get
      let active ← match ← activeStart.get with
        | none => pure 0
        | some old => pure ((← ctx.ledger.get).ruleApplications - old.ruleApplications)
      return s.total.continuation.ruleApplications + active >= limits.continuationRules ||
        (s.grades[grade]!).continuation.ruleApplications + active >= gradeRules
    -- Each invocation captures the caller's scope, never the previous grade's.
    -- The owner catch in withScopedBudget occurs after its result-aware restore.
    if ← withScopedBudget exhausted (fun stop => alternative do
        let r : Run := {
          cfg := cfg
          root := g
          originalType := originalType
          locals := locals
          limits := limits
          stats := stats
          grade := grade
          gradeAttempts := gradeAttempts
          gradeCallbacks := gradeCallbacks
          activeStart := activeStart
          stop := stop
          next := next }
        fill r [(g, depth)] (grade + 1)) then return true
  return false

end BranchComposition

mutual
/-- Structural recursion on a recursive inductive local (Section 17): the
recursor with a constant motive; each constructor branch receives its
induction hypotheses as recursive-call capabilities. Bounded like a split. -/
partial def structuralRecursion (cfg : SearchConfig) (leaf : Leaf) (splits d : Nat)
    (g : MVarId) (locals : Array LocalDecl) (rest : List Goal) (consumed : List FVarId := [])
    (allowNatGuards : Bool := false) (allowBranchComposition : Bool := false) : SearchM Bool := do
  if splits = 0 then return false
  for decl in locals do
    if let some ii ← timed "inductive" (inductiveOfLocal decl) then
      unless ii.isRec && ii.numIndices == 0 && ii.name != ``Nat do continue
      if ← alternative (do
          let subgoals ← g.induction decl.fvarId (mkRecName ii.name)
          search cfg leaf (splits - 1)
            (subgoals.toList.map (fun s => {
              mvar := s.mvarId, depth := d, consumed, allowNatGuards
              tryBranchComposition := allowBranchComposition && !s.fields.isEmpty }) ++ rest)) then
        return true
  return false

/-- One bounded outer induction on Nat or a regular single-index family.
Native Lean computes the motive and reverts dependent locals. Unsupported
indices (compound, repeated, or dependent in an illegal order) fail inside
the transaction; they are not evidence that the requested type is impossible.
Existing nonindexed recursion retains its separate rule and original order. -/
partial def extendedStructuralRecursion (cfg : SearchConfig) (leaf : Leaf) (splits d : Nat)
    (g : MVarId) (locals : Array LocalDecl) (rest : List Goal) (consumed : List FVarId)
    (allowNatGuards : Bool := false) : SearchM Bool := do
  if splits = 0 || cfg.skip.contains "rec" then return false
  -- Prefer the indexed major to its Nat index. This order is fixed and does
  -- not introduce a choice of stronger or invented motives.
  for indexed in [true, false] do
    for decl in locals do
      let some ii ← inductiveOfLocal decl | continue
      if indexed then
        unless ii.isRec && ii.numIndices == 1 && ii.all.length == 1 && ii.numNested == 0 do continue
      else
        unless ii.name == ``Nat do continue
      if ← alternative (do
          checkDeadline
          let recursorName := mkRecName ii.name
          if indexed then
            let info ← mkRecursorInfo recursorName
            let majorType ← whnfR (← instantiateMVars decl.type)
            let _ ← getMajorTypeIndices g `leant2_induction info majorType
          let subgoals ← timed "induction.extended" (g.induction decl.fvarId recursorName)
          let children ← subgoals.toList.mapM fun s => do
            let consumed ← inductionConsumed s consumed
            return ({ mvar := s.mvarId, depth := d, consumed, allowNatGuards } : Goal)
          -- The current delayed-assignment residual representation is not a
          -- typed dependent closure language. Keep indexed branches until the
          -- original contract can be checked on a closed program instead of
          -- extending partial-pruning claims to the newly supported motives.
          let cfg := if indexed then { cfg with skip := "residual" :: cfg.skip } else cfg
          search cfg leaf (splits - 1) (children ++ rest)) then
        return true
  return false

/-- One constructive Nat guard below each enabled program goal. Branches lose
guard and extended-induction permission; unrelated sibling obligations retain
their own metadata. The shared split allowance is consumed once, exactly like
existing native case analysis. -/
partial def constructiveNatGuards (cfg : SearchConfig) (leaf : Leaf) (splits d : Nat)
    (g : MVarId) (locals : Array LocalDecl) (rest : List Goal)
    (consumed : List FVarId := []) : SearchM Bool := do
  if splits == 0 || cfg.contract.isNone || cfg.skip.contains "guards" then return false
  let target ← instantiateMVars (← g.getType)
  if target.hasExprMVar || (← isTypeSort target) || (← isProp target) ||
      (← isClass? target).isSome then return false
  let ctx ← read
  for predicate in ← timed "guards.grammar" (natGuardPredicates locals (checkDeadline.run ctx)) do
    checkDeadline
    if ← splitNatGuard g predicate (fun positive negative =>
        -- Native guard proof binders create another delayed-assignment closure
        -- shape. Initially keep every guarded partial candidate until its full
        -- contract can be checked; focused examples do not prove this closure
        -- representation sound for pruning all dependent guard branches.
        search { cfg with skip := "residual" :: cfg.skip } leaf (splits - 1)
          ([{ mvar := positive, depth := d, consumed },
            { mvar := negative, depth := d, consumed }] ++ rest)) then
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
    if let some prune := cfg.partialPruner then
      let refuted ← timed "prune.goal" (prune g)
      checkDeadline
      if refuted then return false
    g.withContext do
    let target ← timed "entry" (do instantiateMVars (← g.getType))
    -- Preserve genuine local lets in closed frontend telescopes. Reducing the
    -- target first would erase a terminal let before it can become a provider.
    -- Native introduction keeps its definitional value and local-instance role.
    if target.cleanupAnnotations.isLet then
      charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
      return ← alternative do
        let (_, next) ← timed "intro" g.intro1P
        search cfg leaf splits ({ goal with mvar := next } :: rest)
    if leant2.traceNodes.get (← getOptions) then
      IO.println s!"[leant2]     node {← ppExpr target} depth {depth} splits {splits} rest {rest.length}"
    -- a proposition about open holes (the contract on a partial program) is
    -- decided once the holes are filled: it yields to every other obligation
    -- (class goals are not such propositions: an instance determines type holes)
    -- (nor is a hole whose type is itself a metavariable: `?h : ?P` is
    -- determined by an exact local, which also fixes `?P`)
    let isResidual (t : Expr) : MetaM Bool := do
      if !t.hasExprMVar || t.getAppFn.isMVar then return false
      unless ← isProp t do return false
      return (← isClass? t).isNone
    if !rest.isEmpty && (← timed "rotation" (isResidual target)) then
      let other ← timed "rotation" do
        let mut other := false
        for r in rest do
          unless ← isResidual (← instantiateMVars (← r.mvar.getType)) do other := true; break
        pure other
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
    -- (not at depth 0: a leaf is closed by an exact local and the closed
    -- program is decided at the contract goal anyway)
    if cfg.recursionFirst && depth > 0 && !cfg.skip.contains "residual" then  -- i.e. a contract is present
      let refuted ← timed "residual" do
        let mut refuted := false
        for pending in rest do
          let pty ← timed "residual.scan" (instantiateMVars (← pending.mvar.getType))
          if pty.hasExprMVar && (← timed "residual.scan" (isProp pty)) then
            if ← partialRefute cfg pty then refuted := true; break
        pure refuted
      if refuted then return false
    charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
    let targetW ← timed "whnf" (whnfR target)
    let d := depth - 1
    let consumed := goal.consumed
    -- A program flag must not spill into witness search inside a proof, type
    -- invention, or dictionary construction. Clear it before building children.
    let allowNatGuards ← if !goal.allowNatGuards || splits == 0 || cfg.contract.isNone ||
        cfg.skip.contains "guards" || target.hasExprMVar || targetW.isSort then
      pure false
    else if ← isProp target then pure false
    else pure (← isClass? target).isNone
    let cont (children : List MVarId) (isRootSubtypeConstructor : Bool := false) : SearchM Bool :=
      -- `Subtype.mk` creates the root program before its proof obligation.
      -- It is the only constructor through which outer-body eligibility flows.
      let rootProgramField := isRootSubtypeConstructor && cfg.contract.isSome &&
        cfg.root == some g && targetW.isAppOfArity ``Subtype 2
      let rootSubtype := rootProgramField && goal.allowExtendedRecursion
      search cfg leaf splits (children.mapIdx (fun i m => {
        mvar := m, depth := d, consumed, allowExtendedRecursion := rootSubtype && i == 0
        allowNatGuards := allowNatGuards || (rootProgramField && i == 0) }) ++ rest)
    -- like `cont`, but the children may not apply `fv` again
    let contConsuming (fv : FVarId) (children : List MVarId) : SearchM Bool :=
      search cfg leaf splits
        (children.map (fun m => { mvar := m, depth := d, consumed := fv :: consumed, allowNatGuards }) ++ rest)
    let applyHead (e : Expr) : SearchM Bool := alternative do
      charge fun l => { l with unifications := l.unifications + 1 }
      let children ← timed "apply" (g.apply e applyCfg)
      cont children (e.isConstOf ``Subtype.mk)
    -- Decide the exact closed root contract before exploring its ordinary
    -- proof constructors. Stuck or ineligible checks preserve the old grammar.
    let closedContract ← timed "contract.closed" (evalClosedRootContract cfg g)
    match closedContract with
    | some .refuted => return false
    | some (.proved proof) =>
      if ← alternative (do
          g.assign proof
          checkDeadline
          let found ← cont []
          if found then
            withTheReader SearchCtx (fun ctx => { ctx with scopedBudgetCheck := none }) checkDeadline
          else
            checkDeadline
          return found) then return true
    | _ => pure ()
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
    -- leaves are free: exact locals above, and nullary constructors here
    -- (`[]`, `none`, `true`); everything below consumes depth
    if depth = 0 then
      if let .const iname _ := targetW.getAppFn then
        if let some (.inductInfo ii) := (← getEnv).find? iname then
          for c in ii.ctors do
            if isClass (← getEnv) iname then break
            if ← alternative (do
                let children ← g.apply (← mkConstWithFreshMVarLevels c) applyCfg
                if children.isEmpty then cont [] else return false) then return true
      return false
    -- 1. introduction (default transparency, so that `Not` and similar unfold).
    -- Invertible, hence free of depth cost.
    if (← timed "intro" (whnf target)).isForall then
      return ← alternative do
        let (_, g') ← timed "intro" g.intro1P
        search cfg leaf splits
          ({ mvar := g', depth, consumed, allowExtendedRecursion := goal.allowExtendedRecursion, allowNatGuards,
             tryBranchComposition := goal.tryBranchComposition } :: rest)
    -- 2. invertible destructuring (does not consume depth or splits)
    for decl in locals do
      if let some ii ← timed "inductive" (inductiveOfLocal decl) then
        -- class instances are taken apart by projection (rule 6): `inst.out`
        -- rather than `C.casesOn inst fun out => ...`
        if isInvertible ii && !isClass (← getEnv) ii.name then
          if ← alternative (do
              let subgoals ← g.cases decl.fvarId
              search cfg leaf splits
                (subgoals.toList.map (fun s => {
                  mvar := s.mvarId, depth, consumed
                  allowExtendedRecursion := goal.allowExtendedRecursion, allowNatGuards
                  tryBranchComposition := goal.tryBranchComposition }) ++ rest)) then
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
              (subgoals.toList.map (fun s => { mvar := s.mvarId, depth := d, consumed, allowNatGuards }) ++ rest)) then
          return true
    -- 2c. structural recursion first, under a contract, at the outermost level
    -- only (nested recursion remains a late alternative, rule 9d)
    let recurseNow := cfg.recursionFirst && !targetW.isSort && splits == cfg.maxSplits
    if recurseNow then
      if ← structuralRecursion cfg leaf splits d g locals rest consumed allowNatGuards
          (goal.allowExtendedRecursion && cfg.contract.isSome) then return true
    -- 3. reflexivity
    if targetW.isAppOfArity ``Eq 3 then
      if ← alternative (do g.refl; cont []) then return true
    let targetIsSort ← isTypeSort target
    -- 3b. closed class goals: Lean's own instance resolution (canonical instance mode)
    if !target.hasExprMVar then
      if (← isClass? target).isSome then
        if ← alternative (do
            match ← probeInstance? target with
            | some inst => g.assign inst; cont []
            | none => return false) then return true
    -- A small composition prefix on actual outer native induction minors.
    -- It resumes this exact continuation and returns to the old rules on miss.
    if goal.tryBranchComposition && !cfg.skip.contains "composition" then
      if ← BranchComposition.run cfg g depth locals (search cfg leaf splits rest) then return true
    -- Bounded constructive conditional introduction, confined to program
    -- obligations. A skipped guard is a grammar restriction, never refutation.
    if allowNatGuards then
      if ← constructiveNatGuards cfg leaf splits d g locals rest consumed then return true
    if targetIsSort then
      -- type invention: types of locals first, then the closed frontier
      let frontier ← timed "frontier" (localFrontier locals)
      for t in frontier ++ cfg.typeFrontier do
        if ← alternative (do
            if ← timed "frontier" (do isDefEq (← inferType t) target) then
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
      let dty ← timed "6.proj" (do whnfR (← instantiateMVars decl.type))
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
    -- (never a class: an instance built by hand, `Choice.mk True.intro`, leaves
    -- the class arguments undetermined; instances come from resolution or
    -- from instance providers, which fix those arguments)
    if let some iname := targetHead then
      if let some (.inductInfo ii) := (← getEnv).find? iname then
        if !isClass (← getEnv) iname then
          for c in ii.ctors do
            if ← applyHead (← mkConstWithFreshMVarLevels c) then return true
    if !targetIsSort then
      -- 7. application of locals (default transparency: `¬p` is a function)
      for decl in locals do
        if consumed.contains decl.fvarId then continue
        let dty ← timed "7.whnf" (do whnf (← instantiateMVars decl.type))
        unless dty.isForall do continue
        -- a Church-encoded datum (`forall R, ... -> R`) is an eliminator: it is
        -- not applied again inside its own continuation arguments
        let eliminator ← timed "7.elim" (isChurchEliminator dty)
        if ← alternative (do
            charge fun l => { l with unifications := l.unifications + 1 }
            let children ← timed "apply" (g.apply decl.toExpr applyCfg)
            if eliminator then contConsuming decl.fvarId children else cont children) then
          return true
      -- 7a. polymorphic locals instantiated at the accumulator type `T -> T` for
      -- the target `T` before application: `apply` cannot see that
      -- `xs (T -> T) step seed x` has one more argument than `xs T step seed`
      if !target.hasExprMVar && !cfg.skip.contains "7a" then
        let acc ← mkArrow target target
        for decl in locals do
          if consumed.contains decl.fvarId then continue
          let dty ← whnf (← instantiateMVars decl.type)
          let .forallE _ bty body _ := dty | continue
          unless (← whnfR bty).isSort do continue
          -- only folds with an accumulator-threading step gain from `T -> T`
          unless ← timed "7.elim" (isRecursiveEliminator dty) do continue
          let eliminator := true
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
        if cfg.skip.contains "7b" then break
        let dty ← whnf (← instantiateMVars decl.type)
        unless dty.isForall do continue
        if ← alternative (do
            let (args, _, resTy) ← timed "7b.prep" (forallMetaTelescopeReducing dty)
            if args.isEmpty || args.size > 3 then return false
            let filledAll ← timed "7b.prep" do
              let mut ok := true
              for a in args do
                let aty ← instantiateMVars (← inferType a)
                let mut filled := false
                for l in locals do
                  if l.fvarId == decl.fvarId then continue
                  if ← isDefEq (← inferType l.toExpr) aty then
                    if ← isDefEq a l.toExpr then filled := true; break
                unless filled do ok := false; break
              pure ok
            unless filledAll do return false
            let resTy ← instantiateMVars resTy
            -- only results that can be taken apart are worth naming
            let some hn := (← whnfR resTy).getAppFn.constName? | return false
            let some (.inductInfo _) := (← getEnv).find? hn | return false
            let val ← instantiateMVars (mkAppN decl.toExpr args)
            let g' ← g.assert (← mkFreshUserName `h) resTy val
            let (_, g'') ← g'.intro1P
            search cfg leaf splits ({ mvar := g'', depth := d, consumed, allowNatGuards } :: rest)) then return true
      -- 9. providers, head-filtered: a constant-headed conclusion must match the
      -- target head; a variable-headed provider needs a local demanding one of its
      -- argument heads
      let provs ← if cfg.classical then do pure (cfg.providers ++ (← classicalProviders))
                  else pure cfg.providers
      let localHeads ← timed "9.heads" (locals.filterMapM fun decl => do
        let dty ← whnfR (← instantiateMVars decl.type)
        return match dty.getAppFn with | .const c _ => some c | _ => none)
      for p in provs do
        if cfg.skip.contains "9" then break
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
        if cfg.skip.contains "9b" then break
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
            search cfg leaf splits (instGoals ++ otherGoals ++ [{ mvar := g'', depth := d, consumed, allowNatGuards }] ++ rest))
          then return true
      -- 9c. bounded case analysis on multi-constructor locals, after providers so
      -- that library applications (`List.map f xs`) are found before case splits
      if splits > 0 && !cfg.skip.contains "9c" then
        for decl in locals do
          if let some ii ← timed "inductive" (inductiveOfLocal decl) then
            if isInvertible ii || ii.name == ``Nat then continue
            if ← alternative (do
                let subgoals ← g.cases decl.fvarId
                search cfg leaf (splits - 1)
                  (subgoals.toList.map (fun s => { mvar := s.mvarId, depth := d, consumed, allowNatGuards }) ++ rest)) then
              return true
      -- 9d. structural recursion as a late alternative, top level only (nested
      -- recursion is not attempted: it multiplies the search without payoff here)
      if !recurseNow && splits == cfg.maxSplits then
        if ← structuralRecursion cfg leaf splits d g locals rest consumed allowNatGuards
            (goal.allowExtendedRecursion && cfg.contract.isSome) then return true
      -- 10. closed contracts and bounded local proof obligations
      if cfg.proofPortfolio then
        if ← alternative (do
            if ← timed "portfolio" (proofPortfolio cfg g closedContract.isSome) then cont []
            else return false) then
          return true
      -- A new grammar tier, after the existing rules. It cannot recursively
      -- reappear in arithmetic or constructor subterms, nor inside a recursor.
      if goal.allowExtendedRecursion && splits == cfg.maxSplits then
        if ← extendedStructuralRecursion cfg leaf splits d g locals rest consumed allowNatGuards then return true
    return false
end

end Leant2
