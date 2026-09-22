import Leant2.Native.Transaction
import Leant2.Accept.Gate
import Leant2.Native.Export

/-!
Bounded proof search in the original local context.

The service commits only a checked assignment to its incoming goal. Tactics
run on fresh goals, with incoming expression and universe metavariables frozen.
Every speculative exit restores the complete Meta/Core state, including caches,
messages, info, environment, and name generators. The SearchCtx work ledger and
deadline references deliberately remain outside rollback.

This is a local construction service, not the final acceptance gate. A returned
proof may use the original hypotheses and standard axioms; the closed candidate
still needs Leant2.Accept.Gate and the query's profile audit.
-/
namespace Leant2.LocalProof

open Lean Meta Elab

inductive Result where
  | solved (proof : Expr)
  | unresolved
  | unsupportedDependency
  | resourceExhausted
  deriving Inhabited

/-- Fixed internal budgets, in the same units as Lean's `maxHeartbeats` option.
Zero is clamped to one: it never disables the service's bound. -/
structure Config where
  preparationHeartbeats : Nat := 5000
  tacticHeartbeats : Nat := 10000
  validationHeartbeats : Nat := 5000
  deriving Inhabited

/-- Internal tier interface, exposed for adversarial tests. Production callers
use `discharge`, whose three tiers are fixed below. No external tactic text or
user-selected provider is accepted by the production entry point. -/
structure Tier where
  name : Name
  action : Tactic.TacticM Unit

private structure FrozenGoal where
  target : Expr
  lctx : LocalContext
  levelMVars : Array LMVarId

private initialize auxiliaryLimitExceptionId : InternalExceptionId ←
  registerInternalExceptionId `leant2LocalProofAuxiliaryLimit

/-- Unlike Meta.SavedState.restore, this also restores speculative caches and
diagnostics. No speculative declaration or free variable may escape: extraction
and replay below enforce that invariant before the only committed assignment. -/
private def restoring (act : SearchM α) : SearchM α := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  try
    act
  finally
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

private def withBudget (limit : Nat) (act : SearchM α) : SearchM α :=
  withCurrHeartbeats do
    let limit := max limit 1
    withOptions (fun opts => maxHeartbeats.set opts limit) do
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := limit * 1000 }) do
        checkDeadline
        checkSystem "leant2.localProof"
        let result ← act
        checkDeadline
        checkSystem "leant2.localProof"
        return result

/-- User interrupts bypass Lean's runtime handler and still run `finally`.
Leant2 deadlines and unknown internal exceptions are rethrown. Only this
service's bounded resource failures become `resourceExhausted`; ordinary tactic
or replay errors mean unresolved, never logical refutation. -/
private def classify (act : SearchM Result) : SearchM Result :=
  tryCatchRuntimeEx act fun ex => do
    if leant2.trace.get (← getOptions) then
      IO.println s!"[leant2.localProof] {← ex.toMessageData.toString}"
    if ex.isMaxHeartbeat || ex.isMaxRecDepth then return .resourceExhausted
    match ex with
    | .error .. => return .unresolved
    | .internal id _ =>
      if id == auxiliaryLimitExceptionId then return .resourceExhausted
      throw ex

/-- `simp_all` and `omega` can inspect all available locals, including local
instances and implementation-detail lets. The first slice therefore treats all
local types and let values as relevant. Fully assigned holes are instantiated;
any remaining expression dependency suspends the attempt. Incoming universe
holes remain rigid and may occur in the returned proof without being assigned. -/
private def freezeGoal (g : MVarId) : MetaM (Option FrozenGoal) := do
  let target ← instantiateMVars (← g.getType)
  if target.hasExprMVar then
    if leant2.trace.get (← getOptions) then
      IO.println s!"[leant2.localProof] open target dependency: {← ppExpr target}"
    return none
  unless ← isProp target do return none
  let lctx ← getLCtx
  let mut levels := collectLevelMVarIds target
  for decl in lctx do
    let type ← instantiateMVars decl.type
    if type.hasExprMVar then
      if leant2.trace.get (← getOptions) then
        IO.println s!"[leant2.localProof] open local type: {decl.userName} : {← ppExpr type}"
      return none
    levels := levels ++ (collectLevelMVarIds type).filter (!levels.contains ·)
    if let some value := decl.value? (allowNondep := true) then
      let value ← instantiateMVars value
      if value.hasExprMVar then
        if leant2.trace.get (← getOptions) then
          IO.println s!"[leant2.localProof] open local value: {decl.userName} := {← ppExpr value}"
        return none
      levels := levels ++ (collectLevelMVarIds value).filter (!levels.contains ·)
  return some { target, lctx, levelMVars := levels }

private def inOriginalScope (frozen : FrozenGoal) (proof : Expr) : Bool :=
  !proof.hasExprMVar && !proof.hasLooseBVars && !proof.hasSorry &&
    (collectFVars {} proof).fvarIds.all (fun id => (frozen.lctx.find? id).isSome) &&
    (collectLevelMVarIds proof).all frozen.levelMVars.contains

/-- Native tactics such as omega package proofs in auxiliary theorems. Copy
only the bodies of newly created theorems into the extracted proof, with their
universe parameters instantiated. Original constants are retained; new axioms,
opaque declarations, and definitions remain for original-environment replay to
reject. A finite expansion bound and native transform's heartbeat/recursion
checks also protect against malformed cyclic or excessively large exports. -/
private def inlineAuxiliaryTheorems (originalEnv : Environment) (proof : Expr) : SearchM Expr := do
  let speculativeEnv ← getEnv
  let remaining ← IO.mkRef 64
  Native.inlineNewTheorems originalEnv speculativeEnv remaining checkDeadline
    (.internal auxiliaryLimitExceptionId) proof

private def probeTier (cfg : Config) (frozen : FrozenGoal) (tier : Tier) : SearchM Result :=
  classify <| restoring <| withBudget cfg.tacticHeartbeats do
    checkDeadline
    let originalEnv ← getEnv
    -- Allocated inside the caller's increased mctx depth, so this goal is
    -- assignable while every incoming metavariable remains rigid.
    let scratch ← mkFreshExprMVar frozen.target .syntheticOpaque
    -- Diagnose only this tier. The entire incoming log is restored in finally;
    -- a tactic reporting an error cannot succeed by merely clearing its goals.
    modifyThe Core.State fun s => { s with messages := {} }
    let remaining ← Term.TermElabM.run' do
      Tactic.run scratch.mvarId! tier.action
    checkSystem "leant2.localProof"
    checkDeadline
    if (← getThe Core.State).messages.hasErrors then return .unresolved
    unless remaining.isEmpty && (← scratch.mvarId!.isAssignedOrDelayedAssigned) do
      return .unresolved
    -- Extract before restoring the scratch metavariable context. Merely
    -- clearing the tactic goal list does not establish a completed proof.
    let proof ← instantiateMVars scratch
    let proof ← inlineAuxiliaryTheorems originalEnv proof
    unless inOriginalScope frozen proof do return .unresolved
    return .solved proof

private def probe (cfg : Config) (g : MVarId) (tiers : Array Tier) : SearchM Result :=
  classify <| restoring do
    checkDeadline
    g.withContext do
      withNewMCtxDepth do
        let some frozen ← withBudget cfg.preparationHeartbeats (do freezeGoal g)
          | return .unsupportedDependency
        let mut exhausted := false
        for tier in tiers do
          checkDeadline
          match ← probeTier cfg frozen tier with
          | .solved proof => return .solved proof
          | .resourceExhausted => exhausted := true
          | .unresolved | .unsupportedDependency => pure ()
        checkDeadline
        return if exhausted then .resourceExhausted else .unresolved

/-- Replay uses the original context and environment after all tactic state has
been discarded. Both proof checking and comparison with the original target run
with incoming expression/universe holes frozen. No postponed universe equation
is allowed to count as a completed replay. -/
private def validate (cfg : Config) (g : MVarId) (proof : Expr) : SearchM Result :=
  classify <| restoring <| withBudget cfg.validationHeartbeats do
    checkDeadline
    g.withContext do
      withNewMCtxDepth do
        let some frozen ← freezeGoal g | return .unsupportedDependency
        unless inOriginalScope frozen proof do return .unresolved
        check proof
        unless ← isDefEq (← inferType proof) frozen.target do return .unresolved
        unless (← getThe Meta.State).postponed.isEmpty do return .unresolved
        checkSystem "leant2.localProof"
        checkDeadline
        return .solved proof

/-- Internal test seam for bounded tiers. Every tier starts afresh; partial
simplification cannot suppress the next tier. The incoming goal is the only
metavariable assigned by a successful service call. -/
def dischargeWith (cfg : Config) (g : MVarId) (tiers : Array Tier) : SearchM Result := do
  checkDeadline
  if ← g.isAssignedOrDelayedAssigned then return .unresolved
  charge fun ledger => { ledger with proofAttempts := ledger.proofAttempts + 1 }
  match ← probe cfg g tiers with
  | .solved proof =>
    match ← validate cfg g proof with
    | .solved proof =>
      -- Replay has restored its entire speculative state too. Check the lane
      -- again immediately before the sole committed operation.
      checkDeadline
      Core.checkInterrupted
      g.assign proof
      return .solved proof
    | result => return result
  | result => return result

private def tiers : Array Tier := #[
  { name := `assumptionOrRfl, action := do
      Tactic.evalTactic (← `(tactic| first | assumption | rfl)) },
  { name := `simpAll, action := do
      Tactic.evalTactic (← `(tactic| simp_all)) },
  { name := `omega, action := do
      Tactic.evalTactic (← `(tactic| omega)) }
]

/-- Bounded local proof service. In particular, False and a closed false
equality are eligible when local hypotheses are contradictory. A reduction of
the target to false is not a reason to reject a proof under those hypotheses. -/
def discharge (g : MVarId) (cfg : Config := {}) : SearchM Result :=
  dischargeWith cfg g tiers

end Leant2.LocalProof
