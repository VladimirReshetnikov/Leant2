import Leant2.Frontend.Sketch
import Leant2.Frontend.Sketch.Projection

/-! Whole-owned-hole pruning through the actual search continuation. These
tests distinguish an observed partial rejection from ordinary final-contract
rejection, retain the original kernel gate, and exercise unsupported-context
fallback. They make no timing or general delayed-graph correspondence claim. -/

namespace Leant2Tests.SketchProjectionIntegration
open Lean Meta Elab Term Leant2 Frontend.Sketch

private def context : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def pairQuery : TermElabM Query := do
  let target ← elabType (← `(Nat → Nat → Nat × Nat))
  let contract ← elabTerm (← `(fun f : Nat → Nat → Nat × Nat =>
    (f 0 1).1 = 0 ∧ (f 1 0).1 = 1 ∧ (f 0 1).2 = 1 ∧ (f 1 0).2 = 0)) none
  synthesizeSyntheticMVarsNoPostponing
  return {
    target := ← instantiateMVars target
    contract := some (← instantiateMVars contract)
    providers := #[], profile := .strictConstructive
    budgetMs := 5000, maxCandidates := 1, graceMs := 0 }

private def pairSketch : TermElabM (TSyntax `term) :=
  `(fun (x y : Nat) => ((?left : Nat), (?right : Nat)))

private def originalHole (prepared : Prepared) (name : Name) : MetaM OwnedHole := do
  let some hole := prepared.holes.find? (·.spec.sourceName.eraseMacroScopes == name)
    | throwError "integration fixture lost an original owned hole"
  return hole

private def originalLocal (hole : OwnedHole) (name : Name) : MetaM Expr := do
  for declaration in hole.declaration.lctx do
    if declaration.userName.eraseMacroScopes == name then return declaration.toExpr
  throwError "integration fixture lost an original local"

private def replay (query : Query) (candidate : Accepted) : MetaM Unit := do
  unless [candidate.program, candidate.programType, candidate.proof].all
      (fun expression => !expression.hasMVar && !expression.hasFVar &&
        !expression.hasLooseBVars && !expression.hasSorry) do
    throwError "projection integration exported an incomplete accepted object"
  unless ← isDefEq candidate.programType query.target do
    throwError "projection integration changed the original target"
  let .ok programAxioms ← kernelCheckAndAudit `Leant2Tests.SketchProjectionIntegration
      candidate.program query.target candidate.levelParams false
    | throwError "projection integration program failed original-type replay"
  let some contract := query.contract | throwError "integration fixture lost its contract"
  let .ok proofAxioms ← kernelCheckAndAudit `Leant2Tests.SketchProjectionIntegration
      candidate.proof (mkApp contract candidate.program) candidate.levelParams true
    | throwError "projection integration proof failed original-contract replay"
  unless programAxioms.isEmpty && proofAxioms.isEmpty && candidate.axioms.isEmpty do
    throwError "provider-free constructive integration fixture used an axiom"

private def first (result : Result) : TermElabM Accepted := do
  unless result.preparation.holes.size == 2 do throwError "integration fixture lost a hole"
  let .verified candidates _ := result.outcome
    | throwError "integration fixture failed: {← outcomeMessage result.outcome}"
  let some candidate := candidates[0]? | throwError "integration returned no accepted value"
  return candidate

private structure Event where
  leftIsWrongLocal : Bool
  leftIsCorrectLocal : Bool
  rightIsOpen : Bool
  refuted : Bool

-- Exact locals are tried newest first. The real search therefore first puts y
-- in the left hole. The right-hole boundary must reject that partial program,
-- then sibling rollback must permit x on the left and y on the right.
run_elab do
  let query ← pairQuery
  let contract := query.contract.get!
  let events ← IO.mkRef (#[] : Array Event)
  let accepted ← IO.mkRef (none : Option Accepted)
  discard <| withPreparedSketch query.target (← pairSketch) fun prepared => do
    let left ← originalHole prepared `left
    let right ← originalHole prepared `right
    let x ← originalLocal left `x
    let y ← originalLocal left `y
    let projection ← Projection.build prepared
    let observations ← mkObservations contract query.target
    unless observations.size == 4 do throwError "integration lost a contract observation"
    let ctx ← context
    let callback : MVarId → SearchM Bool := fun goal => do
      if goal != left.pending && goal != right.pending then return false
      let active ← read
      let report ← Projection.observe projection query.profile contract observations
        (check := checkDeadline.run active)
      if goal == right.pending then
        let body ← instantiateMVars (mkMVar left.pending)
        let rightIsOpen := !(← right.pending.isAssignedOrDelayedAssigned)
        events.modify (·.push {
          leftIsWrongLocal := body == y
          leftIsCorrectLocal := body == x
          rightIsOpen
          refuted := report.refuted })
      return report.refuted
    let cfg : SearchConfig := {
      profile := query.profile, providers := #[], contract := some contract
      residual := ← mkResidual contract query.target
      recursionFirst := true, maxSplits := 0, skip := ["residual"]
      partialPruner := some callback }
    let savedCore ← getThe Core.State
    let savedMeta ← getThe Meta.State
    let completed ← IO.mkRef 0
    enumerateInitialized ctx cfg (fun depth => do
      modifyThe Core.State fun _ => savedCore
      modifyThe Meta.State fun _ => savedMeta
      checkDeadline
      let proof ← mkFreshExprMVar (contract.beta #[prepared.expression])
      let root ← mkFreshExprMVar (← mkAppM ``Subtype #[contract])
      root.mvarId!.assign (mkApp4 (mkConst ``Subtype.mk [.succ .zero])
        query.target contract prepared.expression proof)
      return {
        root := root.mvarId!
        goals := [{ mvar := left.pending, depth }, { mvar := right.pending, depth },
          { mvar := proof.mvarId!, depth }] })
      (fun expression => do
        unless expression.isAppOfArity ``Subtype.mk 4 do
          throwError "integration leaf received a component instead of the whole root"
        let program := expression.getArg! 2
        let proof := expression.getArg! 3
        let .ok candidate ← gate query.profile program query.target
            (some (proof, mkApp contract program))
          | throwError "integration leaf failed the exact original gate"
        accepted.set (some candidate)
        return true)
      (do return (← accepted.get).isSome) [0, 1, 2] completed
  let events ← events.get
  unless events.any (fun event => event.leftIsWrongLocal && event.rightIsOpen && event.refuted) do
    throwError "real callback did not reject wrong left while right was still open"
  unless events.any (fun event => event.leftIsCorrectLocal && event.rightIsOpen && !event.refuted) do
    throwError "partial rejection did not restore a productive sibling branch"
  let some candidate ← accepted.get | throwError "pruned search never reached whole-root acceptance"
  replay query candidate
  let expected ← elabTerm (← `(fun (x y : Nat) => (x, y))) (some query.target)
  unless ← isDefEq candidate.program expected do
    throwError "partial pruning changed the completed original binder meaning"

-- Public integration and the explicit ablation retain exact acceptance.
-- The preceding callback test, rather than these two PASSes alone, witnesses
-- the pruning action; no elapsed-time or candidate-count advantage is assumed.
run_elab do
  let query ← pairQuery
  let source ← pairSketch
  for disabled in [false, true] do
    let candidate ← withOptions (fun options => options.set `leant2.skipRules
        (if disabled then "sketchProjection" else "")) do
      first (← synthesizeSketch query source)
    replay query candidate
    let expected ← elabTerm (← `(fun (x y : Nat) => (x, y))) (some query.target)
    unless ← isDefEq candidate.program expected do
      throwError "projection ablation changed the accepted pair"

-- A genuine original let is supported by preparation/search but deliberately
-- excluded from projection. Confirm the exclusion before requiring ordinary
-- synthesis to retain this same two-hole sketch and its original contract.
run_elab do
  let query ← pairQuery
  let source ← `(fun (x y : Nat) => let a : Nat := x; ((?left : Nat), (?right : Nat)))
  discard <| withPreparedSketch query.target source fun prepared => do
    unless prepared.holes.any (fun hole =>
        hole.declaration.lctx.foldl (fun found declaration => found || declaration.isLet) false) do
      throwError "unsupported-context fixture did not retain an original let"
    if (← Projection.tryBuild prepared).isSome then
      throwError "original let unexpectedly entered the bounded projection fragment"
  for disabled in [false, true] do
    let candidate ← withOptions (fun options => options.set `leant2.skipRules
        (if disabled then "sketchProjection" else "")) do
      first (← synthesizeSketch query source)
    replay query candidate

private def observeAll (action : MetaM α) : MetaM (Except Exception α) := do
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch exception => return .error exception

-- The callback inherits the actual scoped quota; after it returns, search
-- checks the deadline before constructing or accepting any further term.
-- Quota exhaustion is controlled by a Boolean, not elapsed wall time.
run_meta do
  for prune in [false, true] do
    withoutModifyingState do
      let ctx ← context
      let expired ← IO.mkRef false
      let called ← IO.mkRef false
      let reachedLeaf ← IO.mkRef false
      let goal ← mkFreshExprMVar (mkConst ``Nat)
      let cfg : SearchConfig := { partialPruner := some fun _ => do
        called.set true
        expired.set true
        return prune }
      let result ← (withScopedBudget (do expired.get) fun _ =>
        search cfg (do reachedLeaf.set true; return true) 0
          [{ mvar := goal.mvarId!, depth := 0 }]).run ctx
      unless !result && (← called.get) && !(← reachedLeaf.get) &&
          !(← goal.mvarId!.isAssigned) do
        throwError "partial callback bypassed scoped quota or leaked a completion"

-- Real native cancellation set inside the callback must escape unchanged;
-- the surrounding alternative restores before the exception is observed.
run_meta do
  withoutModifyingState do
    let ctx ← context
    let token ← IO.CancelToken.new
    let called ← IO.mkRef false
    let reachedLeaf ← IO.mkRef false
    let goal ← mkFreshExprMVar (mkConst ``Nat)
    let cfg : SearchConfig := { partialPruner := some fun _ => do
      called.set true
      token.set
      return false }
    let result ← observeAll <| withTheReader Core.Context
        (fun context => { context with cancelTk? := some token }) do
      (alternative <| search cfg (do reachedLeaf.set true; return true) 0
        [{ mvar := goal.mvarId!, depth := 0 }]).run ctx
    let .error exception := result | throwError "callback cancellation became ordinary search"
    unless exception.isInterrupt && (← called.get) && !(← reachedLeaf.get) &&
        !(← goal.mvarId!.isAssigned) do
      throwError "callback cancellation changed identity or escaped after acceptance"

end Leant2Tests.SketchProjectionIntegration
