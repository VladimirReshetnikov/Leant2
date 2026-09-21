import Leant2.Engine

/-! Transactional cancellation checks use injected native/resource exceptions
and a real scoped IO.CancelToken. No timing sleeps or search budgets are needed. -/

namespace Leant2Tests.Cancellation

open Lean Meta Elab Term Leant2

private def observeAll (act : MetaM α) : MetaM (Except Exception α) := do
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try return .ok (← act)
  catch e => return .error e

private def context : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def sameExceptionKind (a b : Exception) : Bool :=
  match a, b with
  | .internal a _, .internal b _ => a == b
  | .error _ a, .error _ b => a.stripNestedTags.kind == b.stripNestedTags.kind
  | _, _ => false

private def heartbeat : Exception :=
  .error .missing (.tagged `runtime.maxHeartbeats m!"test heartbeat limit")

private def recursionDepth : Exception :=
  .error .missing (.tagged `runtime.maxRecDepth m!"test recursion limit")

private def ordinary : Exception := .error .missing m!"ordinary rule failure"

-- A runtime-looking tag that Lean does not classify as a resource limit must
-- not be absorbed by the lane boundary.
private def unrelated : Exception :=
  .error .missing (.tagged `runtime.cancellationRegression m!"unrelated runtime failure")

private def mark (ctx : SearchCtx) (g : MVarId) (name : Name) : MetaM Unit := do
  g.assign (mkNatLit 7)
  addDecl <| .defnDecl {
    name, levelParams := [], type := mkConst ``Nat, value := mkNatLit 11,
    hints := .abbrev, safety := .safe }
  logInfo "cancellation regression: this message must be rolled back"
  ctx.ledger.modify fun l => { l with ruleApplications := l.ruleApplications + 1 }

private def markerName : MetaM Name := do
  return ((← getEnv).asyncPrefix?.getD `Leant2Tests.Cancellation) ++
    (← mkFreshUserName `transactionLeak)

private def checkRestored (ctx : SearchCtx) (g : MVarId) (name : Name)
    (messageCount : Nat) : MetaM Unit := do
  if ← g.isAssigned then throwError "cancelled transaction leaked a metavariable assignment"
  if (← getEnv).contains name then throwError "cancelled transaction leaked a declaration"
  unless (← getThe Core.State).messages.toList.length == messageCount do
    throwError "cancelled transaction leaked a diagnostic"
  unless (← ctx.ledger.get).ruleApplications == 1 do
    throwError "transaction rollback refunded or duplicated work"

private def checkBranchFailure (asAlternative : Bool) (ex : Exception)
    (mustPropagate : Bool) : MetaM Unit := withoutModifyingState do
  let ctx ← context
  let g ← mkFreshExprMVar (mkConst ``Nat)
  let name ← markerName
  let messageCount := (← getThe Core.State).messages.toList.length
  let act : SearchM Bool := do
    mark ctx g.mvarId! name
    throw ex
  let result ← observeAll <| (if asAlternative then alternative act
    else do return (← attempt act).getD false).run ctx
  match result with
  | .ok r =>
    if mustPropagate || r then throwError "transaction swallowed a cancellation/resource exception"
  | .error actual =>
    unless mustPropagate && sameExceptionKind actual ex do
      throwError "transaction changed ordinary failure or exception identity"
  checkRestored ctx g.mvarId! name messageCount

run_meta do
  for asAlternative in [false, true] do
    checkBranchFailure asAlternative ordinary false
    for ex in [Exception.internal interruptExceptionId, .internal deadlineExceptionId,
        .internal graceExceptionId, .internal unsupportedSyntaxExceptionId,
        heartbeat, recursionDepth] do
      checkBranchFailure asAlternative ex true

-- Successful branches still commit; Boolean false still backtracks. These
-- guards prevent cleanup fixes from changing ordinary search control semantics.
run_meta do
  for asAlternative in [false, true] do
    withoutModifyingState do
      let ctx ← context
      let g ← mkFreshExprMVar (mkConst ``Nat)
      let name ← markerName
      let action : SearchM Bool := do
        mark ctx g.mvarId! name
        return true
      let result ← (if asAlternative then alternative action
        else do return (← attempt action).getD false).run ctx
      unless result && (← g.mvarId!.isAssigned) && (← getEnv).contains name do
        throwError "successful transaction failed to commit"
  withoutModifyingState do
    let ctx ← context
    let g ← mkFreshExprMVar (mkConst ``Nat)
    let name ← markerName
    let count := (← getThe Core.State).messages.toList.length
    if ← (alternative (do mark ctx g.mvarId! name; return false)).run ctx then
      throwError "false alternative stopped enumeration"
    checkRestored ctx g.mvarId! name count
  withoutModifyingState do
    let ctx ← context
    let g ← mkFreshExprMVar (mkConst ``Nat)
    let name ← markerName
    let answer ← (attempt (do mark ctx g.mvarId! name; return false)).run ctx
    unless answer == some false && (← g.mvarId!.isAssigned) && (← getEnv).contains name do
      throwError "attempt incorrectly treated a returned false value as failure"

private def checkLane (ex : Exception) (stop : Option SearchStop) : MetaM Unit := withoutModifyingState do
  let ctx ← context
  -- A future grace bound does not conceal a lane deadline or resource limit.
  ctx.graceDeadline.set (some ((← IO.monoMsNow) + 1000000))
  let timedOut ← IO.mkRef false
  let g ← mkFreshExprMVar (mkConst ``Nat)
  let name ← markerName
  let count := (← getThe Core.State).messages.toList.length
  let result ← observeAll <| withLane ctx.ledger ctx.refutedPrograms ctx.graceDeadline
      timedOut 1000000 (fun _ => do mark ctx g.mvarId! name; throw ex)
  match result, stop with
  | .ok _, some reason =>
    unless (← timedOut.get) == (reason != .grace) do
      throwError "lane confused grace completion with resource exhaustion"
  | .error actual, none =>
    unless sameExceptionKind actual ex do throwError "lane changed the escaping exception"
    if ← timedOut.get then throwError "lane counted user cancellation/error as a timeout"
  | _, _ => throwError "lane consumed or propagated the wrong exception category"
  checkRestored ctx g.mvarId! name count

run_meta do
  checkLane (.internal deadlineExceptionId) (some .deadline)
  checkLane (.internal graceExceptionId) (some .grace)
  checkLane heartbeat (some .heartbeats)
  checkLane recursionDepth (some .recursionDepth)
  checkLane (.internal interruptExceptionId) none
  checkLane (.internal unsupportedSyntaxExceptionId) none
  checkLane ordinary none
  checkLane unrelated none

-- Deadline classification is deterministic and independent of CI clock speed.
run_meta do
  for (now, lane, grace, expected) in [
      (10, some 10, none, none),
      (11, some 10, some 20, some SearchStop.deadline),
      (21, some 10, some 20, some SearchStop.deadline),
      (21, some 20, some 10, some SearchStop.grace),
      (11, none, some 10, some SearchStop.grace)] do
    unless expiredDeadline? now lane grace == expected do
      throwError "incorrect deadline/grace boundary classification"

class PendingChoice (α : Type) where
  value : α

instance : PendingChoice Nat := ⟨0⟩

-- A native stuck-instance control exception remains an ordinary deferred
-- branch. It must not become an escaping internal error under the new policy.
run_meta do
  withoutModifyingState do
    let ctx ← context
    let α ← mkFreshExprMVar (mkSort (.succ .zero))
    let target := mkApp (mkConst ``PendingChoice) α
    unless (← trySynthInstance target) matches .undef do
      throwError "open-class fixture did not exercise a stuck instance"
    let goal ← mkFreshExprMVar target
    let cfg : SearchConfig := { proofPortfolio := false, maxSplits := 0 }
    let result ← observeAll <| (search cfg (pure true) 0
      [{ mvar := goal.mvarId!, depth := 1 }]).run ctx
    match result with
    | .ok false => pure ()
    | _ => throwError "open class search did not remain an ordinary stalled branch"
    if ← α.mvarId!.isAssigned then throwError "stalled instance probe assigned its input type"
    α.mvarId!.assign (mkConst ``Nat)
    unless ← (search cfg (pure true) 0 [{ mvar := goal.mvarId!, depth := 1 }]).run ctx do
      throwError "class search failed after its input type became known"
    unless ← goal.mvarId!.isAssigned do throwError "class instance success did not commit"
  withoutModifyingState do
    let p ← mkFreshExprMVar (mkSort .zero)
    let contract := mkLambda `f .default (mkConst ``Nat) p
    let residual ← mkResidual contract (mkConst ``Nat)
    unless residual.size == 1 && residual[0]!.2.isNone do
      throwError "stuck residual decider was not deferred"
    if ← p.mvarId!.isAssigned then throwError "residual instance probe assigned its proposition"

-- Native cancellation is detected by checkDeadline even when there is no lane
-- deadline. The token lives only in a local reader context, leaving the test
-- runner uncancelled when the finalizer and assertions execute.
run_meta do
  withoutModifyingState do
    let ctx ← context
    let token ← IO.CancelToken.new
    let g ← mkFreshExprMVar (mkConst ``Nat)
    let name ← markerName
    let count := (← getThe Core.State).messages.toList.length
    let result ← observeAll <| withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
      (attempt (do
        mark ctx g.mvarId! name
        token.set
        checkDeadline
        return true)).run ctx
    match result with
    | .error ex => unless ex.isInterrupt do throwError "native cancellation changed exception kind"
    | .ok _ => throwError "checkDeadline ignored native cancellation"
    checkRestored ctx g.mvarId! name count

-- Standalone tacticProve preserves successful proof assignment, restores failed
-- proof attempts, and lets native cancellation escape without losing cleanup.
run_meta do
  withoutModifyingState do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let count := (← getThe Core.State).messages.toList.length
    unless ← tacticProve goal.mvarId! do throwError "proof success behavior changed"
    unless ← goal.mvarId!.isAssigned do throwError "successful proof was rolled back"
    unless (← getThe Core.State).messages.toList.length == count do
      throwError "successful proof leaked diagnostics"
  withoutModifyingState do
    let goal ← mkFreshExprMVar (mkConst ``False)
    let count := (← getThe Core.State).messages.toList.length
    if ← tacticProve goal.mvarId! then throwError "false proof attempt succeeded"
    if ← goal.mvarId!.isAssigned then throwError "failed proof leaked assignment"
    unless (← getThe Core.State).messages.toList.length == count do
      throwError "failed proof leaked diagnostics"
  withoutModifyingState do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let token ← IO.CancelToken.new
    token.set
    let count := (← getThe Core.State).messages.toList.length
    let result ← observeAll <| withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
      tacticProve goal.mvarId!
    match result with
    | .error ex => unless ex.isInterrupt do throwError "proof changed native cancellation"
    | .ok _ => throwError "proof swallowed native cancellation"
    if ← goal.mvarId!.isAssigned then throwError "cancelled proof leaked assignment"
    unless (← getThe Core.State).messages.toList.length == count do
      throwError "cancelled proof leaked diagnostics"

end Leant2Tests.Cancellation
