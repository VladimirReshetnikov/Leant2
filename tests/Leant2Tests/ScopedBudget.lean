import Leant2.Engine

/-!
Owned cooperative quotas, transactional rollback, and accepted-stop preservation.
Tests use deterministic counters/injected exceptions and real scoped cancellation
tokens; they do not sleep or rely on wall-time races.
-/

namespace Leant2Tests.ScopedBudget

open Lean Meta Elab Term Leant2

private def observeAll (act : MetaM α) : MetaM (Except Exception α) := do
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try return .ok (← act)
  catch ex => return .error ex

private def context : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def markerName : MetaM Name := do
  return ((← getEnv).asyncPrefix?.getD `Leant2Tests.ScopedBudget) ++
    (← mkFreshUserName `quotaLeak)

private def mark (ctx : SearchCtx) (g : MVarId) (name : Name) : MetaM Unit := do
  g.assign (mkNatLit 7)
  addDecl <| .defnDecl {
    name, levelParams := [], type := mkConst ``Nat, value := mkNatLit 11,
    hints := .abbrev, safety := .safe }
  logInfo "scoped quota: speculative diagnostic"
  ctx.ledger.modify fun l => { l with ruleApplications := l.ruleApplications + 1 }

private def restored (g : MVarId) (name : Name) (messages : Nat) : MetaM Unit := do
  if ← g.isAssigned then throwError "quota leaked a goal assignment"
  if (← getEnv).contains name then throwError "quota leaked a declaration"
  unless (← getThe Core.State).messages.toList.length == messages do
    throwError "quota leaked a diagnostic"

private def sameException (a b : Exception) : Bool :=
  match a, b with
  | .internal a x, .internal b y =>
    a == b && x.getName `leant2.scopedBudget.owner == y.getName `leant2.scopedBudget.owner
  | .error _ a, .error _ b => a.stripNestedTags.kind == b.stripNestedTags.kind
  | _, _ => false

-- Existing false/success control flow, restoration of joint assignments,
-- monotone IO counters, and removal of the reader hook after scope exit.
run_meta do
  for answer in [false, true] do
    withoutModifyingState do
      let ctx ← context
      let exhausted ← IO.mkRef false
      let checks ← IO.mkRef 0
      let g ← mkFreshExprMVar (mkConst ``Nat)
      let sibling ← mkFreshExprMVar (mkConst ``Nat)
      let u ← mkFreshLevelMVar
      let name ← markerName
      let messages := (← getThe Core.State).messages.toList.length
      let continuous : MetaM Bool := do
        checks.modify (· + 1)
        exhausted.get
      let result ← (withScopedBudget continuous fun _ => do
        mark ctx g.mvarId! name
        sibling.mvarId!.assign (mkNatLit 9)
        unless ← isDefEq (mkSort u) (mkSort (.succ .zero)) do
          throwError "failed to set up universe rollback fixture"
        return answer).run ctx
      unless result == answer do throwError "scope changed ordinary Boolean control flow"
      if answer then
        unless (← g.mvarId!.isAssigned) && (← sibling.mvarId!.isAssigned) &&
            (← getEnv).contains name do throwError "successful scope did not commit"
      else
        restored g.mvarId! name messages
        if ← sibling.mvarId!.isAssigned then throwError "scope leaked sibling assignment"
        unless (← instantiateLevelMVars u) == u do throwError "scope leaked universe assignment"
      unless (← ctx.ledger.get).ruleApplications == 1 do throwError "scope refunded work"
      let before ← checks.get
      exhausted.set true
      checkDeadline.run ctx
      unless (← checks.get) == before do throwError "scope hook escaped its reader lifetime"

-- The last admitted callback may checkpoint. Admission counters are not the
-- continuous predicate. A third attempted admission stops without being charged.
run_meta do
  for requestThird in [false, true] do
    withoutModifyingState do
      let ctx ← context
      let admitted ← IO.mkRef 0
      let completed ← IO.mkRef 0
      let result ← (withScopedBudget (pure false) fun stop => do
        let admit : SearchM Unit := do
          checkDeadline
          if (← admitted.get) >= 2 then stop
          admitted.modify (· + 1)
          charge fun l => { l with unifications := l.unifications + 1 }
          checkDeadline
          completed.modify (· + 1)
        admit
        admit
        if requestThird then admit
        return true).run ctx
      unless result == !requestThird do throwError "admission cap changed successful stop"
      unless (← admitted.get) == 2 && (← completed.get) == 2 do
        throwError "last admitted callback was aborted or an extra callback ran"
      unless (← ctx.ledger.get).unifications == 2 do
        throwError "admission rollback refunded or duplicated global work"

-- An owned continuous quota restores before being translated to ordinary false.
run_meta do
  withoutModifyingState do
    let ctx ← context
    let exhausted ← IO.mkRef false
    let g ← mkFreshExprMVar (mkConst ``Nat)
    let name ← markerName
    let messages := (← getThe Core.State).messages.toList.length
    let result ← (withScopedBudget (do exhausted.get) fun _ => do
      mark ctx g.mvarId! name
      exhausted.set true
      checkDeadline
      return true).run ctx
    if result then throwError "owned continuous quota was ignored"
    restored g.mvarId! name messages
    unless (← ctx.ledger.get).ruleApplications == 1 do throwError "quota refunded work"

-- An outer owner must pass through the inner catch. Conversely an inner quota
-- restores only the inner speculation and permits the outer continuation.
run_meta do
  for stopOuter in [false, true] do
    withoutModifyingState do
      let ctx ← context
      let outerG ← mkFreshExprMVar (mkConst ``Nat)
      let innerG ← mkFreshExprMVar (mkConst ``Nat)
      let outerName ← markerName
      let innerName ← markerName
      let messages := (← getThe Core.State).messages.toList.length
      let continued ← IO.mkRef false
      let result ← (withScopedBudget (pure false) fun outerStop => do
        mark ctx outerG.mvarId! outerName
        let innerResult ← withScopedBudget (pure false) fun innerStop => do
          mark ctx innerG.mvarId! innerName
          if stopOuter then outerStop else innerStop
          return true
        if innerResult then throwError "inner quota was ignored"
        if ← innerG.mvarId!.isAssigned then throwError "inner quota returned before restoration"
        if (← getEnv).contains innerName then throwError "inner declaration escaped"
        continued.set true
        return true).run ctx
      unless result == !stopOuter && (← continued.get) == !stopOuter do
        throwError "nested scope consumed a different owner's quota"
      if stopOuter then
        restored outerG.mvarId! outerName messages
        if ← innerG.mvarId!.isAssigned then throwError "outer quota leaked inner assignment"
      else
        unless (← outerG.mvarId!.isAssigned) && (← getEnv).contains outerName do
          throwError "inner quota rolled back the successful outer scope"
      unless (← ctx.ledger.get).ruleApplications == 2 do throwError "nested quota refunded work"

private def heartbeat : Exception :=
  .error .missing (.tagged `runtime.maxHeartbeats m!"scoped heartbeat fixture")

private def recursionDepth : Exception :=
  .error .missing (.tagged `runtime.maxRecDepth m!"scoped recursion fixture")

-- The primitive consumes only its own quota. Ordinary errors are still owned
-- by the caller's alternative; all native/resource/internal identities survive.
run_meta do
  for ex in [Exception.error .missing m!"ordinary scoped failure",
      .internal unsupportedSyntaxExceptionId, .internal deadlineExceptionId,
      .internal graceExceptionId, .internal interruptExceptionId,
      heartbeat, recursionDepth] do
    withoutModifyingState do
      let ctx ← context
      let g ← mkFreshExprMVar (mkConst ``Nat)
      let name ← markerName
      let messages := (← getThe Core.State).messages.toList.length
      let result ← observeAll <| (withScopedBudget (pure false) fun _ => do
        mark ctx g.mvarId! name
        throw ex).run ctx
      match result with
      | .error actual => unless sameException actual ex do throwError "scope changed exception identity"
      | .ok _ => throwError "scope swallowed an unowned exception"
      restored g.mvarId! name messages
      unless (← ctx.ledger.get).ruleApplications == 1 do throwError "exception refunded work"

-- Real interruption/deadline/grace has priority over a simultaneously exhausted
-- local quota, including the owned admission stop path.
run_meta do
  for mode in [0, 1, 2] do
    withoutModifyingState do
      let ctx ← context
      let token ← IO.CancelToken.new
      let exhausted ← IO.mkRef false
      let g ← mkFreshExprMVar (mkConst ``Nat)
      let name ← markerName
      let messages := (← getThe Core.State).messages.toList.length
      let result ← observeAll <| withTheReader Core.Context
          (fun c => { c with cancelTk? := some token }) do
        (withScopedBudget (do exhausted.get) fun stop => do
          mark ctx g.mvarId! name
          exhausted.set true
          if mode == 0 then
            token.set
            stop
          else if mode == 1 then
            withTheReader SearchCtx (fun c => { c with deadline := some 0 }) stop
          else
            ctx.graceDeadline.set (some 0)
            stop
          return true).run ctx
      let expected := if mode == 0 then interruptExceptionId
        else if mode == 1 then deadlineExceptionId else graceExceptionId
      match result with
      | .error (.internal actual _) => unless actual == expected do
          throwError "owned quota took priority over genuine interruption"
      | _ => throwError "genuine interruption was swallowed by the quota"
      restored g.mvarId! name messages

-- Engine.accept records accepted results in IO before returning true. Expiring
-- either an inner or outer heuristic quota must not turn that true into false,
-- because fallback could then collect extra accepted results.
run_meta do
  withoutModifyingState do
    let ctx ← context
    let accepted ← IO.mkRef 0
    let fallback ← IO.mkRef false
    let exhausted ← IO.mkRef false
    let g ← mkFreshExprMVar (mkConst ``Nat)
    let name ← markerName
    let result ← (withScopedBudget (do exhausted.get) fun _ =>
      withScopedBudget (do exhausted.get) fun _ => do
        mark ctx g.mvarId! name
        accepted.modify (· + 1)
        exhausted.set true
        return true).run ctx
    unless result do
      fallback.set true
      accepted.modify (· + 1)
    unless result && (← accepted.get) == 1 && !(← fallback.get) do
      throwError "post-success quota erased the accepted-result stop request"
    unless (← g.mvarId!.isAssigned) && (← getEnv).contains name do
      throwError "successful accepted-result state did not commit"

-- Successful-stop protection does not suppress real native cancellation. The
-- external accepted marker remains, but speculative Meta/Core state restores.
run_meta do
  withoutModifyingState do
    let ctx ← context
    let accepted ← IO.mkRef 0
    let token ← IO.CancelToken.new
    let exhausted ← IO.mkRef false
    let g ← mkFreshExprMVar (mkConst ``Nat)
    let name ← markerName
    let messages := (← getThe Core.State).messages.toList.length
    let result ← observeAll <| withTheReader Core.Context
        (fun c => { c with cancelTk? := some token }) do
      (withScopedBudget (do exhausted.get) fun _ => do
        mark ctx g.mvarId! name
        accepted.modify (· + 1)
        exhausted.set true
        token.set
        return true).run ctx
    match result with
    | .error ex => unless ex.isInterrupt do throwError "true exit changed native cancellation"
    | .ok _ => throwError "true exit bypassed genuine cancellation"
    restored g.mvarId! name messages
    unless (← accepted.get) == 1 do throwError "test wrongly expected external result rollback"

-- Account for completed callbacks plus work in a callback that has not returned.
-- The finalizer records partial work once even when an owned quota unwinds it.
run_meta do
  withoutModifyingState do
    let ctx ← context
    let completedWork ← IO.mkRef 0
    let activeStart ← IO.mkRef (none : Option Nat)
    let continuous : MetaM Bool := do
      let active ← match ← activeStart.get with
        | none => pure 0
        | some start => pure ((← ctx.ledger.get).ruleApplications - start)
      return (← completedWork.get) + active >= 3
    let callback : SearchM Unit := do
      let start := (← ctx.ledger.get).ruleApplications
      activeStart.set (some start)
      try
        for _ in [:2] do
          charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
          checkDeadline
      finally
        let delta := (← ctx.ledger.get).ruleApplications - start
        completedWork.modify (· + delta)
        activeStart.set none
    let result ← (withScopedBudget continuous fun _ => do
      callback
      callback
      return true).run ctx
    if result then throwError "active continuation work escaped the quota"
    unless (← completedWork.get) == 3 && (← activeStart.get).isNone &&
        (← ctx.ledger.get).ruleApplications == 3 do
      throwError "continuation accounting omitted, refunded, or duplicated partial work"

-- Capture a private quota only to verify its lane boundary behavior. This is
-- adversarial test instrumentation; production callers never export the stop.
private def capturedQuota : MetaM Exception := do
  let ctx ← context
  let captured ← IO.mkRef (none : Option Exception)
  discard <| (withScopedBudget (pure false) fun stop => do
    let result ← observeAll (stop.run (← read))
    match result with
    | .error ex => captured.set (some ex)
    | .ok _ => throwError "owned stop returned"
    return false).run ctx
  let some ex ← captured.get | throwError "no captured quota"
  return ex

run_meta do
  withoutModifyingState do
    let quota ← capturedQuota
    unless (searchStop? quota).isNone do throwError "private quota became a public lane stop"
    -- Same registered ID is insufficient: another scope's token, an absent
    -- token, and an explicitly different payload must all retain identity.
    let .internal id _ := quota | throwError "quota was not an internal exception"
    let wrongPayload := ({} : KVMap).setName `leant2.scopedBudget.owner `notThisOwner
    for unowned in [quota, Exception.internal id {}, .internal id wrongPayload] do
      let probeCtx ← context
      let result ← observeAll <| (withScopedBudget (pure false) fun _ => throw unowned).run probeCtx
      match result with
      | .error actual => unless sameException actual unowned do
          throwError "scope altered a quota payload it did not own"
      | .ok _ => throwError "scope consumed the quota ID without matching its owner"
    let ctx ← context
    let timedOut ← IO.mkRef false
    let g ← mkFreshExprMVar (mkConst ``Nat)
    let name ← markerName
    let messages := (← getThe Core.State).messages.toList.length
    let result ← observeAll <| withLane ctx.ledger ctx.refutedPrograms ctx.graceDeadline
      timedOut 1000000 (fun _ => do mark ctx g.mvarId! name; throw quota)
    match result with
    | .error actual => unless sameException actual quota do throwError "lane changed escaped owner"
    | .ok _ => throwError "lane consumed an escaped private quota"
    if ← timedOut.get then throwError "escaped private quota marked lane timed out"
    restored g.mvarId! name messages

end Leant2Tests.ScopedBudget
