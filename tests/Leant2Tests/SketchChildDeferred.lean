import Leant2.Frontend.Sketch.ChildProjection

/-! Replay ordering, refusal and exact restoration checks. Test-only elaborators
name the two private adapters without exposing a production override. -/
namespace Leant2.Frontend.Sketch.ChildProjection.DeferredTests
open Lean Meta Elab
open Lean.Elab.Term hiding mkConst

private def privateAdapter (name : Name) : TermElabM Expr := do
  let name := mkPrivateNameCore `Leant2.Frontend.Sketch.ChildProjection
    (`Leant2.Frontend.Sketch.ChildProjection ++ name)
  discard <| getConstInfo name
  mkConstWithFreshMVarLevels name

elab "eagerReplayForTest" : term => privateAdapter `withPartialViewWithReplay
elab "deferredReplayForTest" : term => privateAdapter `tryObservePartialWithReplay?

structure Snapshot where
  coreState : Core.State
  metaState : Meta.State
  termState : Term.State

private def snapshot : TermElabM Snapshot := do
  return {
    coreState := ← getThe Core.State
    metaState := ← getThe Meta.State
    termState := ← getThe Term.State }

private unsafe def assertRestored (before : Snapshot) : TermElabM Unit := do
  let after ← snapshot
  unless ptrEq before.coreState after.coreState && ptrEq before.metaState after.metaState &&
      ptrEq before.termState after.termState do
    throwError "deferred fixture: exact Core/Meta/Term state was not restored"

private def catchAll (action : TermElabM α) : TermElabM (Except Exception α) := do
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch exception => return .error exception

private def pass (name : String) : TermElabM Unit := IO.println s!"PASS {name}"

private def owned (prepared : Prepared) (name : Name) : MetaM OwnedHole := do
  let some hole := prepared.holes.find? (·.spec.sourceName.eraseMacroScopes == name)
    | throwError "deferred fixture: missing owned hole {name}"
  return hole

private def term (stx : Syntax) : TermElabM Expr := do
  let value ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

private def recording (calls : IO.Ref (Array (Expr × Expr))) (value type : Expr) : MetaM Unit := do
  calls.modify (·.push (value, type))
  replay value type

private unsafe def counterFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let contract ← term (← `(fun pair : Nat × Nat => pair.1 = 0))
  let observations ← mkObservations contract target
  let stuckContract ← term (← `(fun pair : Nat × Nat => pair.1 = 1))
  let stuckObservations ← mkObservations stuckContract target
  let trueContract ← term (← `(fun _pair : Nat × Nat => True))
  let trueObservations ← mkObservations trueContract target
  let outer ← snapshot
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← build prepared
    let left ← owned prepared `left
    let right ← owned prepared `right
    let child ← left.pending.withContext do mkFreshExprMVar (mkConst ``Nat) .natural
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
    typedAssign right.pending (mkNatLit 2)
    let branch ← snapshot
    let eager ← IO.mkRef (#[] : Array (Expr × Expr))
    eagerReplayForTest (recording eager) state left.pending fun view => do
      -- Completed right + left/child nodes + final composed program.
      unless (← eager.get).size == 4 do throwError "deferred fixture: eager callback saw missing replays"
      unless view.childInterfaces.size == 1 do throwError "deferred fixture: wrong frontier"
    assertRestored branch
    pass "eager-callback-follows-all-four-native-replays"
    for (predicate, parts) in [(stuckContract, stuckObservations), (trueContract, trueObservations)] do
      let calls ← IO.mkRef (#[] : Array (Expr × Expr))
      let result ← deferredReplayForTest (recording calls) state left.pending
        .strictConstructive predicate parts
      unless result.isNone && (← calls.get).isEmpty do
        throwError "deferred fixture: inconclusive observation replayed or exposed a report"
      assertRestored branch
    pass "stuck-and-satisfied-return-none-with-zero-replays"
    let deferred ← IO.mkRef (#[] : Array (Expr × Expr))
    let result ← deferredReplayForTest (recording deferred) state left.pending
      .strictConstructive contract observations
    unless result.any (·.refuted) do throwError "deferred fixture: actual false was lost"
    let actual ← deferred.get
    unless actual.size == 7 && actual.extract 0 4 == (← eager.get) do
      throwError "deferred fixture: false did not discharge the exact eager obligation sequence"
    assertRestored branch
    pass "false-replays-three-evidence-schemas-and-every-exact-native-obligation"
    let publicResult ← tryObservePartial? state left.pending .strictConstructive contract observations
    unless publicResult.any (·.refuted) do throwError "deferred fixture: public adapter lost false"
    assertRestored branch
    pass "public-observer-returns-only-fully-replayed-refutation"
    -- Fail every construction/evidence obligation so no missing final
    -- validation can silently expose refuted.
    for failAt in [1, 2, 3, 4, 5, 6, 7] do
      let count ← IO.mkRef (0 : Nat)
      let injected (value type : Expr) : MetaM Unit := do
        count.modify (· + 1)
        if (← count.get) == failAt then
          discard <| mkFreshExprMVar (mkConst ``Nat)
          discard <| mkFreshLevelMVar
          logInfo "speculative deferred replay failure"
          throwError "injected independent replay refusal"
        replay value type
      let result ← deferredReplayForTest injected state left.pending
        .strictConstructive contract observations
      unless result.isNone && (← count.get) == failAt do
        throwError "deferred fixture: failed independent obligation was skipped"
      assertRestored branch
    pass "every-deferred-obligation-failure-refuses-and-restores"
  assertRestored outer

unsafe def unsafeNat : Nat := 0
axiom forbiddenNat : Nat
axiom forbiddenFalse : False

private unsafe def eagerFailureFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← build prepared
    let left ← owned prepared `left
    let right ← owned prepared `right
    let child ← left.pending.withContext do mkFreshExprMVar (mkConst ``Nat) .natural
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
    typedAssign right.pending (mkConst ``unsafeNat)
    let branch ← snapshot
    let reached ← IO.mkRef false
    let result ← tryPartialView state left.pending fun _ => reached.set true
    unless result.isNone && !(← reached.get) do
      throwError "deferred fixture: eager public callback received a kernel-unsafe view"
    assertRestored branch
  pass "eager-public-callback-blocked-by-real-kernel-unsafe-completion"

private unsafe def deniedFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let contract ← term (← `(fun pair : Nat × Nat => pair.1 = 0))
  let observations ← mkObservations contract target
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← build prepared
    let left ← owned prepared `left
    let fn ← left.pending.withContext do
      mkFreshExprMVar (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) .natural
    let child ← left.pending.withContext do mkFreshExprMVar (mkConst ``Nat) .natural
    typedAssign left.pending (mkApp (mkConst ``Nat.succ)
      (mkApp2 (mkConst ``Nat.add) (mkApp fn (mkConst ``forbiddenNat)) child))
    typedAssign fn.mvarId! (mkLambda `ignored .default (mkConst ``Nat) (mkNatLit 0))
    let branch ← snapshot
    for profile in [.strictConstructive, .standard, .projectRelative [``forbiddenNat], .strictConstructive] do
      let calls ← IO.mkRef (#[] : Array (Expr × Expr))
      let result ← deferredReplayForTest (recording calls) state left.pending profile contract observations
      let allowed := profile.allowedAxioms.contains ``forbiddenNat
      unless result.any (·.refuted) == allowed do
        throwError "deferred fixture: erased raw dependency policy changed"
      unless (← calls.get).isEmpty == !allowed do
        throwError "deferred fixture: original anchored policy refusal performed replay"
      assertRestored branch
  pass "raw-erased-dependency-denied-without-replay-and-reauthorized-per-call"

private unsafe def observationDeniedFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let contract ← term (← `(fun pair : Nat × Nat => pair.1 = pair.1))
  let decider ← term (← `(fun pair : Nat × Nat =>
    (Decidable.isFalse (fun _ => forbiddenFalse) : Decidable (pair.1 = pair.1))))
  let observations := #[{ predicate := contract, decider := some decider : Observation }]
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← build prepared
    let left ← owned prepared `left
    let child ← left.pending.withContext do mkFreshExprMVar (mkConst ``Nat) .natural
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
    let branch ← snapshot
    let calls ← IO.mkRef (#[] : Array (Expr × Expr))
    let result ← deferredReplayForTest (recording calls) state left.pending
      .strictConstructive contract observations
    unless result.isNone && (← calls.get).isEmpty do
      throwError "deferred fixture: decider-only policy refusal performed independent replay"
    assertRestored branch
    -- The constant is only in the supplied decider. In particular neither
    -- graph anchors nor the original contract can short-circuit this case.
    withPartialView state left.pending fun view => do
      unless !(view.auditConstants.any (·.isConstOf ``forbiddenFalse)) &&
          !contract.getUsedConstants.contains ``forbiddenFalse do
        throwError "deferred fixture: bad evidence unexpectedly entered original/graph policy"
      let (raw, _) ← evalObservations observations view.program #[] instantiateMVars
      unless raw.refuted do throwError "deferred fixture: supplied bad decider did not reduce false"
    assertRestored branch
  pass "decider-only-policy-refusal-performs-zero-independent-replays"

private unsafe def exceptionFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let contract ← term (← `(fun pair : Nat × Nat => pair.1 = 0))
  let observations ← mkObservations contract target
  let unknown ← registerInternalExceptionId `deferredReplayUnknown
  for mode in [0, 1, 2] do
    discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
      let state ← build prepared
      let left ← owned prepared `left
      let child ← left.pending.withContext do mkFreshExprMVar (mkConst ``Nat) .natural
      typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
      let token ← IO.CancelToken.new
      let calls ← IO.mkRef (0 : Nat)
      let branch ← snapshot
      let injected (value type : Expr) : MetaM Unit := do
        calls.modify (· + 1)
        if (← calls.get) == 4 then
          discard <| mkFreshExprMVar (mkConst ``Nat)
          discard <| mkFreshLevelMVar
          logInfo "speculative deferred interruption"
          match mode with
          | 0 => throw (.internal unknown)
          | 1 => token.set; Core.checkInterrupted
          | _ => Core.throwMaxHeartbeat `deferredChild `maxHeartbeats 1
        replay value type
      let result ← catchAll <| withTheReader Core.Context
          (fun context => { context with cancelTk? := some token }) do
        deferredReplayForTest injected state left.pending .strictConstructive contract observations
      assertRestored branch
      unless (← calls.get) == 4 do throwError "deferred fixture: did not reach obligation injection"
      match mode, result with
      | 0, .error (.internal id _) => unless id == unknown do throwError "deferred fixture: internal ID changed"
      | 1, .error exception => unless exception.isInterrupt do throwError "deferred fixture: cancellation changed"
      | 2, .error exception => unless exception.isMaxHeartbeat do throwError "deferred fixture: resource failure changed"
      | _, _ => throwError "deferred fixture: exceptional replay became an ordinary result"
      unless !(← child.mvarId!.isAssigned) do throwError "deferred fixture: opaque child assignment escaped"
    pass s!"deferred-exception-identity-and-restoration-{mode}"

run_elab do counterFixture
run_elab do eagerFailureFixture
run_elab do deniedFixture
run_elab do observationDeniedFixture
run_elab do exceptionFixture
run_elab do IO.println "DEFERRED CHILD MATRIX COMPLETE"

end Leant2.Frontend.Sketch.ChildProjection.DeferredTests
