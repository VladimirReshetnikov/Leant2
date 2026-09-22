import Leant2.Frontend.Sketch.ChildProjection

/-! Native descendant-selection regressions for exact identity, conservative
admission, and state restoration. These do not establish synthesis success
or a performance improvement. -/
namespace Leant2Tests.SketchChildSelection
open Lean Meta Elab
open Lean.Elab.Term hiding mkConst
open Leant2 Leant2.Frontend.Sketch ChildProjection

private structure Snapshot where
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
    throwError "selector fixture: exact Core/Meta/Term state was not restored"

private def restore (before : Snapshot) : TermElabM Unit := do
  modifyThe Meta.State fun _ => before.metaState
  modifyThe Core.State fun _ => before.coreState
  modifyThe Term.State fun _ => before.termState

private def catchAll (action : TermElabM α) : TermElabM (Except Exception α) := do
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch exception => return .error exception

private def pass (name : String) : TermElabM Unit := IO.println s!"PASS {name}"

private def owned (prepared : Prepared) (name : Name) : MetaM OwnedHole := do
  let some hole := prepared.holes.find? (·.spec.sourceName.eraseMacroScopes == name)
    | throwError "selector fixture: missing owned hole {name}"
  return hole

private def natChild (parent : MVarId) (kind : MetavarKind := .syntheticOpaque) : MetaM Expr :=
  parent.withContext do mkFreshExprMVar (mkConst ``Nat) kind

private unsafe def expectSelection (state : ChildProjection.State) (child : MVarId)
    (expected : Option MVarId) : TermElabM Unit := do
  let before ← snapshot
  let actual ← ChildProjection.selectAncestor? state child
  assertRestored before
  unless actual == expected do
    throwError "selector fixture: wrong ancestor identity"

private unsafe def nativeApplicationFixture : TermElabM Unit := do
  -- Fin (Nat.succ 0) deliberately puts a fixed application in an introduced
  -- binder's type. It must not make an otherwise intro-only body productive.
  let target ← elabType (← `(((next : Nat → Nat) → Fin (Nat.succ 0) → Nat) × Nat))
  let before ← snapshot
  discard <| withPreparedSketch target
      (← `(term| ((?function : (next : Nat → Nat) → Fin (Nat.succ 0) → Nat),
        (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let function ← owned prepared `function
    let (next, body1) ← function.pending.intro1P
    let (_, body2) ← body1.intro1P
    expectSelection state body2 none
    pass "selector-native-intro-only-is-suppressed"
    -- Native apply creates the real argument obligation and stores next ?child
    -- in the assignment graph. No prefilled final function is supplied.
    let children ← body2.apply (mkFVar next)
    let [child] := children | throwError "selector fixture: native apply did not create one child"
    unless (← child.getDecl).kind.isNatural do
      throwError "selector fixture: native apply child is not natural"
    expectSelection state child (some function.pending)
    unless !(← child.isAssigned) && !(← child.isDelayedAssigned) do
      throwError "selector fixture: selection completed the native child"
    pass "selector-local-application-selects-original-root"
    let detached ← natChild child
    unless detached.mvarId! != child && (← detached.mvarId!.getType) == (← child.getType) do
      throwError "selector fixture: detached identity control is not a distinct same-type child"
    expectSelection state detached.mvarId! none
    pass "selector-detached-same-type-child-is-refused"
  assertRestored before

private unsafe def sharedAncestorFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let right ← owned prepared `right
    unless prepared.holes.map (·.pending) == #[left.pending, right.pending] do
      throwError "selector fixture: original root order does not match the source"
    let child ← natChild left.pending
    let initial ← snapshot
    typedAssign left.pending child
    typedAssign right.pending (mkApp (mkConst ``Nat.succ) child)
    expectSelection state child.mvarId! (some right.pending)
    pass "selector-shared-child-selects-productive-later-root"
    restore initial
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
    typedAssign right.pending (mkApp (mkConst ``Nat.succ) child)
    expectSelection state child.mvarId! (some left.pending)
    pass "selector-shared-child-keeps-stable-original-order"

private unsafe def branchFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let first ← natChild left.pending
    let second ← natChild left.pending
    let initial ← snapshot
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) first)
    expectSelection state first.mvarId! (some left.pending)
    expectSelection state second.mvarId! none
    restore initial
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) second)
    expectSelection state first.mvarId! none
    expectSelection state second.mvarId! (some left.pending)
  pass "selector-branch-restoration-discards-old-child"

private unsafe def refusalFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  -- Genuine membership in the captured context, not a forged user name/tag.
  for kind in [MetavarKind.natural, MetavarKind.syntheticOpaque] do
    discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
      let left ← owned prepared `left
      let earlier ← natChild left.pending kind
      let state ← ChildProjection.build prepared
      unless state.beforeSearch.decls.contains earlier.mvarId! do
        throwError "selector fixture: earlier child is not in the pre-search context"
      typedAssign left.pending (mkApp (mkConst ``Nat.succ) earlier)
      expectSelection state earlier.mvarId! none
      expectSelection state left.pending none
  pass "selector-presearch-child-is-refused"
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let child ← natChild left.pending
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
    typedAssign child.mvarId! (mkNatLit 0)
    unless ← child.mvarId!.isAssigned do throwError "selector fixture: regular assignment is absent"
    expectSelection state child.mvarId! none
  pass "selector-assigned-child-is-refused"
  let functionTarget ← elabType (← `((Nat → Nat) × Nat))
  discard <| withPreparedSketch functionTarget
      (← `(term| ((?function : Nat → Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let function ← owned prepared `function
    let nat := mkConst ``Nat
    -- Construct an exact native delayed abstraction edge: the pending goal has
    -- the binder in its context; the wrapper has the closed function type.
    let wrapper ← withLocalDeclD `delayedArgument nat fun argument => do
      let pending ← mkFreshExprMVar nat .syntheticOpaque
      withLCtx {} #[] do
        let wrapper ← mkFreshExprMVar (← mkArrow nat nat) .syntheticOpaque
        assignDelayedMVar wrapper.mvarId! #[argument] pending.mvarId!
        return wrapper
    typedAssign function.pending wrapper
    unless !(← wrapper.mvarId!.isAssigned) && (← wrapper.mvarId!.isDelayedAssigned) do
      throwError "selector fixture: delayed assignment was normalized away"
    expectSelection state wrapper.mvarId! none
  pass "selector-delayed-assigned-child-is-refused"
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let original ← getMCtx
    -- Retain a genuinely deeper-created declaration at the original current
    -- depth solely to exercise the foreign-goal refusal. It is not assigned to
    -- an original program hole and is discarded with the prepared callback.
    modifyMCtx fun current => current.incDepth
    let foreign ← natChild left.pending
    modifyMCtx fun current => { current with
      depth := original.depth, levelAssignDepth := original.levelAssignDepth }
    unless (← foreign.mvarId!.getDecl).depth == prepared.depth + 1 do
      throwError "selector fixture: foreign declaration was not created at a deeper depth"
    expectSelection state foreign.mvarId! none
  pass "selector-foreign-depth-child-is-refused"
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let synthetic ← natChild left.pending .synthetic
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) synthetic)
    let .synthetic := (← synthetic.mvarId!.getDecl).kind
      | throwError "selector fixture: synthetic control changed kind"
    unless !(← synthetic.mvarId!.isAssigned) && !(← synthetic.mvarId!.isDelayedAssigned) do
      throwError "selector fixture: synthetic control became assigned"
    let some parentBody ← getExprMVarAssignment? left.pending
      | throwError "selector fixture: synthetic control has no parent assignment"
    unless parentBody == mkApp (mkConst ``Nat.succ) synthetic do
      throwError "selector fixture: synthetic child disappeared from the raw parent assignment"
    expectSelection state synthetic.mvarId! none
  pass "selector-synthetic-child-is-refused"

private unsafe def quotaFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  for syntaxQuota in [false, true] do
    discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
      let state ← ChildProjection.build prepared
      let left ← owned prepared `left
      let child ← natChild left.pending
      typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
      let calls ← IO.mkRef 0
      let check : MetaM Unit := do
        calls.modify (· + 1)
        discard <| mkFreshExprMVar (mkConst ``Nat)
        discard <| mkFreshLevelMVar
        logInfo "selector quota speculative diagnostic"
      let limits : ChildProjection.Limits := if syntaxQuota then { syntaxNodes := 0 } else { nodes := 0 }
      let before ← snapshot
      let result ← catchAll <| ChildProjection.selectAncestor? state child.mvarId! check limits
      assertRestored before
      unless (← calls.get) > 0 do throwError "selector fixture: quota check was not reached"
      let expected := if syntaxQuota then "child projection: selection syntax quota"
        else "child projection: selection graph quota"
      let .error (.error _ message) := result
        | throwError "selector fixture: admission quota did not retain an ordinary error"
      unless (← message.toString) == expected do
        throwError "selector fixture: admission quota error changed"
      unless !(← child.mvarId!.isAssigned) do throwError "selector fixture: quota completed a child"
    pass (if syntaxQuota then "selector-syntax-quota-restores-state" else "selector-node-quota-restores-state")

private unsafe def exitFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let unknown ← registerInternalExceptionId `childSelectionUnknown
  for mode in [0, 1, 2, 3, 4, 5] do
    discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
      let state ← ChildProjection.build prepared
      let left ← owned prepared `left
      let child ← natChild left.pending
      typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
      let token ← IO.CancelToken.new
      let calls ← IO.mkRef 0
      let check : MetaM Unit := do
        calls.modify (· + 1)
        discard <| mkFreshExprMVar (mkConst ``Nat)
        discard <| mkFreshLevelMVar
        logInfo "selector exit speculative diagnostic"
        -- Reach actual traversal before injecting, rather than testing only
        -- the selector's first entry check. IO counts cannot be rolled back.
        if (← calls.get) == 3 then
          match mode with
          | 0 => pure ()
          | 1 => throwError "selector injected ordinary failure"
          | 2 => throw (.internal unknown)
          | 3 => token.set; Core.checkInterrupted
          | 4 => Core.throwMaxHeartbeat `childSelection `maxHeartbeats 1
          | _ => throwMaxRecDepthAt Syntax.missing
      let before ← snapshot
      let result ← catchAll <| withTheReader Core.Context
          (fun context => { context with cancelTk? := some token }) do
        ChildProjection.selectAncestor? state child.mvarId! check
      assertRestored before
      unless (← calls.get) ≥ 3 do throwError "selector fixture: exit injection did not reach traversal"
      match mode, result with
      | 0, .ok (some ancestor) =>
        unless ancestor == left.pending do throwError "selector fixture: successful identity changed"
      | 1, .error (.error _ message) =>
        unless (← message.toString) == "selector injected ordinary failure" do
          throwError "selector fixture: ordinary exception identity changed"
      | 2, .error (.internal id _) =>
        unless id == unknown do throwError "selector fixture: internal exception identity changed"
      | 3, .error exception =>
        unless exception.isInterrupt do throwError "selector fixture: cancellation was consumed"
      | 4, .error exception =>
        unless exception.isMaxHeartbeat do throwError "selector fixture: heartbeat identity changed"
      | 5, .error exception =>
        unless exception.isMaxRecDepth do throwError "selector fixture: recursion identity changed"
      | _, _ => throwError "selector fixture: unexpected exit result"
      unless !(← child.mvarId!.isAssigned) do throwError "selector fixture: exit completed a child"
    pass s!"selector-all-exit-restoration-{mode}"

run_elab do nativeApplicationFixture
run_elab do sharedAncestorFixture
run_elab do branchFixture
run_elab do refusalFixture
run_elab do quotaFixture
run_elab do exitFixture
run_elab do IO.println "CHILD SELECTION MATRIX COMPLETE"

end Leant2Tests.SketchChildSelection
