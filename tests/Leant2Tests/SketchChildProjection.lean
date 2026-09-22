import Leant2.Frontend.Sketch.ChildProjection

namespace Leant2Tests.SketchChildProjection
open Lean Meta Elab
open Lean.Elab.Term hiding mkConst
open Leant2 Leant2.Frontend.Sketch ChildProjection

structure Snapshot where
  coreState : Core.State
  metaState : Meta.State
  termState : Term.State

private def snapshot : TermElabM Snapshot := do
  return { coreState := ← getThe Core.State, metaState := ← getThe Meta.State, termState := ← getThe Term.State }

private unsafe def assertRestored (before : Snapshot) : TermElabM Unit := do
  let after ← snapshot
  unless ptrEq before.coreState after.coreState && ptrEq before.metaState after.metaState &&
      ptrEq before.termState after.termState do
    throwError "fixture: exact Core/Meta/Term state was not restored"

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
    | throwError "fixture: missing owned hole {name}"
  return hole

private def localNamed (name : Name) : MetaM Expr := do
  for entry in (← getLCtx) do
    if entry.userName.eraseMacroScopes == name then return entry.toExpr
  throwError "fixture: missing local {name}"

private def term (stx : Syntax) : TermElabM Expr := do
  let result ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars result

private def natChild (parent : MVarId) : MetaM Expr := parent.withContext do
  mkFreshExprMVar (mkConst ``Nat) .syntheticOpaque

private unsafe def prefixFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let contract ← term (← `(fun pair : Nat × Nat => pair.1 = 0 ∧ pair.2 = 2))
  let observations ← mkObservations contract target
  let before ← snapshot
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let initial ← snapshot
    let state ← ChildProjection.build prepared
    assertRestored initial
    let left ← owned prepared `left
    let right ← owned prepared `right
    let child ← natChild left.pending
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
    let branch ← snapshot
    let baseline ← Projection.observe state.base .strictConstructive contract observations
    unless baseline.statuses == #[some .stuck, some .stuck] do
      throwError "fixture: baseline no longer hides the unfinished owned hole"
    assertRestored branch
    let result ← ChildProjection.observe state left.pending .strictConstructive contract observations
    unless result.enhanced && result.report.statuses == #[some .refuted, none] do
      throwError "fixture: wrong successor prefix did not refute: {result.enhanced}, {repr result.report.statuses}"
    assertRestored branch
    unless !(← child.mvarId!.isAssigned) && !(← right.pending.isAssigned) do
      throwError "fixture: observation completed pending children"
    pass "wrong-prefix-refutes-before-child-completion"
    let projected ← withPartialView state left.pending fun view => do
      let some only := view.childInterfaces[0]? | throwError "fixture: missing child interface"
      unless view.childInterfaces.size == 1 && only.id == child.mvarId! do
        throwError "fixture: wrong child inventory"
      mkLambdaFVars view.parameters view.program (usedOnly := false)
    assertRestored branch
    for n in [0, 7] do
      restore branch
      typedAssign child.mvarId! (mkNatLit n)
      typedAssign right.pending (mkNatLit 2)
      let native ← instantiateMVars prepared.expression
      let expected := mkAppN projected #[mkNatLit 99, mkNatLit 2, mkNatLit n]
      replay native prepared.expected
      replay expected prepared.expected
      unless ← isDefEq native expected do throwError "fixture: completion/native correspondence failed"
    pass "two-completions-agree-with-parametric-native-view"
    restore initial
    -- A correct completed left hole retains ordinary whole-hole behavior.
    typedAssign left.pending (mkNatLit 0)
    let correct ← snapshot
    let result ← ChildProjection.observe state left.pending .strictConstructive contract observations
    unless !result.enhanced && result.report.statuses == #[some .satisfied, some .stuck] do
      throwError "fixture: correct completed prefix lost fallback"
    assertRestored correct
    pass "correct-completed-prefix-retains-stuck-sibling"
  assertRestored before
  pass "prepared-prefix-fixture-restores-all-state"

private unsafe def delayedFixture : TermElabM Unit := do
  let target ← elabType (← `((Nat → Nat) × Nat))
  let contract ← term (← `(fun pair : (Nat → Nat) × Nat => pair.1 0 = 0))
  let observations ← mkObservations contract target
  discard <| withPreparedSketch target (← `(term| ((?function : Nat → Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let function ← owned prepared `function
    let right ← owned prepared `right
    let (_, body) ← function.pending.intro1P
    let child ← natChild body
    typedAssign body (mkApp (mkConst ``Nat.succ) child)
    let branch ← snapshot
    withPartialView state function.pending (fun _ => pure ())
    assertRestored branch
    let result ← ChildProjection.observe state function.pending .strictConstructive contract observations
    unless result.enhanced && result.report.refuted do
      throwError "fixture: native introduction/delayed partial closure stayed opaque"
    assertRestored branch
    let projected ← withPartialView state function.pending fun view =>
      mkLambdaFVars view.parameters view.program (usedOnly := false)
    child.mvarId!.withContext do
      let args := (← getLCtx).getFVars
      unless args.size == 1 do throwError "fixture: introduced child has wrong local context"
      typedAssign child.mvarId! args[0]!
    typedAssign right.pending (mkNatLit 0)
    let identity := mkLambda `x .default (mkConst ``Nat) (.bvar 0)
    let expected := mkAppN projected #[identity, mkNatLit 0, identity]
    let native ← instantiateMVars prepared.expression
    replay expected prepared.expected
    replay native prepared.expected
    unless ← isDefEq expected native do throwError "fixture: delayed native correspondence failed"
  pass "native-intro-child-closure-and-correspondence"

axiom forbiddenNat : Nat

private unsafe def erasedDependencyFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let contract ← term (← `(fun pair : Nat × Nat => pair.1 = 0))
  let observations ← mkObservations contract target
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let fn ← left.pending.withContext do
      mkFreshExprMVar (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) .syntheticOpaque
    let child ← natChild left.pending
    let erased := mkApp fn (mkConst ``forbiddenNat)
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) (mkApp2 (mkConst ``Nat.add) erased child))
    typedAssign fn.mvarId! (mkLambda `ignored .default (mkConst ``Nat) (mkNatLit 0))
    let some rawParent ← getExprMVarAssignment? left.pending | throwError "fixture: missing raw parent"
    unless rawParent.getUsedConstants.contains ``forbiddenNat do
      throwError "fixture: assignment had already erased the dependency before the probe"
    let branch ← snapshot
    let actualErasure ← isolated do
      let value ← instantiateMVars (mkMVar left.pending)
      return !value.getUsedConstants.contains ``forbiddenNat
    unless actualErasure do throwError "fixture: native instantiation did not erase the intended dependency"
    assertRestored branch
    withPartialView state left.pending fun view => do
      unless view.auditConstants.any (·.isConstOf ``forbiddenNat) do
        throwError "fixture: pre-instantiation dependency inventory lost forbidden body"
      unless !view.program.getUsedConstants.contains ``forbiddenNat do
        throwError "fixture: forbidden dependency was not erased from visible partial view"
      let (raw, _) ← evalObservations observations view.program #[] instantiateMVars Core.checkInterrupted
      unless raw.refuted do throwError "fixture: erased-dependency observation is not actually false"
    assertRestored branch
    for profile in [.strictConstructive, .standard, .projectRelative [``forbiddenNat], .strictConstructive] do
      let result ← ChildProjection.observe state left.pending profile contract observations
      let allow := profile.allowedAxioms.contains ``forbiddenNat
      unless result.enhanced && result.report.statuses == #[some (if allow then .refuted else .stuck)] do
        throwError "fixture: unused child dependency profile mismatch {repr result.report.statuses}"
      assertRestored branch
  pass "raw-unused-child-dependency-survives-native-beta-erasure"

private unsafe def unsupportedFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let contract ← term (← `(fun pair : Nat × Nat => pair.1 = 0))
  let observations ← mkObservations contract target
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let left ← owned prepared `left
    let caller ← natChild left.pending
    let state ← ChildProjection.build prepared
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) caller)
    let branch ← snapshot
    let result ← ChildProjection.observe state left.pending .strictConstructive contract observations
    unless !result.enhanced && result.report.statuses == #[some .stuck] do
      throwError "fixture: pre-search caller hole was captured"
    assertRestored branch
  pass "pre-search-leaf-refused-and-kept-opaque"
  discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let child ← natChild left.pending
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
    let branch ← snapshot
    let result ← ChildProjection.observe state left.pending .strictConstructive contract observations
      Core.checkInterrupted { nodes := 1 }
    unless !result.enhanced && result.report.statuses == #[some .stuck] do
      throwError "fixture: bounded unsupported frontier was not opaque"
    assertRestored branch
  pass "admission-limit-preserves-opaque-fallback"

private unsafe def asymmetricFixture : TermElabM Unit := do
  let target ← elabType (← `((n : Nat) →
    (Nat × Fin (n+1)) × ((m : Nat) → Fin (n+1) → Fin (m+1))))
  let target ← instantiateMVars target
  let contract ← term (← `(fun f : ((n : Nat) →
      (Nat × Fin (n+1)) × ((m : Nat) → Fin (n+1) → Fin (m+1))) =>
    (f 2).1.1 = 0 ∧ ((f 2).2 3 (Fin.last 2)).val = 3))
  let observations ← mkObservations contract target
  discard <| withPreparedSketch target (← `(fun (n : Nat) =>
      ((?left : Nat × Fin (n+1)), fun (m : Nat) (foreign : Fin (n+1)) => (?right : Fin (m+1))))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let right ← owned prepared `right
    let child ← left.pending.withContext do
      let n ← localNamed `n
      let type := mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) n)
      let child ← mkFreshExprMVar type .syntheticOpaque
      typedAssign left.pending (← mkAppM ``Prod.mk #[mkNatLit 1, child])
      return child
    let branch ← snapshot
    isolated <| right.pending.withContext do
      let foreign ← localNamed `foreign
      unless ← isDefEq (← inferType foreign) (← child.mvarId!.getType) do
        throwError "fixture: asymmetric foreign control has a different type"
      if ← child.mvarId!.checkedAssign foreign then throwError "fixture: same-type foreign variable captured"
    assertRestored branch
    let result ← ChildProjection.observe state left.pending .strictConstructive contract observations
    unless result.enhanced && result.report.refuted do
      throwError "fixture: dependent partial constructor did not refute"
    assertRestored branch
    withPartialView state left.pending fun view => do
      let some only := view.childInterfaces[0]? | throwError "fixture: missing child interface"
      unless view.childInterfaces.size == 1 && only.arguments.size == 1 do
        throwError "fixture: dependent child acquired richer-context arguments"
      unless closed only.closedType do
        throwError "fixture: dependent child interface did not close"
    assertRestored branch
    child.mvarId!.withContext do
      typedAssign child.mvarId! (mkApp (mkConst ``Fin.last) (← localNamed `n))
    right.pending.withContext do
      typedAssign right.pending (mkApp (mkConst ``Fin.last) (← localNamed `m))
    let completed ← snapshot
    Projection.withView state.base fun _ view _ => do
      let native ← instantiateMVars prepared.expression
      replay native prepared.expected
      replay view prepared.expected
      unless ← isDefEq native view do throwError "fixture: dependent completed native replay mismatch"
    assertRestored completed
  pass "dependent-asymmetric-context-and-foreign-capture-refusal"

private unsafe def restorationFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let unknown ← registerInternalExceptionId `partialChildUnknown
  for mode in [0, 1, 2, 3, 4] do
    discard <| withPreparedSketch target (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
      let state ← ChildProjection.build prepared
      let left ← owned prepared `left
      let child ← natChild left.pending
      typedAssign left.pending (mkApp (mkConst ``Nat.succ) child)
      let before ← snapshot
      let reached ← IO.mkRef false
      let token ← IO.CancelToken.new
      let result ← catchAll <| withTheReader Core.Context (fun context => { context with cancelTk? := some token }) do
        withPartialView state left.pending (fun _ => do
          reached.set true
          discard <| mkFreshExprMVar (mkConst ``Nat)
          discard <| mkFreshLevelMVar
          logInfo "speculative child projection diagnostic"
          match mode with
          | 0 => pure ()
          | 1 => throwError "child projection injected ordinary failure"
          | 2 => throw (.internal unknown)
          | 3 => token.set; Core.checkInterrupted
          | _ => Core.throwMaxHeartbeat `partialChild `maxHeartbeats 1)
      assertRestored before
      unless ← reached.get do throwError "fixture: exception injection did not reach grounded state"
      match mode, result with
      | 0, .ok () => pure ()
      | 1, .error (.error _ message) =>
        unless (← message.toString) == "child projection injected ordinary failure" do
          throwError "fixture: ordinary exception changed"
      | 2, .error (.internal id _) => unless id == unknown do throwError "fixture: internal exception changed"
      | 3, .error exception => unless exception.isInterrupt do throwError "fixture: interruption changed"
      | 4, .error exception => unless exception.isMaxHeartbeat do throwError "fixture: resource exception changed"
      | _, _ => throwError "fixture: unexpected exception result"
      unless !(← child.mvarId!.isAssigned) do throwError "fixture: child placeholder leaked"
    pass s!"all-exit-restoration-{mode}"

private unsafe def frontierFixture : TermElabM Unit := do
  let target ← elabType (← `((Nat × Nat) × Nat))
  for shared in [true, false] do
    discard <| withPreparedSketch target
        (← `(term| ((?left : Nat × Nat), (?right : Nat)))) fun prepared => do
      let state ← ChildProjection.build prepared
      let left ← owned prepared `left
      let first ← natChild left.pending
      let second ← if shared then pure first else natChild left.pending
      typedAssign left.pending (← mkAppM ``Prod.mk #[first, second])
      let branch ← snapshot
      withPartialView state left.pending fun view => do
        unless view.childInterfaces.size == (if shared then 1 else 2) do
          throwError "fixture: shared/distinct child identity changed"
        let body := view.partialClosure
        let firstResult ← whnf (← mkAppM ``Prod.fst #[body])
        let secondResult ← whnf (← mkAppM ``Prod.snd #[body])
        unless (firstResult == secondResult) == shared do
          throwError "fixture: same-type child parameters were aliased or split"
      assertRestored branch
  pass "shared-child-identity-and-distinct-same-type-frontier"
  let natTarget := mkConst ``Nat
  discard <| withPreparedSketch natTarget (← `(term| (?left : Nat))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let n ← natChild left.pending
    let i ← left.pending.withContext do
      mkFreshExprMVar (mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) n)) .syntheticOpaque
    typedAssign left.pending (mkApp (mkConst ``Nat.succ)
      (mkApp2 (mkConst ``Fin.val) (mkApp (mkConst ``Nat.succ) n) i))
    let branch ← snapshot
    let result ← tryPartialView state left.pending (fun _ => pure true)
    unless result.isNone do throwError "fixture: cross-child dependent type was abstracted independently"
    assertRestored branch
  pass "cross-child-type-dependency-refused"
  for useHave in [false, true] do
    discard <| withPreparedSketch natTarget (← `(term| (?left : Nat))) fun prepared => do
      let state ← ChildProjection.build prepared
      let left ← owned prepared `left
      let changed ← left.pending.change (.letE `hidden (mkConst ``Nat) (mkNatLit 0) (mkConst ``Nat) useHave)
      -- Native introduction intentionally turns both source let/have forms
      -- into dependent let locals (Intro.lean), which the fragment excludes.
      let (_, body) ← changed.intro1P
      let child ← natChild body
      typedAssign body (mkApp (mkConst ``Nat.succ) child)
      let declaration ← child.mvarId!.getDecl
      unless declaration.lctx.any (fun entry => entry.isLet) do
        throwError "fixture: hidden local was erased before the refusal test"
      let branch ← snapshot
      let result ← tryPartialView state left.pending (fun _ => pure true)
      unless result.isNone do throwError "fixture: let/have child context was accepted"
      assertRestored branch
  pass "fresh-let-and-have-child-contexts-refused"

private unsafe def shadowFixture : TermElabM Unit := do
  let target ← elabType (← `((x : Nat) → ((x : Nat) → Nat) × Nat))
  let target ← instantiateMVars target
  discard <| withPreparedSketch target
      (← `(fun (x : Nat) => ((?left : (x : Nat) → Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let right ← owned prepared `right
    let (_, body) ← left.pending.intro1P
    let child ← natChild body
    typedAssign body (mkApp (mkConst ``Nat.succ) child)
    let declaration ← child.mvarId!.getDecl
    let args := declaration.lctx.getFVars
    unless args.size == 2 && args[0]! != args[1]! do
      throwError "fixture: shadow telescope did not contain two different locals"
    let names := declaration.lctx.foldl (fun names entry => names.push entry.userName.eraseMacroScopes) #[]
    unless names == #[`x, `x] do throwError "fixture: expected genuine shadowed local names, got {names}"
    let branch ← snapshot
    let projected ← withPartialView state left.pending fun view => do
      let some item := view.childInterfaces[0]? | throwError "fixture: missing shadow child"
      unless item.arguments == args do throwError "fixture: original shadow telescope order changed"
      mkLambdaFVars view.parameters view.program (usedOnly := false)
    assertRestored branch
    let nat := mkConst ``Nat
    let zero2 := mkLambda `x .default nat (mkLambda `x .default nat (mkNatLit 0))
    let zero1 := mkLambda `x .default nat (mkNatLit 0)
    for index in [0, 1] do
      restore branch
      typedAssign child.mvarId! args[index]!
      typedAssign right.pending (mkNatLit 0)
      let childClosure := mkLambda `x .default nat (mkLambda `x .default nat (.bvar (1-index)))
      let expected := mkAppN projected #[zero2, zero1, childClosure]
      let native ← instantiateMVars prepared.expression
      replay expected prepared.expected
      replay native prepared.expected
      unless ← isDefEq native expected do throwError "fixture: same-name variables captured during closure"
  pass "shadowed-binders-preserve-native-identity-and-order"

private unsafe def naturalApplyFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat × Nat))
  let contract ← term (← `(fun pair : Nat × Nat => pair.1 = 0))
  let observations ← mkObservations contract target
  discard <| withPreparedSketch target
      (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let state ← ChildProjection.build prepared
    let left ← owned prepared `left
    let right ← owned prepared `right
    let [child] ← left.pending.apply (mkConst ``Nat.succ)
      | throwError "fixture: actual successor application produced an unexpected frontier"
    let declaration ← child.getDecl
    unless declaration.kind.isNatural && declaration.depth == prepared.depth &&
        !state.beforeSearch.decls.contains child do
      throwError "fixture: native application did not produce a fresh natural child"
    let branch ← snapshot
    let result ← ChildProjection.observe state left.pending .strictConstructive contract observations
    unless result.enhanced && result.report.refuted do
      throwError "fixture: natural application child did not admit uniform refutation"
    assertRestored branch
    let projected ← withPartialView state left.pending fun view => do
      let some item := view.childInterfaces[0]? | throwError "fixture: missing application child"
      unless view.childInterfaces.size == 1 && item.id == child && item.declaration.kind.isNatural do
        throwError "fixture: application child was retagged or replaced"
      mkLambdaFVars view.parameters view.program (usedOnly := false)
    assertRestored branch
    for n in [0, 7] do
      restore branch
      typedAssign child (mkNatLit n)
      typedAssign right.pending (mkNatLit 2)
      let native ← instantiateMVars prepared.expression
      let expected := mkAppN projected #[mkNatLit 99, mkNatLit 2, mkNatLit n]
      replay native prepared.expected
      replay expected prepared.expected
      unless ← isDefEq native expected do
        throwError "fixture: actual-application child completion disagrees with projection"
  pass "actual-native-apply-natural-child-refutes-and-corresponds"
  discard <| withPreparedSketch target
      (← `(term| ((?left : Nat), (?right : Nat)))) fun prepared => do
    let left ← owned prepared `left
    let caller ← left.pending.withContext do
      mkFreshExprMVar (mkConst ``Nat) .syntheticOpaque
    let [child] ← caller.mvarId!.apply (mkConst ``Nat.succ)
      | throwError "fixture: caller application produced an unexpected frontier"
    unless (← child.getDecl).kind.isNatural do
      throwError "fixture: caller control is not a native natural child"
    let state ← ChildProjection.build prepared
    unless state.beforeSearch.decls.contains child do throwError "fixture: caller is absent from baseline"
    typedAssign left.pending (mkApp (mkConst ``Nat.succ) (mkMVar child))
    let branch ← snapshot
    let result ← ChildProjection.observe state left.pending .strictConstructive contract observations
    unless !result.enhanced && result.report.statuses == #[some .stuck] do
      throwError "fixture: pre-search natural child was captured"
    assertRestored branch
    unless !(← child.isAssigned) do throwError "fixture: caller natural child was assigned"
  pass "pre-search-natural-application-child-remains-opaque"

run_elab do prefixFixture
run_elab do delayedFixture
run_elab do erasedDependencyFixture
run_elab do unsupportedFixture
run_elab do asymmetricFixture
run_elab do restorationFixture
run_elab do frontierFixture
run_elab do shadowFixture
run_elab do naturalApplyFixture
run_elab do IO.println "PARTIAL CHILD MATRIX COMPLETE"

end Leant2Tests.SketchChildProjection
