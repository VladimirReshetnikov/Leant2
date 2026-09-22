import Leant2.Frontend.Sketch.Projection

/-! Native whole-owned-hole projection, exact closure replay, profile refusal,
and transactional restoration. These are synthesis-substrate tests; they do
not establish a search performance or corpus-completion result. -/
namespace Leant2Tests.SketchProjection
open Lean Meta Elab
open Lean.Elab.Term hiding mkConst
open Leant2 Leant2.Frontend.Sketch
open Leant2.Frontend.Sketch.Projection

private def frozen (e : Expr) : Bool :=
  !e.hasExprMVar && !e.hasLevelMVar && !e.hasLooseBVars && !e.hasSorry

private def closed (e : Expr) : Bool := frozen e && !e.hasFVar

/-- Restore all backtrackable state even when native resource/cancel exceptions
are not caught by an ordinary MetaM exception handler. No depth increment. -/
private def isolated (action : MetaM α) : MetaM α := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  try action
  finally
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

private def requireDepth (depth : Nat) : MetaM Unit := do
  unless (← getMCtx).depth == depth do
    throwError "projection: changed owned metavariable depth"

/-- Synchronous safe declaration check, including the expression's exact type.
The returned environment is inspected only for axiom accounting, never installed
persistently. Universes must already be rigid; there is no generalization. -/
private def replay (e type : Expr) : MetaM Unit := withLCtx {} #[] do
  unless closed e && closed type do
    throwError "projection: replay input is not closed and frozen"
  let params := (collectLevelParams (collectLevelParams {} type) e).params.toList
  let .ok _ ← kernelCheckAndAudit `Leant2Tests.SketchProjection e type params false
    | throwError "projection: independent safe kernel replay failed"
  pure ()

private def typedAssign (goal : MVarId) (value : Expr) : MetaM Unit := goal.withContext do
  unless (← goal.isAssignable) && !(← goal.isAssigned) && !(← goal.isDelayedAssigned) do
    throwError "projection: assignment target is not an open owned-depth goal"
  check value
  unless ← isDefEq (← inferType value) (← goal.getType) do
    throwError "projection: assignment type mismatch"
  unless ← goal.checkedAssign value do
    throwError "projection: assignment dependency check failed"

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
    throwError "prototype: exact Core/Meta/Term state identity was not restored"

private def observeAll (action : TermElabM α) : TermElabM (Except Exception α) := do
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch exception => return .error exception

private def pass (name : String) : TermElabM Unit := IO.println s!"PASS {name}"

private def owned (prepared : Prepared) (name : Name) : MetaM OwnedHole := do
  let some hole := prepared.holes.find? (·.spec.sourceName.eraseMacroScopes == name.eraseMacroScopes)
    | throwError "prototype: missing original hole {name}"
  return hole

private def localNamed (name : Name) : MetaM Expr := do
  for entry in (← getLCtx) do
    if entry.userName.eraseMacroScopes == name then return entry.toExpr
  throwError "prototype: missing original local {name}"

private def assignLocal (hole : OwnedHole) (name : Name) : MetaM Unit := hole.pending.withContext do
  typedAssign hole.pending (← localNamed name)

private def requireStatuses (projection : Projection.State) (originalContract : Expr) (observations : Array Observation)
    (expected : Array (Option ObservationStatus)) : MetaM Unit := do
  let report ← Projection.observe projection .strictConstructive originalContract observations
  unless report.statuses == expected do
    throwError "prototype: statuses {repr report.statuses}, expected {repr expected}"

private unsafe def pairFixture : TermElabM Unit := do
  let target ← elabType (← `(Nat → Nat → Nat × Nat))
  let target ← instantiateMVars target
  let contract ← elabTerm (← `(fun f : Nat → Nat → Nat × Nat =>
    (f 0 1).1 = 0 ∧ (f 1 0).1 = 1 ∧ (f 0 1).2 = 1 ∧ (f 1 0).2 = 0)) none
  let contract ← instantiateMVars contract
  unless closed contract do throwError "pair fixture's original contract is not frozen"
  let sketch ← `(fun (x y : Nat) => ((?left : Nat), (?right : Nat)))
  let before ← snapshot
  discard <| withPreparedSketch target sketch fun prepared => do
    unless prepared.holes.size == 2 && !prepared.wrappers.isEmpty do
      throwError "prototype: fixture did not create two holes and native delayed closures"
    let initial ← snapshot
    let projection ← build prepared
    assertRestored initial
    let some _ ← tryBuild prepared | throwError "supported projection was refused by tryBuild"
    assertRestored initial
    pass "build-typed-native-skeleton-and-restore"
    let observations ← mkObservations contract target
    unless observations.size == 4 do throwError "prototype: wrong observation inventory"
    let left ← owned prepared `left
    let right ← owned prepared `right
    let branch ← snapshot
    requireStatuses projection contract observations #[some .stuck, some .stuck, some .stuck, some .stuck]
    assertRestored branch
    pass "all-original-holes-opaque"
    -- Neither valid native assignment nor observation may accidentally acquire
    -- access to a placeholder absent from the original pending lctx.
    isolated do
      let some item := projection.interfaces[0]? | throwError "prototype: missing first interface"
      withLCtx {} #[] <| withLocalDeclD `outside item.closedType fun parameter => do
        let entries := item.owned.declaration.lctx.foldl (fun result entry => result ++ [entry]) []
        withExistingLocalDecls entries do
          let value := mkAppN parameter item.arguments
          check value
          if ← item.owned.pending.checkedAssign value then
            throwError "prototype: checkedAssign accepted an out-of-scope placeholder"
    assertRestored branch
    pass "unchecked-scope-shortcut-is-rejected"
    let wrongType ← observeAll do
      isolated <| typedAssign left.pending (mkConst ``Bool.false)
    assertRestored branch
    let .error (.error _ message) := wrongType
      | throwError "prototype: assignment type mismatch was accepted"
    unless (← message.toString) == "projection: assignment type mismatch" do
      throwError "prototype: wrong assignment-type rejection {message}"
    pass "wrong-assignment-type-is-rejected-before-commit"
    -- A wrong completed left body refutes before right has a value.
    typedAssign left.pending (mkNatLit 0)
    let wrongBranch ← snapshot
    requireStatuses projection contract observations #[some .satisfied, some .refuted, none, none]
    assertRestored wrongBranch
    unless !(← right.pending.isAssigned) do throwError "prototype: pruning filled the right hole"
    pass "wrong-left-refutes-with-right-open"
    modifyThe Meta.State fun _ => branch.metaState
    modifyThe Core.State fun _ => branch.coreState
    assignLocal left `x
    let correctBranch ← snapshot
    requireStatuses projection contract observations #[some .satisfied, some .satisfied, some .stuck, some .stuck]
    assertRestored correctBranch
    pass "sibling-rollback-removes-refutation"
    assignLocal right `y
    let completeBranch ← snapshot
    requireStatuses projection contract observations
      #[some .satisfied, some .satisfied, some .satisfied, some .satisfied]
    assertRestored completeBranch
    withView projection fun _ view completed => do
      unless completed == #[true, true] do throwError "prototype: complete holes were opaque"
      let native ← instantiateMVars prepared.expression
      replay native prepared.expected
      replay view prepared.expected
      unless ← isDefEq native view do
        throwError "prototype: typed projection disagrees with original native graph"
    assertRestored completeBranch
    pass "complete-original-native-projection-agreement"
    modifyThe Meta.State fun _ => branch.metaState
    modifyThe Core.State fun _ => branch.coreState
    -- An ordinary assignment to an unfinished child remains completely opaque.
    let child ← left.pending.withContext do
      let child ← mkFreshExprMVar (mkConst ``Nat) .syntheticOpaque
      typedAssign left.pending child
      return child.mvarId!
    let partialBranch ← snapshot
    requireStatuses projection contract observations #[some .stuck, some .stuck, some .stuck, some .stuck]
    withView projection fun _ _ completed => do
      unless completed == #[false, false] do throwError "prototype: partial child leaked into view"
    assertRestored partialBranch
    pass "partially-assigned-owned-hole-stays-opaque"
    child.withContext do typedAssign child (← localNamed `x)
    requireStatuses projection contract observations #[some .satisfied, some .satisfied, some .stuck, some .stuck]
    pass "child-completion-becomes-whole-hole-substitution"
  assertRestored before
  pass "preparation-restores-after-all-branches"

private unsafe def excludedContexts : TermElabM Unit := do
  for (label, sketch) in [
      ("let", ← `(let h : Nat := 1; (?body : Nat))),
      ("have", ← `(have h : Nat := 1; (?body : Nat)))] do
    discard <| withPreparedSketch (mkConst ``Nat) sketch fun prepared => do
      let before ← snapshot
      let result ← observeAll do build prepared
      assertRestored before
      let .error (.error _ message) := result
        | throwError "prototype: excluded {label} context entered projection"
      unless ((← message.toString).splitOn "original let/have local excluded").length > 1 do
        throwError "prototype: unexpected exclusion error {message}"
      let result ← tryBuild prepared
      assertRestored before
      unless result.isNone do throwError "tryBuild accepted an excluded let/have context"
    pass s!"original-{label}-context-conservatively-excluded"

private unsafe def exceptionalRestoration : TermElabM Unit := do
  let target ← elabType (← `(Nat → Nat))
  let target ← instantiateMVars target
  let sketch ← `(fun x : Nat => (?body : Nat))
  let unknown ← registerInternalExceptionId `sketchProjectionUnknown
  for mode in [0, 1, 2, 3] do
    discard <| withPreparedSketch target sketch fun prepared => do
      let token ← IO.CancelToken.new
      let reached ← IO.mkRef false
      let before ← snapshot
      let result ← observeAll <| withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
        build prepared do
          Core.checkInterrupted
          let mut assigned := false
          for hole in prepared.holes do
            assigned := assigned || (← hole.pending.isAssigned)
          if assigned then
            reached.set true
            discard <| mkFreshExprMVar (mkConst ``Nat)
            discard <| mkFreshLevelMVar
            logInfo "speculative projection diagnostic"
            match mode with
            | 0 => throwError "projection injected ordinary failure"
            | 1 => throw (.internal unknown)
            | 2 => token.set; Core.checkInterrupted
            | _ => Core.throwMaxHeartbeat `sketchProjection `maxHeartbeats 1
      assertRestored before
      unless ← reached.get do throwError "prototype: did not reach mutated projection state"
      match mode, result with
      | 0, .error (.error _ message) =>
        unless (← message.toString) == "projection injected ordinary failure" do
          throwError "prototype: ordinary exception payload changed"
      | 1, .error (.internal id _) => unless id == unknown do throwError "prototype: internal id changed"
      | 2, .error error => unless error.isInterrupt do throwError "prototype: cancellation identity changed"
      | 3, .error error => unless error.isMaxHeartbeat do throwError "prototype: resource exception changed"
      | _, _ => throwError "prototype: wrong exceptional restoration outcome"
      requireDepth prepared.depth
      for hole in prepared.holes do
        unless !(← hole.pending.isAssigned) do throwError "prototype: placeholder assignment escaped"
    pass s!"projection-exact-state-exception-{mode}"

/-- A harmless but profile-forbidden dependency, deliberately placed only in
an otherwise erased predicate/decider binder domain. No oracle providers. -/
axiom projectionForbidden : True

private unsafe def erasedEvidenceControl : TermElabM Unit := do
  let target ← elabType (← `(Nat → Nat → Nat × Nat))
  let target ← instantiateMVars target
  let falseDecision ← elabTerm (← `(Decidable.isFalse (fun impossible : False => impossible)))
    (some (mkApp (mkConst ``Decidable) (mkConst ``False)))
  let falseDecision ← instantiateMVars falseDecision
  let sketch ← `(fun (x y : Nat) => ((?left : Nat), (?right : Nat)))
  let badTarget := mkApp (mkLambda `erased .default (mkConst ``True) target)
    (mkConst ``projectionForbidden)
  let lawful : Observation := {
    predicate := mkLambda `program .default target (mkConst ``False)
    decider := some (mkLambda `program .default target falseDecision) }
  let forbidden : Observation := {
    predicate := mkLambda `program .default badTarget (mkConst ``False)
    decider := some (mkLambda `program .default badTarget falseDecision) }
  let before ← snapshot
  discard <| withPreparedSketch target sketch fun prepared => do
    let projection ← build prepared
    let branch ← snapshot
    -- Establish that this is an actual false reduction, not a stuck-control
    -- fixture. A beta-erased audit would incorrectly authorize this result.
    withView projection fun _ view _ => do
      let (raw, _) ← evalObservations #[forbidden] view #[] instantiateMVars
        Core.checkInterrupted
      unless raw.statuses == #[some .refuted] do
        throwError "prototype: forbidden evidence did not reduce false"
      let predicate := forbidden.predicate.beta #[view]
      let some decider := forbidden.decider | throwError "prototype: missing control decider"
      unless ← falseEvidenceAllowed .strictConstructive predicate (decider.beta #[view]) do
        throwError "prototype: erased evidence no longer exposes the intended audit defect"
    assertRestored branch
    requireStatuses projection lawful.predicate #[forbidden] #[some .stuck]
    assertRestored branch
    requireStatuses projection lawful.predicate #[lawful] #[some .refuted]
    assertRestored branch
    -- Observation preparation can erase the original contract's binder
    -- domain. Its separate full application audit must still retain it.
    let decomposed ← isolated <| mkObservations forbidden.predicate target
    unless decomposed.size == 1 && decomposed.all (fun observation =>
        !(observation.predicate.getUsedConstants.contains ``projectionForbidden)) do
      throwError "contract decomposition did not erase the intended original dependency"
    withView projection fun _ view _ => do
      let (raw, _) ← evalObservations decomposed view #[] instantiateMVars Core.checkInterrupted
      unless raw.refuted do throwError "decomposed original contract does not reduce false"
    let originalRefused ← Projection.observe projection .strictConstructive forbidden.predicate decomposed
    unless originalRefused.statuses == #[some .stuck] do
      throwError "original contract binder dependency was erased before authorization"
    assertRestored branch
    let standardRefused ← Projection.observe projection .standard forbidden.predicate decomposed
    unless standardRefused.statuses == #[some .stuck] do
      throwError "standard profile accepted the erased original contract axiom"
    assertRestored branch
    let allowed ← Projection.observe projection (.projectRelative [``projectionForbidden])
      forbidden.predicate decomposed
    unless allowed.statuses == #[some .refuted] do
      throwError "explicit profile did not authorize its original contract premise"
    assertRestored branch
    let refusedAgain ← Projection.observe projection .strictConstructive forbidden.predicate decomposed
    unless refusedAgain.statuses == #[some .stuck] do
      throwError "project-relative authorization survived a strict profile change"
    assertRestored branch
  assertRestored before
  pass "unreduced-forbidden-binder-domain-refuses-false"

private unsafe def dependentAsymmetricFixture : TermElabM Unit := do
  let target ← elabType (← `((n : Nat) →
    Fin (n + 1) × ((m : Nat) → Fin (n + 1) → Fin (m + 1))))
  let target ← instantiateMVars target
  let contract ← elabTerm (← `(fun f : ((n : Nat) →
      Fin (n + 1) × ((m : Nat) → Fin (n + 1) → Fin (m + 1))) =>
    (f 2).1.val = 2 ∧ (f 7).1.val = 7 ∧
    ((f 2).2 3 (Fin.last 2)).val = 3 ∧ ((f 7).2 1 (Fin.last 7)).val = 1)) none
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  unless closed target do throwError "dependent fixture's original target is not frozen"
  let contract ← instantiateMVars contract
  unless closed contract do throwError "dependent fixture's original contract is not frozen"
  let sketch ← `(fun n : Nat => ((?left : Fin (n + 1)),
    fun (m : Nat) (foreign : Fin (n + 1)) => (?right : Fin (m + 1))))
  let before ← snapshot
  discard <| withPreparedSketch target sketch fun prepared => do
    let retainsAssigned ← isolated do
      let mut declarations := prepared.holes.map (·.declaration)
      for wrapper in prepared.wrappers do
        declarations := declarations.push (← wrapper.outer.getDecl)
        declarations := declarations.push (← wrapper.pending.getDecl)
      let mut found := false
      for declaration in declarations do
        let types := declaration.lctx.foldl (fun types entry => types.push entry.type)
          #[declaration.type]
        for type in types do
          if type.hasExprMVar || type.hasLevelMVar then
            found := true
            unless frozen (← instantiateMVars type) do
              throwError "dependent fixture retains unresolved, not assigned, inference variables"
      return found
    unless retainsAssigned do
      throwError "dependent fixture no longer exercises assigned inference variables in stored declarations"
    let projection ← build prepared
    let left ← owned prepared `left
    let right ← owned prepared `right
    unless left.declaration.lctx.getFVars.size == 1 && right.declaration.lctx.getFVars.size == 3 do
      throwError "dependent fixture did not produce asymmetric one/three-binder contexts"
    let observations ← mkObservations contract target
    unless observations.size == 4 do throwError "dependent fixture has wrong observation count"
    let branch ← snapshot
    requireStatuses projection contract observations #[some .stuck, some .stuck, some .stuck, some .stuck]
    assertRestored branch
    isolated <| right.pending.withContext do
      let foreign ← localNamed `foreign
      check foreign
      unless ← isDefEq (← inferType foreign) left.declaration.type do
        throwError "foreign-local scope control does not have the original left type"
      if ← left.pending.checkedAssign foreign then
        throwError "native scope checker captured a same-type foreign local"
    assertRestored branch
    pass "dependent-same-type-richer-context-local-refused"
    left.pending.withContext do
      let n ← localNamed `n
      let proof := mkApp (mkConst ``Nat.zero_lt_succ) n
      typedAssign left.pending (← mkAppM ``Fin.mk #[mkNatLit 0, proof])
    let wrongBranch ← snapshot
    requireStatuses projection contract observations #[some .refuted, none, none, none]
    assertRestored wrongBranch
    unless !(← right.pending.isAssigned) do throwError "dependent early observation assigned right"
    pass "dependent-wrong-left-refutes-before-right-completion"
    modifyThe Meta.State fun _ => branch.metaState
    modifyThe Core.State fun _ => branch.coreState
    left.pending.withContext do
      typedAssign left.pending (mkApp (mkConst ``Fin.last) (← localNamed `n))
    let corrected ← snapshot
    requireStatuses projection contract observations #[some .satisfied, some .satisfied, some .stuck, some .stuck]
    assertRestored corrected
    right.pending.withContext do
      typedAssign right.pending (mkApp (mkConst ``Fin.last) (← localNamed `m))
    let completed ← snapshot
    requireStatuses projection contract observations
      #[some .satisfied, some .satisfied, some .satisfied, some .satisfied]
    withView projection fun _ view flags => do
      unless flags == #[true, true] do throwError "dependent hole completions stayed opaque"
      let native ← instantiateMVars prepared.expression
      replay native target
      replay view target
      unless ← isDefEq native view do
        throwError "dependent asymmetric projection disagrees with original native root"
    assertRestored completed
    pass "dependent-asymmetric-native-projection-replay-and-rollback"
  assertRestored before

private unsafe def optionalBuildExceptions : TermElabM Unit := do
  let target ← elabType (← `(Nat → Nat))
  let target ← instantiateMVars target
  let sketch ← `(fun x : Nat => (?body : Nat))
  let internal ← registerInternalExceptionId `sketchProjectionOptionalInternal
  let exceptions : Array Exception := #[
    .error .missing m!"optional ordinary failure",
    .internal internal (({} : KVMap).setNat `marker 73),
    .internal interruptExceptionId,
    .error .missing (.tagged `runtime.maxHeartbeats m!"projection heartbeats"),
    .error .missing (.tagged `runtime.maxRecDepth m!"projection recursion"),
    .error .missing (.tagged `runtime.projectionUnknown m!"projection unknown runtime")]
  -- Native isRuntime recognizes the resource exceptions, not arbitrary tags
  -- beginning with `runtime`. This last case is an ordinary unsupported error.
  unless !(exceptions[5]!).isRuntime do throwError "runtime-looking tag became a native resource exception"
  for index in [:exceptions.size] do
    let exception := exceptions[index]!
    discard <| withPreparedSketch target sketch fun prepared => do
      let calls ← IO.mkRef 0
      let reached ← IO.mkRef false
      let before ← snapshot
      let result ← observeAll do
        tryBuild prepared do
          calls.modify (· + 1)
          Core.checkInterrupted
          for hole in prepared.holes do
            if ← hole.pending.isAssigned then
              reached.set true
              throw exception
      assertRestored before
      unless (← reached.get) && (← calls.get) > 1 do
        throwError "optional construction did not fail after actual scope/assignment work"
      match index, result with
      | 0, .ok none | 5, .ok none => pure ()
      | 0, _ | 5, _ => throwError "optional build did not refuse ordinary failure"
      | _, .error actual =>
        match exception, actual with
        | .internal expectedId expectedData, .internal actualId actualData =>
          unless expectedId == actualId && expectedData == actualData do
            throwError "optional build changed internal exception identity/payload"
        | .error _ expected, .error _ actual =>
          unless expected.stripNestedTags.kind == actual.stripNestedTags.kind &&
              (← expected.toString) == (← actual.toString) do
            throwError "optional build changed runtime exception payload/category"
        | _, _ => throwError "optional build changed exception constructor"
      | _, _ => throwError "optional build swallowed internal or runtime exception"
    pass s!"optional-build-exception-{index}"

-- Never executed: the kernel only discards this proof field while reducing
-- the Decidable constructor. It has no axioms and is still unsafe evidence.
set_option linter.defProp false in
private unsafe def uncheckedFalse (_n : Nat) : False := uncheckedFalse 0

private unsafe def unsafeEvidenceControl : TermElabM Unit := do
  let target := mkConst ``Nat
  let proposition := mkConst ``True
  let contract := mkLambda `program .default target proposition
  let negative := mkLambda `proof .default proposition (mkApp (mkConst ``uncheckedFalse) (mkNatLit 0))
  let decision := mkApp2 (mkConst ``Decidable.isFalse) proposition negative
  let observation : Observation := {
    predicate := contract
    decider := some (mkLambda `program .default target decision) }
  unless (← getConstInfo ``uncheckedFalse).isUnsafe && (← collectAxioms ``uncheckedFalse).isEmpty do
    throwError "unsafe observation fixture lost its unsafe/axiom-free distinction"
  let canonical := mkApp3 (mkConst ``of_decide_eq_false) proposition decision
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))
  let .error (.kernelRejected message) ← gate .strictConstructive canonical
      (mkApp (mkConst ``Not) proposition) none
    | throwError "safe gate did not reject the unsafe negative evidence"
  unless (message.splitOn "unsafe").length > 1 do
    throwError "unsafe fixture kernel failure had a different cause"
  discard <| withPreparedSketch target (← `((?body : Nat))) fun prepared => do
    let projection ← build prepared
    let branch ← snapshot
    withView projection fun _ view _ => do
      let (raw, _) ← evalObservations #[observation] view #[] instantiateMVars Core.checkInterrupted
      unless raw.refuted do throwError "unsafe observation does not actually reduce false"
    assertRestored branch
    for profile in [.strictConstructive, .standard, .projectRelative [``uncheckedFalse]] do
      let result ← observeAll do Projection.observe projection profile contract #[observation]
      assertRestored branch
      match result with
      | .ok report =>
        if report.refuted then throwError "unsafe negative observation was authorized"
      | .error (.error _ message) =>
        unless (← message.toString) == "projection: independent safe kernel replay failed" do
          throwError "unexpected unsafe-evidence refusal {message}"
      | .error exception => throw exception
  pass "unsafe-false-evidence-never-authorized-by-any-profile"


run_elab do
  pairFixture
  excludedContexts
  exceptionalRestoration
  erasedEvidenceControl
  dependentAsymmetricFixture
  optionalBuildExceptions
  unsafeEvidenceControl
  IO.println "SKETCH PROJECTION MATRIX COMPLETE"

end Leant2Tests.SketchProjection
