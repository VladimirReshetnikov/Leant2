import Leant2.Frontend.Sketch.Prepare

/- Owned sketch preparation, kernel-checked closure completion, and exact native
   state restoration. These tests do not establish sketch synthesis capability. -/
namespace Leant2Tests.SketchPreparation
open Lean Meta Elab
open Lean.Elab.Term hiding mkConst
open Leant2.Frontend.Sketch

macro "sketchPreparationDup% " value:term : term => `(($value, $value))
macro "sketchPreparationExtend% " value:term : term => `(($value, fun (x : Nat) => $value))
macro "sketchPreparationConflict% " value:term : term =>
  `((fun (x : Nat) => $value, fun (b : Bool) => $value))
macro "sketchPreparationNewHole%" : term => `((?_ : Nat))
macro "sketchPreparationErasedHole%" : term =>
  `(let +usedOnly h : Nat := ?_; (0 : Nat))
macro "sketchPreparationErasedClosed%" : term =>
  `(let +usedOnly h : Nat := 7; (0 : Nat))

syntax (name := sketchPreparationCaller) "sketchPreparationCaller%" : term
@[term_elab sketchPreparationCaller] def elabCaller : TermElab := fun _ _ => do
  let some caller := (← getMCtx).findUserName? `body
    | throwError "test caller hole was not installed"
  return mkMVar caller

syntax (name := sketchPreparationLoggedError) "sketchPreparationLoggedError%" : term
@[term_elab sketchPreparationLoggedError] def elabLoggedError : TermElab := fun _ _ => do
  logError "injected sketch error"
  return mkNatLit 0

syntax (name := sketchPreparationNewDeclaration) "sketchPreparationNewDeclaration%" : term
@[term_elab sketchPreparationNewDeclaration] def elabNewDeclaration : TermElab := fun _ _ => do
  let namePrefix := (← getEnv).asyncPrefix?.getD `Leant2Tests.SketchPreparation
  let name := namePrefix ++ (← mkFreshUserName `preparationAuxiliary)
  addDecl (.thmDecl {
    name, levelParams := [], type := Lean.mkConst ``True, value := Lean.mkConst ``True.intro })
  return mkNatLit 0

structure Snapshot where
  coreState : Core.State
  metaState : Meta.State
  termState : Term.State

private def snapshot : TermElabM Snapshot := do
  return { coreState := ← getThe Core.State, metaState := ← getThe Meta.State, termState := ← getThe Term.State }

/-- Test-only physical identity is stronger than checking a selected subset
of counters: the wrapper promises to restore the exact three saved records. -/
private unsafe def assertRestored (before : Snapshot) : TermElabM Unit := do
  let after ← snapshot
  unless ptrEq before.coreState after.coreState && ptrEq before.metaState after.metaState &&
      ptrEq before.termState after.termState do
    throwError "preparation did not restore exact Core/Meta/Term state record identity"

private def observeAll (action : TermElabM α) : TermElabM (Except Exception α) := do
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch ex => return .error ex

private def pass (label : String) : TermElabM Unit := IO.println s!"PASS {label}"

private unsafe def reject (label : String) (expected : Expr) (stx : TSyntax `term)
    (messagePart : String := "") : TermElabM Unit := do
  let entered ← IO.mkRef false
  let before ← snapshot
  let outcome ← observeAll <| withPreparedSketch expected stx (fun _ => entered.set true)
  assertRestored before
  if ← entered.get then throwError "{label}: invalid preparation entered consumer"
  let .error ex := outcome | throwError "{label}: invalid preparation was accepted"
  if ex.isInterrupt || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
  let message ← ex.toMessageData.toString
  unless messagePart.isEmpty || (message.splitOn messagePart).length > 1 do
    throwError "{label}: unexpected rejection: {message}"
  pass label

private def kernelReplay (expression expected : Expr) : MetaM Unit := do
  unless !expression.hasMVar && !expression.hasFVar && !expression.hasLooseBVars && !expression.hasSorry do
    throwError "completed expression is not closed"
  let env ← getEnv
  let namePrefix := env.asyncPrefix?.getD `Leant2Tests.SketchPreparation
  let name := namePrefix ++ (← mkFreshUserName `replay)
  let parameters := (collectLevelParams (collectLevelParams {} expected) expression).params.toList
  let declaration := Declaration.defnDecl {
    name, levelParams := parameters, type := expected, value := expression
    hints := .abbrev, safety := .safe }
  match env.addDeclCore 0 1000 declaration none (doCheck := true) with
  | .ok _ => pure ()
  | .error ex => throwError "completed root failed independent kernel replay: {ex.toMessageData (← getOptions)}"

private def complete (prepared : Prepared) (value : OwnedHole → MetaM Expr) : TermElabM Unit := do
  for hole in prepared.holes do
    unless (← getMCtx).depth == prepared.depth && (← hole.pending.isAssignable) do
      throwError "owned hole is not assignable at preparation depth"
    hole.pending.withContext do
      let expression ← value hole
      check expression
      unless ← isDefEq (← inferType expression) (← hole.pending.getType) do
        throwError "completion has wrong original hole type"
      unless ← hole.pending.checkedAssign expression do throwError "checked completion failed"
  let expression ← instantiateMVars prepared.expression
  withLCtx {} #[] <| kernelReplay expression prepared.expected

private def localNamed (name : Name) : MetaM Expr := do
  for localDecl in (← getLCtx) do
    if localDecl.userName.eraseMacroScopes == name then return localDecl.toExpr
  throwError "missing expected local {name}"

private unsafe def positive (label : String) (expected : Expr) (stx : TSyntax `term)
    (count : Nat) (consumer : Prepared → TermElabM Unit := fun _ => pure ()) : TermElabM Report := do
  let before ← snapshot
  let report ← withPreparedSketch expected stx fun prepared => do
    unless prepared.holes.size == count do throwError "{label}: wrong owned-hole count"
    consumer prepared
  assertRestored before
  IO.println s!"PASS {label} holes={report.holes.size} wrappers={report.delayedWrappers} graph={report.unresolvedBeforeConsumer}"
  return report

private def natArrow : MetaM Expr := mkArrow (mkConst ``Nat) (mkConst ``Nat)

private unsafe def ownershipCases : TermElabM Unit := do
  let nat := mkConst ``Nat
  discard <| positive "closed-zero-hole" nat (← `(0)) 0
  discard <| positive "typed-owned-hole" nat (← `((?body : Nat))) 1
  reject "malformed-expected-value" (mkNatLit 0) (← `(?body)) "well-formed type"
  reject "malformed-expected-application" (mkApp nat (mkNatLit 0)) (← `(?body))
  reject "explicit-duplicate-label" (← mkAppM ``Prod #[nat, nat]) (← `((?body, ?body))) "duplicate"
  reject "anonymous-hole" nat (← `((_ : Nat))) "anonymous"
  reject "unnamed-hole" nat (← `((?_ : Nat))) "explicitly named"
  reject "macro-unregistered-hole" nat (← `(sketchPreparationNewHole%)) "unregistered"
  reject "macro-erased-unregistered-hole" nat (← `(sketchPreparationErasedHole%))
    "unregistered native hole or inference obligation"
  discard <| positive "macro-erased-closed-let" nat (← `(sketchPreparationErasedClosed%)) 0
  reject "type-hole" (mkSort (.succ .zero)) (← `(?body)) "type, motive"
  reject "motive-hole" (← mkArrow nat (mkSort (.succ .zero))) (← `(?body)) "type, motive"
  reject "dictionary-hole" (← mkAppM ``Inhabited #[nat]) (← `(?body)) "dictionary"
  reject "fifth-hole" nat (← `((?one : Nat) + ?two + ?three + ?four + ?five)) "at most four"
  reject "recursive-lifting" nat (← `(
    let rec count (n : Nat) : Nat :=
      match n with
      | 0 => 0
      | m + 1 => count m
    count 2)) "recursive lifting"
  reject "new-environment-declaration" nat (← `(sketchPreparationNewDeclaration%)) "new declarations"
  reject "logged-error" nat (← `(sketchPreparationLoggedError%))
  let caller ← mkFreshExprMVar nat .natural `body
  let callerLevel ← mkFreshLevelMVar
  discard <| positive "caller-name-collision" nat (← `((?body : Nat))) 1 fun prepared => do
    let some hole := prepared.holes[0]? | throwError "missing owned hole"
    unless hole.pending != caller.mvarId! do throwError "caller name was captured"
    if ← isDefEq caller (mkNatLit 0) then throwError "caller expression was not rigid"
    if ← isDefEq (mkSort callerLevel) (mkSort .zero) then throwError "caller universe was not rigid"
    complete prepared (fun _ => pure (mkNatLit 7))
  unless !(← caller.mvarId!.isAssigned) && (← instantiateLevelMVars callerLevel) == callerLevel do
    throwError "caller assignment leaked"
  reject "caller-hole-injection" nat (← `(sketchPreparationCaller%)) "caller metavariable"
  let oldTerm ← getThe Term.State
  try
    registerMVarErrorHoleInfo caller.mvarId! .missing
    discard <| positive "caller-error-record-isolated" nat (← `((?body : Nat))) 1 fun prepared =>
      complete prepared (fun _ => pure (mkNatLit 8))
    if ← caller.mvarId!.isAssigned then throwError "caller error-hole was assigned"
  finally modifyThe Term.State fun _ => oldTerm
  let oldMeta ← getThe Meta.State
  try
    modifyPostponed fun pending => pending.push {
      ref := .missing, lhs := callerLevel, rhs := .zero, ctx? := none }
    reject "caller-pending-universe-equation" nat (← `(0)) "caller has pending universe equations"
  finally modifyThe Meta.State fun _ => oldMeta

private unsafe def contextCases : TermElabM Unit := do
  let nat := mkConst ``Nat
  discard <| positive "closed-let" nat (← `(let h : Nat := 1; (?body : Nat))) 1 fun p => do
    let some hole := p.holes[0]? | throwError "missing let-body hole"
    hole.pending.withContext do
      unless ← isDefEq (← localNamed `h) (mkNatLit 1) do
        throwError "genuine let lost its definitional value"
    complete p (fun _ => localNamed `h)
  discard <| positive "closed-have" nat (← `(have h : Nat := 1; (?body : Nat))) 1 fun p => do
    let some hole := p.holes[0]? | throwError "missing have-body hole"
    hole.pending.withContext do
      if ← isDefEq (← localNamed `h) (mkNatLit 1) then
        throwError "nondependent have was unfolded as a genuine let"
    complete p (fun _ => localNamed `h)
  reject "unfinished-let-value" nat (← `(let h : Nat := ?first; (?second : Nat))) "hole-local value"
  reject "unfinished-have-value" nat (← `(have h : Nat := ?first; (?second : Nat))) "hole-local value"
  discard <| positive "lambda-completion" (← natArrow) (← `(fun x : Nat => (?body : Nat))) 1 fun p => do
    let some hole := p.holes[0]? | throwError "missing owned hole"
    let pending := hole.pending
    unless ← pending.isAssignable do throwError "same-depth hole was frozen"
    withNewMCtxDepth do
      if ← pending.isAssignable then throwError "nested depth did not make hole rigid"
    unless ← pending.isAssignable do throwError "hole did not regain owned depth"
    complete p (fun _ => localNamed `x)
  let doubleArrow ← mkArrow nat (← natArrow)
  discard <| positive "nested-lambda-let-completion" doubleArrow
      (← `(fun x : Nat => let y := x; fun z : Nat => (?body : Nat))) 1 fun p =>
    complete p (fun _ => localNamed `y)
  let natBool ← mkArrow nat (← mkArrow (mkConst ``Bool) nat)
  discard <| positive "nested-mixed-lambda-completion" natBool
      (← `(fun x : Nat => fun y : Bool => (?body : Nat))) 1 fun p =>
    complete p (fun _ => localNamed `x)
  let pairFunctions ← mkAppM ``Prod #[← natArrow, ← natArrow]
  discard <| positive "separate-lambda-contexts" pairFunctions
      (← `((fun x : Nat => (?left : Nat), fun y : Nat => (?right : Nat)))) 2 fun p =>
    complete p fun hole => localNamed (if hole.spec.sourceName.eraseMacroScopes == `left then `x else `y)

private unsafe def macroCases : TermElabM Unit := do
  let nat := mkConst ``Nat
  let pair ← mkAppM ``Prod #[nat, nat]
  discard <| positive "macro-compatible-sharing" pair (← `(sketchPreparationDup% ?body)) 1 fun p =>
    complete p (fun _ => pure (mkNatLit 5))
  let pairExtended ← mkAppM ``Prod #[nat, ← natArrow]
  discard <| positive "macro-compatible-extended-context" pairExtended (← `(sketchPreparationExtend% ?body)) 1 fun p =>
    complete p (fun _ => pure (mkNatLit 9))
  let incompatible ← mkAppM ``Prod #[← natArrow, ← mkArrow (mkConst ``Bool) (mkConst ``Bool)]
  reject "macro-incompatible-contexts" incompatible (← `(sketchPreparationConflict% ?body))

private def contaminate (sibling : MVarId) (level : LMVarId) (name : Name) : TermElabM Unit := do
  sibling.assign (mkNatLit 42)
  assignLevelMVar level .zero
  discard <| mkFreshExprMVar (mkConst ``Nat)
  discard <| mkFreshLevelMVar
  logInfo "speculative preparation diagnostic"
  modifyThe Core.State fun state => { state with infoState := { state.infoState with enabled := false } }
  modifyThe Term.State fun state => { state with
    levelNames := `contaminated :: state.levelNames
    pendingMVars := sibling :: state.pendingMVars
    mvarArgNames := state.mvarArgNames.insert sibling `contaminated }
  addDecl (.axiomDecl { name, levelParams := [], type := mkConst ``True, isUnsafe := false })

private unsafe def restorationCases : TermElabM Unit := do
  let unknown ← registerInternalExceptionId `sketchPreparationUnknown
  for mode in [0, 1, 2, 3, 4] do
    let sibling ← mkFreshExprMVar (mkConst ``Nat)
    let level ← mkFreshLevelMVar
    let namePrefix := (← getEnv).asyncPrefix?.getD `Leant2Tests.SketchPreparation
    let name := namePrefix ++ (← mkFreshUserName `mutated)
    let token ← IO.CancelToken.new
    let stx ← `((?body : Nat))
    -- Existing caller queue is intentionally nonempty, and must not be drained.
    let oldTerm ← getThe Term.State
    modifyThe Term.State fun state => { state with pendingMVars := sibling.mvarId! :: state.pendingMVars }
    try
      let before ← snapshot
      let reached ← IO.mkRef false
      let outcome ← observeAll <| withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
        withPreparedSketch (mkConst ``Nat) stx fun prepared => do
          reached.set true
          contaminate sibling.mvarId! level.mvarId! name
          match mode with
          | 0 => complete prepared (fun _ => pure (mkNatLit 1))
          | 1 => throwError "ordinary preparation consumer failure"
          | 2 => throw (.internal unknown)
          | 3 => token.set; Core.checkInterrupted
          | _ => Core.throwMaxHeartbeat `sketchPreparation `maxHeartbeats 1
      assertRestored before
      unless ← reached.get do throwError "restoration fixture did not enter consumer"
      match mode, outcome with
      | 0, .ok _ => pure ()
      | 1, .error (.error _ message) =>
        unless (← message.toString) == "ordinary preparation consumer failure" do
          throwError "ordinary exception payload changed"
      | 2, .error (.internal id _) => unless id == unknown do throwError "internal identity changed"
      | 3, .error ex => unless ex.isInterrupt do throwError "native cancellation identity changed"
      | 4, .error ex => unless ex.isMaxHeartbeat do throwError "heartbeat exception changed"
      | _, _ => throwError "unexpected restoration outcome in mode {mode}"
      unless !(← sibling.mvarId!.isAssigned) && (← instantiateLevelMVars level) == level &&
          !(← getEnv).contains name do throwError "speculative state leaked"
      pass s!"exact-state-restoration-{mode}"
    finally modifyThe Term.State fun _ => oldTerm

run_elab do
  ownershipCases
  contextCases
  macroCases
  restorationCases
  IO.println "MATRIX COMPLETE"

end Leant2Tests.SketchPreparation
