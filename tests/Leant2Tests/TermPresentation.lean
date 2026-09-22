import Leant2.Frontend.Presentation

/-! Compiler preparation from term elaboration retains the exact kernel value,
isolates caller state, and uses only branch-local rules in asynchronous proofs.
Known terms isolate publication behavior from synthesis scheduling. -/

open Lean Elab Term Meta Leant2

namespace TermPresentation

universe u v

inductive Tree (A : Type u) where
  | tip : A → Tree A
  | fork : Tree A → Tree A → Tree A

inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)

inductive AsyncTree where
  | tip : AsyncTree
  | fork : AsyncTree → AsyncTree → AsyncTree

inductive CancelTree where
  | tip : CancelTree
  | fork : CancelTree → CancelTree → CancelTree

mutual
  inductive LeftTree where
    | next : RightTree → LeftTree
  inductive RightTree where
    | tip : RightTree
    | next : LeftTree → RightTree
end

private def assertRule (recName : Name) : TermElabM Compiler.CSimp.Entry := do
  let some entry := (Compiler.CSimp.ext.getState (← getEnv)).map.find? recName
    | throwError "term presentation: missing compiler adapter for {recName}"
  unless Presentation.isAuxiliaryName entry.toDeclName &&
      Presentation.isAuxiliaryName entry.thmName do
    throwError "term presentation: adapter names would enter the provider inventory"
  let proof ← getConstInfo entry.thmName
  unless !proof.type.hasMVar && !(proof.value! (allowOpaque := true)).hasMVar &&
      !(proof.value! (allowOpaque := true)).hasSorry do
    throwError "term presentation: incomplete compiler equality"
  let axioms ← collectAxioms entry.thmName
  unless axioms.all Profile.standard.allowedAxioms.contains do
    throwError "term presentation: unaudited compiler equality"
  return entry

syntax (name := preparedTerm) "prepared% " term : term

@[term_elab preparedTerm] def elabPrepared : TermElab := fun stx expected => do
  let body := stx[1]
  let value ← withoutErrToSorry <| elabTermEnsuringType body expected
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasFVar || value.hasMVar || value.hasSorry then
    throwError "term presentation fixture must be closed and complete"
  let .ok accepted ← gate .strictConstructive value (← inferType value) none
    | throwError "term presentation: known term failed the strict kernel gate"
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let beforeTerm ← get
  let beforeMessages := (← getThe Core.State).messages.toList.length
  let beforeLevels ← getLevelNames
  withLocalDeclD `arg0 (mkConst ``Bool) fun ambient => do
    Presentation.prepareProgram accepted.program
    unless (← getLCtx).contains ambient.fvarId! do
      throwError "term presentation: preparation changed the caller's local context"
  unless (← getLevelNames) == beforeLevels &&
      (← get).pendingMVars == beforeTerm.pendingMVars &&
      (← get).letRecsToLift.length == beforeTerm.letRecsToLift.length &&
      (← getThe Core.State).messages.toList.length == beforeMessages do
    throwError "term presentation: preparation changed caller elaboration state"
  if ← pending.mvarId!.isAssigned then
    throwError "term presentation: preparation assigned a caller metavariable"
  -- The returned expression is precisely what the gate checked, not rendered
  -- syntax or the generated compiler implementation.
  return accepted.program

def leaves : (A : Type u) → Tree A → List A := prepared%
  fun A tree => Tree.rec (motive := fun _ => List A)
    (fun value => [value]) (fun _ _ left right => left ++ right) tree

example (A : Type u) (value : A) : leaves A (.tip value) = [value] := rfl
example (A : Type u) (left right : Tree A) :
    leaves A (.fork left right) = leaves A left ++ leaves A right := rfl

/-- info: [3, 7, 11] -/
#guard_msgs in
#eval leaves Nat (.fork (.tip 3) (.fork (.tip 7) (.tip 11)))

private def mapped : (A : Type u) → (B : Type v) → (A → B) →
    (n : Nat) → Vec A n → Vec B n := prepared%
  fun _A B f _n xs => Vec.rec (motive := fun n _ => Vec B n)
    .nil (fun x _rest ih => .cons (f x) ih) xs

example (A : Type u) (B : Type v) (f : A → B) : mapped A B f 0 .nil = .nil := rfl
example (A : Type u) (B : Type v) (f : A → B) (n : Nat) (x : A) (xs : Vec A n) :
    mapped A B f (n + 1) (.cons x xs) = .cons (f x) (mapped A B f n xs) := rfl

/-- info: true -/
#guard_msgs in
#eval match mapped Nat Bool (· == 4) 2 (.cons 2 (.cons 4 .nil)) with
  | .cons false (.cons true .nil) => true
  | _ => false

run_meta do
  TermElabM.run' do
    for recName in [``Tree.rec, ``Vec.rec] do
      let entry ← assertRule recName
      let count := (← getEnv).constants.map₂.toList.length
      unless ← Presentation.ensureRecursorTerm recName do
        throwError "term presentation: repeated preparation failed"
      unless (← getEnv).constants.map₂.toList.length == count &&
          (← assertRule recName).thmName == entry.thmName do
        throwError "term presentation: current-environment cache was not reused"

elab "prepared_async%" : term => do
  let some declPrefix := (← getEnv).asyncPrefix?
    | throwError "term presentation: asynchronous fixture did not enter an async branch"
  unless ← Presentation.ensureRecursorTerm ``AsyncTree.rec do
    throwError "term presentation: asynchronous preparation failed"
  let entry ← assertRule ``AsyncTree.rec
  unless declPrefix.isPrefixOf (privateToUserName entry.toDeclName.eraseMacroScopes) &&
      declPrefix.isPrefixOf (privateToUserName entry.thmName.eraseMacroScopes) do
    throwError "term presentation: asynchronous adapter escaped the declaration prefix"
  let count := (← getEnv).constants.map₂.toList.length
  unless ← Presentation.ensureRecursorTerm ``AsyncTree.rec do
    throwError "term presentation: asynchronous cache lookup failed"
  unless (← getEnv).constants.map₂.toList.length == count do
    throwError "term presentation: asynchronous cache lookup leaked a duplicate adapter"
  return mkConst ``True.intro

set_option Elab.async true in
theorem asyncPrepared : True := prepared_async%

-- Force the asynchronous theorem body before inspecting the main environment.
run_meta do
  discard <| collectAxioms ``asyncPrepared
  if (Compiler.CSimp.ext.getState (← getEnv)).map.contains ``AsyncTree.rec then
    throwError "term presentation: branch-local compiler rule escaped to the main environment"

run_meta do
  TermElabM.run' do
    let count := (← getEnv).constants.map₂.toList.length
    let messages := (← getThe Core.State).messages.toList.length
    let pending ← mkFreshExprMVar (mkConst ``Nat)
    if ← Presentation.ensureRecursorTerm ``LeftTree.rec then
      throwError "term presentation: mutually recursive adapter unexpectedly succeeded"
    unless (← getEnv).constants.map₂.toList.length == count &&
        (← getThe Core.State).messages.toList.length == messages do
      throwError "term presentation: unsupported adapter leaked state"
    if (← pending.mvarId!.isAssigned) ||
        (Compiler.CSimp.ext.getState (← getEnv)).map.contains ``LeftTree.rec then
      throwError "term presentation: unsupported adapter committed work"

private def observeAll (act : TermElabM α) : TermElabM (Except Exception α) := do
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  try return .ok (← act)
  catch ex => return .error ex

-- Real cancellation must propagate after restoration, never become the
-- unsupported/noncomputable Boolean fallback.
run_meta do
  TermElabM.run' do
    let count := (← getEnv).constants.map₂.toList.length
    let messages := (← getThe Core.State).messages.toList.length
    let pending ← mkFreshExprMVar (mkConst ``Nat)
    let token ← IO.CancelToken.new
    token.set
    let result ← observeAll <| withTheReader Core.Context
      (fun ctx => { ctx with cancelTk? := some token }) do
        Presentation.ensureRecursorTerm ``CancelTree.rec
    match result with
    | .error ex => unless ex.isInterrupt do throw ex
    | .ok _ => throwError "term presentation: cancellation was swallowed"
    unless (← getEnv).constants.map₂.toList.length == count &&
        (← getThe Core.State).messages.toList.length == messages &&
        !(← pending.mvarId!.isAssigned) do
      throwError "term presentation: cancellation leaked speculative state"
    if (Compiler.CSimp.ext.getState (← getEnv)).map.contains ``CancelTree.rec then
      throwError "term presentation: cancelled adapter was registered"

end TermPresentation
