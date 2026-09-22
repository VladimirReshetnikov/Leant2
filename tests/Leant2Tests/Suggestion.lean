import Leant2.Frontend.Suggestion
import Leant2.Frontend.Presentation

/-! Completed suggestion replay checks native recursive terms at the original
type and restores all speculative elaboration state. Known terms isolate this
validation boundary from synthesis scheduling. -/

open Lean Meta Elab Term Leant2 Leant2.Frontend

namespace Suggestion

universe u v
set_option linter.unusedVariables false

inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)

private def assertStable (query : LocalQuery) (source : TSyntax `tactic)
    (expected := true) : TermElabM Unit := do
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let beforeCore ← getThe Core.State
  let beforeTerm ← getThe Term.State
  let beforeLocals := (← getLCtx).getFVarIds
  let result ← validateCompletedSuggestion query source
  unless result == expected do
    throwError "completed suggestion validation returned {result}, expected {expected}"
  unless (← getEnv).constants.map₂.toList.map Prod.fst ==
        beforeCore.env.constants.map₂.toList.map Prod.fst &&
      (← getThe Core.State).messages.toList.length == beforeCore.messages.toList.length &&
      (← getThe Term.State).pendingMVars == beforeTerm.pendingMVars &&
      (← getThe Term.State).levelNames == beforeTerm.levelNames &&
      (← getThe Term.State).letRecsToLift.length == beforeTerm.letRecsToLift.length &&
      (← getLCtx).getFVarIds == beforeLocals && !(← pending.mvarId!.isAssigned) do
    throwError "completed suggestion validation changed caller state"

private def checkValue (value : Expr) : TermElabM Unit := do
  let .ok query ← prepareLocalQuery (← inferType value) | throwError "invalid query"
  let termSyntax ← Presentation.programSyntax value
  assertStable query (← `(tactic| exact $termSyntax))

elab "validated% " value:term : term <= expected => do
  let value ← elabTermEnsuringType value expected
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  checkValue value
  Presentation.prepareProgram value
  return value

def closedMap : ∀ (A : Type u) (B : Type v), (A → B) → ∀ n, Vec A n → Vec B n :=
  validated% (fun A B f n xs => @Vec.rec A (fun n _ => Vec B n)
    .nil (fun {n} a _ ih => .cons (f a) ih) n xs)

example (A : Type u) (B : Type v) (f : A → B) : closedMap A B f 0 .nil = .nil := rfl
example (A : Type u) (B : Type v) (f : A → B) (n : Nat) (a : A) (xs : Vec A n) :
    closedMap A B f (n + 1) (.cons a xs) = .cons (f a) (closedMap A B f n xs) := rfl

def localMap (A : Type u) (B : Type v) (f : A → B) (n : Nat) (xs : Vec A n) : Vec B n :=
  validated% (@Vec.rec A (fun n _ => Vec B n) .nil
    (fun {n} a _ ih => .cons (f a) ih) n xs)

example (A : Type u) (B : Type v) (f : A → B) (n : Nat) (a : A) (xs : Vec A n) :
    localMap A B f (n + 1) (.cons a xs) = .cons (f a) (localMap A B f n xs) := rfl

private def privateMap (A : Type u) (B : Type v) (f : A → B) (n : Nat) (xs : Vec A n) : Vec B n :=
  validated% (@Vec.rec A (fun n _ => Vec B n) .nil
    (fun {n} a _ ih => .cons (f a) ih) n xs)

def letMap (A : Type u) (B : Type v) (f : A → B) (n : Nat) (xs : Vec A n) : Vec B n :=
  let kept : A → B := f
  validated% (@Vec.rec A (fun n _ => Vec B n) .nil
    (fun {n} a _ ih => .cons (kept a) ih) n xs)

def instanceMap (A : Type u) (B : Type v) [Inhabited B] (n : Nat) (xs : Vec A n) : Vec B n :=
  validated% (@Vec.rec A (fun n _ => Vec B n) .nil
    (fun {n} _ _ ih => .cons default ih) n xs)

-- The kernel term returned by the fixture remains the original recursor.
#guard (match closedMap Nat Bool (· == 0) 2 (.cons 0 (.cons 3 .nil)) with
  | .cons a (.cons b .nil) => a && !b)
#guard (match privateMap Bool Nat (fun b => if b then 7 else 3) 2 (.cons false (.cons true .nil)) with
  | .cons a (.cons b .nil) => a == 3 && b == 7)
#guard (match letMap Nat Nat (· + 1) 2 (.cons 3 (.cons 7 .nil)) with
  | .cons a (.cons b .nil) => a == 4 && b == 8)
#guard (match instanceMap Nat Bool 2 (.cons 4 (.cons 8 .nil)) with
  | .cons a (.cons b .nil) => !a && !b)

elab "validated_async%" : term => do
  unless (← getEnv).asyncPrefix?.isSome do
    throwError "suggestion fixture must execute in an asynchronous declaration"
  let value ← elabTerm (← `(term| fun (xs : List Nat) => List.rec (motive := fun _ => Nat) (0 : Nat)
    (fun x _ ih => x + ih) xs)) none
  synthesizeSyntheticMVarsNoPostponing
  checkValue (← instantiateMVars value)
  return mkConst ``True.intro

set_option Elab.async true in
theorem asyncValidation : True := validated_async%

run_meta do
  unless (← collectAxioms ``asyncValidation).isEmpty do
    throwError "async suggestion fixture added axioms"

-- Hidden values of nondependent haves need not be well typed. Like LocalQuery,
-- the validator must treat them as parameters and never copy their value.
run_elab do
  withLetDecl `opaqueHave (mkConst ``Nat) (mkConst ``True.intro) (nondep := true) fun h => do
    let .ok query ← prepareLocalQuery (mkConst ``Nat) | throwError "invalid have query"
    assertStable query (← `(tactic| exact $(mkIdent `opaqueHave)))

-- A genuine let remains definitionally available even if it is absent from
-- the original result type and is used only inside the suggested recursion.
run_elab do
  withLetDecl `kept (mkConst ``Nat) (mkNatLit 37) fun _ => do
    let .ok query ← prepareLocalQuery (← elabType (← `(term| List Nat → Nat)))
      | throwError "invalid let query"
    assertStable query (← `(tactic| exact fun xs =>
      let rec go : List Nat → Nat
        | [] => $(mkIdent `kept)
        | _ :: tail => go tail
      go xs))

axiom forbidden : True
elab "diagnostic%" : term => do
  logError "deliberate test diagnostic"
  return mkConst ``True.intro

run_elab do
  let .ok query ← prepareLocalQuery (mkConst ``True) | throwError "invalid negative query"
  for source in [← `(tactic| exact (0 : Nat)), ← `(tactic| exact sorry),
      ← `(tactic| exact forbidden), ← `(tactic| exact diagnostic%),
      ← `(tactic| exact (by skip))] do
    assertStable query source false
  assertStable query (← `(tactic| exact True.intro))

-- A pending native let-rec in the caller's elaborator must not be consumed by
-- validation of another term. Discard only this fixture's own pending work.
run_elab do
  let beforeCore ← getThe Core.State
  let beforeMeta ← getThe Meta.State
  let beforeTerm ← getThe Term.State
  try
    discard <| elabTerm (← `(term| let rec callerLoop : Nat → Nat
      | 0 => 0
      | n + 1 => callerLoop n
      callerLoop)) none
    unless !(← getThe Term.State).letRecsToLift.isEmpty do
      throwError "pending-let-rec fixture did not create pending work"
    let .ok query ← prepareLocalQuery (mkConst ``True) | throwError "invalid pending query"
    assertStable query (← `(tactic| exact True.intro))
  finally
    modifyThe Term.State fun _ => beforeTerm
    modifyThe Meta.State fun _ => beforeMeta
    modifyThe Core.State fun _ => beforeCore

elab "interrupting%" : term => do
  let name ← mkAuxName `_interrupt_test
  addDecl (.axiomDecl { name, levelParams := [], type := mkConst ``True, isUnsafe := false })
  logInfo "speculative diagnostic"
  throwInterruptException

run_elab do
  let .ok query ← prepareLocalQuery (mkConst ``True) | throwError "invalid interrupt query"
  let beforeCore ← getThe Core.State
  let beforeTerm ← getThe Term.State
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  let propagated ← try
    discard <| validateCompletedSuggestion query (← `(tactic| exact interrupting%))
    pure false
  catch ex => pure ex.isInterrupt
  unless propagated do throwError "suggestion validation swallowed cancellation"
  unless (← getEnv).constants.map₂.toList.map Prod.fst ==
        beforeCore.env.constants.map₂.toList.map Prod.fst &&
      (← getThe Core.State).messages.toList.length == beforeCore.messages.toList.length &&
      (← getThe Term.State).pendingMVars == beforeTerm.pendingMVars &&
      !(← pending.mvarId!.isAssigned) do
    throwError "cancelled suggestion validation leaked state"

end Suggestion
