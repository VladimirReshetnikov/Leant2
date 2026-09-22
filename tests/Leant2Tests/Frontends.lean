import Leant2.Frontend.Term

namespace Leant2Tests.Frontends

open Lean Meta Elab Term Leant2

set_option leant2.budgetMs 5000
set_option linter.unusedVariables false

universe u v

def identity (A : Sort u) (x : A) : A := synth%
example (A : Sort u) (x : A) : identity A x = x := rfl

def dependent (I : Type u) (F : I → Type v) (i : I) (x : F i) : F i := synth%
example (I : Type u) (F : I → Type v) (i : I) (x : F i) :
    dependent I F i x = x := rfl

def applyLocal (A B : Type) (f : A → B) (a : A) : B := by leant2
example (A B : Type) (f : A → B) (a : A) : applyLocal A B f a = f a := rfl

theorem implication (p q : Prop) (hp : p) (hpq : p → q) : q := by leant2

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · leant2
  · exact hq

private def second {A : Type} (_x y : A) : A := y
-- A is unknown at the first argument; the later typed argument resolves it.
def delayed := second synth% (7 : Nat)
example : delayed = 7 := rfl
def delayedPair := (fun {A : Type} (x y : A) => (x, y)) synth% (7 : Nat)
example : Nat × Nat := delayedPair
example : delayedPair.2 = 7 := rfl

def terminalLet : { n : Nat // n = 37 } :=
  let kept : Nat := 37
  synth%
example : terminalLet.val = 37 := rfl

class HasValue (A : Type) where
  value : A

def localInstance (A : Type) (a : A) : A :=
  letI : HasValue A := ⟨a⟩
  synth%
example (A : Type) (a : A) : localInstance A a = a := rfl

-- User result-like names are ordinary declarations and must never be rebound.
def it : Nat := 91
def it1 : Nat := 92
def noAliasMutation : Nat := synth%
example : it = 91 ∧ it1 = 92 := by constructor <;> rfl

example : True := by
  fail_if_success have impossible : False := synth%
  fail_if_success have impossible : False := by leant2
  trivial

run_meta do
  for name in [``identity, ``dependent, ``applyLocal, ``implication, ``delayed, ``delayedPair,
      ``terminalLet, ``localInstance, ``noAliasMutation] do
    if (← collectAxioms name).contains ``sorryAx then
      throwError "frontend declaration contains sorry: {name}"

syntax (name := diagnosticProof) "diagnosticProof%" : term
@[term_elab diagnosticProof] def elabDiagnosticProof : TermElab := fun _ _ => do
  logError "test: a well-typed term with an error diagnostic is not a valid suggestion"
  return mkConst ``True.intro

elab "extraGoalAfterExact" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact True.intro))
  let extra ← mkFreshExprMVar (mkConst ``False)
  Lean.Elab.Tactic.appendGoals [extra.mvarId!]

run_elab do
  for bad in [← `(tactic| exact diagnosticProof%), ← `(tactic| extraGoalAfterExact)] do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let sibling ← mkFreshExprMVar (mkConst ``Nat)
    let .ok query ← Frontend.prepareLocalQuery (mkConst ``True)
      | throwError "suggestion test preparation failed"
    let remaining ← Lean.Elab.Tactic.run goal.mvarId! do
      Lean.Elab.Tactic.appendGoals [sibling.mvarId!]
      let initial ← Lean.Elab.Tactic.saveState
      let beforeMessages := (← getThe Core.State).messages.toList.length
      if ← Frontend.validatesSuggestion initial goal.mvarId! query bad then
        throwError "suggestion validation accepted errors or an extra obligation"
      unless !(← goal.mvarId!.isAssigned) && !(← sibling.mvarId!.isAssigned) &&
          (← getThe Core.State).messages.toList.length == beforeMessages do
        throwError "failed suggestion replay changed the caller state"
      unless (← Lean.Elab.Tactic.getUnsolvedGoals) == [goal.mvarId!, sibling.mvarId!] do
        throwError "failed suggestion replay changed sibling goals"
      goal.mvarId!.assign (mkConst ``True.intro)
      sibling.mvarId!.assign (mkNatLit 0)
      Lean.Elab.Tactic.setGoals []
    unless remaining.isEmpty do throwError "suggestion test did not close its own goals"

namespace ProjectAxiom

axiom untrusted : False

run_meta do
  unless (← sessionConstants).contains ``untrusted do
    throwError "project-axiom frontend regression has no axiom provider"

set_option leant2.budgetMs 1000 in
theorem rejectsProjectAxiom : True := by
  fail_if_success have rejected : False := synth%
  fail_if_success have rejected : False := by leant2
  trivial

run_meta do
  for axiomName in (← collectAxioms ``rejectsProjectAxiom) do
    unless axiomName ∈ [``propext, ``Classical.choice, ``Quot.sound] do
      throwError "frontend project-axiom refusal introduced {axiomName}"

end ProjectAxiom

end Leant2Tests.Frontends
