import Lean
open Lean Meta Elab Tactic
namespace Leant2Prototype
private def attempt (action : MetaM Bool) : MetaM Bool := do
  let saved ← saveState
  try
    if ← action then return true
  catch _ => pure ()
  saved.restore
  return false
private partial def search (fuel splits : Nat) (goals : List MVarId) : MetaM Bool := do
  match goals with
  | [] => return true
  | goal :: rest =>
    if ← goal.isAssigned then return ← search fuel splits rest
    if fuel == 0 then return false
    goal.withContext do
      let target ← whnf (← goal.getType)
      let context ← getLCtx
      let locals := context.getFVarIds.filter fun id =>
        !(context.get! id).isImplementationDetail
      if ← attempt do
        goal.refl
        search (fuel - 1) splits rest
      then return true
      for id in locals do
        if ← attempt do
          let value := mkFVar id
          if !(← isDefEq (← inferType value) target) then return false
          goal.assign value
          search (fuel - 1) splits rest
        then return true
      if target.isForall then
        if ← attempt do
          let (_, next) ← goal.intro1
          search (fuel - 1) splits (next :: rest)
        then return true
      if let .const name _ := target.getAppFn then
        if let .inductInfo info ← getConstInfo name then
          for ctor in info.ctors do
            if ← attempt do
              let value ← mkConstWithFreshMVarLevels ctor
              let next ← goal.apply value { newGoals := .all }
              search (fuel - 1) splits (next ++ rest)
            then return true
      for id in locals do
        if ← attempt do
          let next ← goal.apply (mkFVar id) { newGoals := .all }
          search (fuel - 1) splits (next ++ rest)
        then return true
      if splits > 0 then
        for id in locals do
          if ← attempt do
            let ty ← whnf (← inferType (mkFVar id))
            let .const name _ := ty.getAppFn | return false
            let .inductInfo _ ← getConstInfo name | return false
            let branches ← goal.cases id
            search (fuel - 1) (splits - 1)
              (branches.toList.map (·.mvarId) ++ rest)
          then return true
      return false
elab "leant2_core" : tactic => withMainContext do
  if ← search 32 2 (← getGoals) then setGoals []
  else throwError "Leant2 prototype: bounded search found no term"
universe u v w
def identity {A : Sort u} : A → A := by leant2_core
def compose {A : Sort u} {B : Sort v} {C : Sort w} :
    (B → C) → (A → B) → A → C := by leant2_core
def dependentApply {A : Sort u} {B : A → Sort v} :
    ((x : A) → B x) → (x : A) → B x := by leant2_core
def dependentPair {A : Type u} {B : A → Type v} :
    (a : A) → B a → Sigma B := by leant2_core
def higherRank {B : Type u} : (((A : Type) → A → A) → B) → B := by leant2_core
def swap {A : Type u} {B : Type v} : A × B → B × A := by leant2_core
def sumElim {A : Type u} {B : Type v} {C : Type w} :
    (A → C) → (B → C) → Sum A B → C := by leant2_core
inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)
def vectorHead {A : Type u} {n : Nat} : Vec A (n + 1) → A := by leant2_core
def vectorTail {A : Type u} {n : Nat} : Vec A (n + 1) → Vec A n := by leant2_core
inductive Choice where | first | second
inductive Good : Choice → Prop where | second : Good Choice.second
def coupledWitness : {c : Choice // Good c} := by leant2_core
example : coupledWitness.val = Choice.second := rfl
class Source (A : Type u) where
  value : A
def dictionary {A : Type u} : Source A → A := by leant2_core
theorem conjunction {P Q : Prop} : P ∧ Q → Q ∧ P := by leant2_core
theorem impossibleFunction : ¬ Nonempty ((A B : Type) → A → B) := by
  intro ⟨f⟩
  exact (f Unit Empty ()).elim
example : True := by
  fail_if_success have bad : False := by leant2_core
  exact True.intro
#print axioms identity
#print axioms compose
#print axioms dependentApply
#print axioms dependentPair
#print axioms higherRank
#print axioms swap
#print axioms sumElim
#print axioms vectorHead
#print axioms vectorTail
#print axioms coupledWitness
#print axioms dictionary
#print axioms conjunction
#print axioms impossibleFunction
#eval Lean.versionString
#eval identity 7
#eval compose (fun x : Nat => x + 1) (fun x : Nat => x * 2) 3
#eval (swap (11, 29)).1
#eval dictionary (Source.mk 29 : Source Nat)
end Leant2Prototype
