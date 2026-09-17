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
universe u v
inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)
def vectorMap {A : Type u} {B : Type v} (f : A → B) :
    {n : Nat} → Vec A n → Vec B n
  | _, .nil => by leant2_core
  | _, .cons x xs => by
    have mapped := vectorMap f xs
    leant2_core
def toList {A : Type u} : {n : Nat} → Vec A n → List A
  | _, .nil => []
  | _, .cons x xs => x :: toList xs
theorem vectorMap_nil {A : Type u} {B : Type v} (f : A → B) :
    vectorMap f .nil = .nil := rfl
theorem vectorMap_cons {A : Type u} {B : Type v} (f : A → B)
    {n : Nat} (x : A) (xs : Vec A n) :
    vectorMap f (.cons x xs) = .cons (f x) (vectorMap f xs) := rfl
#print axioms vectorMap
#print axioms vectorMap_nil
#print axioms vectorMap_cons
#eval toList (vectorMap (fun x : Nat => x + 1) (.cons 1 (.cons 2 .nil)))
end Leant2Prototype
