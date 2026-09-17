import Lean

open Lean Meta Elab Tactic
namespace Leant2Pilot
private def splitHeads : List Name :=
  [``Prod, ``Sigma, ``Subtype, ``And, ``Or, ``Sum, ``Option, ``Bool, ``Fin]
partial def search (fuel : Nat) (goals : List MVarId) : MetaM Bool := do
  let goals ← goals.filterM fun g => return !(← g.isAssigned)
  if goals.isEmpty then return true
  if fuel == 0 then return false
  let goal := goals.head!
  let rest := goals.tail!
  goal.withContext do
    let initial ← saveState
    try
      goal.refl
      if ← search (fuel - 1) rest then return true
    catch _ => pure ()
    initial.restore
    let target ← whnf (← goal.getType)
    if target.isForall then
      try
        let (_, body) ← goal.intro1
        if ← search (fuel - 1) (body :: rest) then return true
      catch _ => pure ()
      initial.restore
    let localDecls := (← getLCtx).foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push decl
    for decl in localDecls do
      try
        let premises ← goal.apply (mkFVar decl.fvarId) { newGoals := .all }
        if ← search (fuel - 1) (premises ++ rest) then return true
      catch _ => pure ()
      initial.restore
    let target ← whnf (← goal.getType)
    if let .const head _ := target.getAppFn then
      if let some (.inductInfo info) := (← getEnv).find? head then
        for ctor in info.ctors do
          try
            let term ← mkConstWithFreshMVarLevels ctor
            let premises ← goal.apply term { newGoals := .all }
            if ← search (fuel - 1) (premises ++ rest) then return true
          catch _ => pure ()
          initial.restore
    for decl in localDecls do
      let ty ← whnf decl.type
      if let .const head _ := ty.getAppFn then
        if splitHeads.contains head then
          try
            let branches ← goal.cases decl.fvarId
            let premises := branches.toList.map (·.mvarId)
            if ← search (fuel - 1) (premises ++ rest) then return true
          catch _ => pure ()
          initial.restore
    return false
elab "leant2_pilot" : tactic => liftMetaTactic fun goal => do
  unless ← search 24 [goal] do
    throwError "Leant2 pilot: no solution within the bounded grammar"
  return []
universe u v w
def identity (α : Sort u) : α → α := by leant2_pilot
def composition (α : Sort u) (β : Sort v) (γ : Sort w) :
    (β → γ) → (α → β) → α → γ := by leant2_pilot
def sCombinator (α : Sort u) (β : Sort v) (γ : Sort w) :
    (α → β → γ) → (α → β) → α → γ := by leant2_pilot
def pairSwap (α : Type u) (β : Type v) : α × β → β × α := by leant2_pilot
def dependentApply (α : Sort u) (β : α → Sort v) :
    ((x : α) → β x) → (x : α) → β x := by leant2_pilot
def dependentPair (α : Type u) (β : α → Type v) :
    (x : α) → β x → Sigma β := by leant2_pilot
def higherRank : ((α : Type) → α → α) → (β : Type) → β → β := by
  leant2_pilot
def rankNConsumer (β : Type v) (k : ((α : Type u) → α → α) → β) : β := by
  leant2_pilot
def indexedWitness : Sigma (fun n : Nat => Fin (n + 1)) := by leant2_pilot
def constrainedBool : {b : Bool // b = true} := by leant2_pilot
def constrainedNat : {n : Nat // n = 2} := by leant2_pilot
def sumSwap (α : Type u) (β : Type v) : Sum α β → Sum β α := by
  leant2_pilot
theorem modusPonens (P Q : Prop) : (P → Q) → P → Q := by leant2_pilot
theorem disjunctionSwap (P Q : Prop) : P ∨ Q → Q ∨ P := by leant2_pilot
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
def Vec.map (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (Vec.map f xs)
def Vec.zip : Vec α n → Vec β n → Vec (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (Vec.zip xs ys)
def reverseAux {α : Type u} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => reverseAux xs (x :: acc)
theorem reverseAux_spec {α : Type u} (xs acc : List α) :
    reverseAux xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [reverseAux, ih, List.reverse_cons, List.append_assoc]
example : (α : Sort u) → α → α := identity
example : (α : Sort u) → (β : Sort v) → (γ : Sort w) →
    (β → γ) → (α → β) → α → γ := composition
example (α : Type u) (β : Type v) : α × β → β × α := pairSwap α β
example : constrainedBool.val = true := constrainedBool.property
example : constrainedNat.val = 2 := constrainedNat.property
example : pairSwap Nat Bool (7, true) = (true, 7) := rfl
example : reverseAux [1, 2, 3] [] = [3, 2, 1] := rfl
example (α β : Type) : True := by
  fail_if_success have : α → β := by leant2_pilot
  trivial
example : True := by
  fail_if_success have : False := by leant2_pilot
  trivial
#print axioms identity
#print axioms composition
#print axioms sCombinator
#print axioms pairSwap
#print axioms dependentApply
#print axioms dependentPair
#print axioms higherRank
#print axioms rankNConsumer
#print axioms indexedWitness
#print axioms constrainedBool
#print axioms constrainedNat
#print axioms sumSwap
#print axioms modusPonens
#print axioms disjunctionSwap
#print axioms Vec.map
#print axioms Vec.zip
#print axioms reverseAux
#print axioms reverseAux_spec
#eval Lean.versionString
#eval constrainedNat.val
#eval pairSwap Nat Bool (7, true)
