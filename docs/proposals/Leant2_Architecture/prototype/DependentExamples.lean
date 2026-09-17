import NativeCore
-- To check this file locally, first compile NativeCore.lean and replace this
-- comment by `import NativeCore`, or use Combined.lean, which is self-contained.
-- The remote experiment concatenates the two source files, keeping import Lean.
open Lean Meta Elab Tactic
namespace Leant2Prototype
universe u v
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)
def vcons {α : Type u} {n : Nat} : α → Vec α n → Vec α (n + 1) := by
  leant2_core
def vecMap {α : Type u} {β : Type v} (f : α → β) {n : Nat}
    (xs : Vec α n) : Vec β n :=
  match xs with
  | .nil => by leant2_core
  | .cons a xs => by
    have ih := vecMap f xs
    leant2_core
def vecToList {α : Type u} {n : Nat} : Vec α n → List α
  | .nil => []
  | .cons a xs => a :: vecToList xs
theorem vecMap_behavior {α : Type u} {β : Type v} (f : α → β) {n : Nat}
    (xs : Vec α n) : vecToList (vecMap f xs) = (vecToList xs).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [vecMap, vecToList, ih]
def transport {α : Sort u} (β : α → Sort v) {a b : α}
    (h : a = b) (x : β a) : β b := by
  cases h
  leant2_core
def inheritedDefault {α : Type u} [Inhabited α] : α := by
  leant2_with Inhabited.default
structure Payload where
  value : Nat
def chooseRight (left right : Payload) : {p : Payload // p.value = right.value} := by
  leant2_core
def rankTwoSpec :
    {h : ((α : Type) → α → α) → Nat → Nat // ∀ f n, h f n = f Nat n} := by
  leant2_core
def higherRank : (((α : Type) → α → α) → Nat) → Nat := by leant2_core
theorem noPolyCast : ((α : Type) → (β : Type) → α → β) → False := by
  intro f
  exact Empty.elim (f Unit Empty ())
#print axioms vcons
#print axioms vecMap
#print axioms vecMap_behavior
#print axioms transport
#print axioms inheritedDefault
#print axioms chooseRight
#print axioms rankTwoSpec
#print axioms higherRank
#print axioms noPolyCast
#eval (chooseRight ⟨2⟩ ⟨9⟩).val.value
#eval vecToList (vecMap (fun n => n + 1) (.cons 2 (.cons 3 .nil)))
end Leant2Prototype
