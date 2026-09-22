-- Separate Lean-only reference process. Never import into synthesis.
import Lean

def offsetContract (f : List Nat → Nat) : Prop :=
  f [] = 1 ∧ f [2] = 3 ∧ f [2, 3] = 6 ∧ f [0, 4, 0] = 5

def reference : List Nat → Nat := List.foldr Nat.add 1
def wrongSeed : List Nat → Nat := List.foldr Nat.add 0
def wrongStep : List Nat → Nat := List.foldr (fun _ acc => acc) 1

example : offsetContract reference := by
  unfold offsetContract
  decide
example : ¬ offsetContract wrongSeed := by
  unfold offsetContract
  decide
example : ¬ offsetContract wrongStep := by
  unfold offsetContract
  decide
example : wrongStep [] = 1 ∧ wrongStep [2] ≠ 3 := by decide
example : reference [5, 8] = 14 ∧ reference [9, 1, 2, 3] = 16 := by decide
example : ∀ (A : Type) (x : A), (fun (A : Type) (x : A) => x) A x = x := by
  intro A x
  rfl

#eval "SKETCH_REFERENCES_OK"
