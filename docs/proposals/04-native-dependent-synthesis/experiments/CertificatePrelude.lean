import Mathlib
namespace Leant2Affine

def affine (c a b d : Nat) : List Nat → Nat
  | [] => c
  | x :: xs => a * x + b * affine c a b d xs + d

/-- Inductive summary certificate for a whole (unbounded) family of lists. -/
theorem certify {c a b d A B C : Nat}
    (h0 : c = C) (ha : a = A) (hba : b * A = A) (hbb : b * B = B)
    (hc : b * C + d = B + C) :
    ∀ xs : List Nat, affine c a b d xs = A * xs.sum + B * xs.length + C := by
  subst a
  intro xs
  induction xs with
  | nil => simp [affine, h0]
  | cons x xs ih =>
    simp only [affine, ih, List.sum_cons, List.length_cons,
      Nat.mul_add, ← Nat.mul_assoc, hba, hbb, Nat.mul_one]
    omega

#print axioms certify
