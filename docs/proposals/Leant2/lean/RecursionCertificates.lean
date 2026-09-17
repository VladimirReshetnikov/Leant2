import Lean

/-! These recursion schemes are supplied, not invented by `leant2_core`.
The affine-fold coefficients are selected by experiments/search_models.py.
The universal theorem below is stronger than its finite test corpus. -/

namespace RecursionCertificates
universe u v

inductive MapRel {A : Type u} {B : Type v} (f : A → B) : List A → List B → Prop where
  | nil : MapRel f [] []
  | cons {x : A} {xs : List A} {ys : List B} :
      MapRel f xs ys → MapRel f (x :: xs) (f x :: ys)

def certifiedMap {A : Type u} {B : Type v} (f : A → B) :
    (xs : List A) → { ys : List B // MapRel f xs ys }
  | [] => ⟨[], .nil⟩
  | x :: xs =>
      let tail := certifiedMap f xs
      ⟨f x :: tail.val, .cons tail.property⟩

def affineFold (base element accumulator bias : Nat) : List Nat → Nat
  | [] => base
  | x :: xs => element * x + accumulator * affineFold base element accumulator bias xs + bias

theorem sumCorrect (xs : List Nat) : affineFold 0 1 1 0 xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [affineFold, ih]

theorem notPolyChoice : (∀ A : Type, A) → False := by
  intro choose
  exact nomatch choose Empty

#eval affineFold 0 1 1 0 [2, 5, 9]
#eval (certifiedMap (fun x : Nat => x + 1) [2, 5, 9]).val

open Lean in
run_cmd do
  let names := #[``certifiedMap, ``affineFold, ``sumCorrect, ``notPolyChoice]
  for name in names do
    let axioms ← collectAxioms name
    logInfo m!"AXIOMS {name}: {axioms}"
    unless axioms.all (fun ax => #[``propext, ``Quot.sound, ``Classical.choice].contains ax) do
      throwError "{name}: unexpected axioms {axioms}"
  logInfo "LEANT2_RECURSION_AUDIT: 4 declarations; standard-axiom audit passed"

end RecursionCertificates
