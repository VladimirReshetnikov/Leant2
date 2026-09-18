import Lean

universe u
namespace Leant2Certificates

-- Reference construction: this recursion was written by hand, not synthesized.
def certifiedAppend {α : Type u} (ys : List α) :
    (xs : List α) → {zs : List α // zs = xs ++ ys}
  | [] => ⟨ys, rfl⟩
  | x :: xs =>
    let tail := certifiedAppend ys xs
    ⟨x :: tail.val, congrArg (List.cons x) tail.property⟩

theorem certifiedAppend_correct {α : Type u} (xs ys : List α) :
    (certifiedAppend ys xs).val = xs ++ ys :=
  (certifiedAppend ys xs).property

-- This is a genuine refutation, not an interpretation of failed search.
theorem noUniversalChooser : ¬ Nonempty (∀ α : Type, α) := by
  intro existsChooser
  obtain ⟨choose⟩ := existsChooser
  exact (choose Empty).elim

-- A proof about EVERY completion of one partial program.
theorem prefixCannotComplete {α : Type u} (input fixedPart : List α)
    (tooLong : input.length < fixedPart.length) :
    ∀ suffix : List α, (fixedPart ++ suffix).length ≠ input.length := by
  intro suffix equality
  simp only [List.length_append] at equality
  omega

#print axioms certifiedAppend
#print axioms certifiedAppend_correct
#print axioms noUniversalChooser
#print axioms prefixCannotComplete
#eval Lean.versionString
end Leant2Certificates
