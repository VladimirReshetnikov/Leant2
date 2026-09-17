import Lean
namespace Leant2Certificate
universe u
def specReverse {A : Type u} : List A → List A
  | [] => []
  | x :: xs => specReverse xs ++ [x]
def generatedReverse {A : Type u} (xs : List A) : List A :=
  xs.foldl (fun acc x => [x] ++ acc) []
theorem foldInvariant {A : Type u} (xs acc : List A) :
    xs.foldl (fun acc x => [x] ++ acc) acc = specReverse xs ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change xs.foldl (fun acc x => [x] ++ acc) (x :: acc) =
      (specReverse xs ++ [x]) ++ acc
    rw [ih, List.append_assoc, List.cons_append, List.nil_append]
theorem generatedReverse_correct {A : Type u} (xs : List A) :
    generatedReverse xs = specReverse xs := by
  unfold generatedReverse
  rw [foldInvariant, List.append_nil]
example : generatedReverse [1, 2, 3] = [3, 2, 1] := rfl
#print axioms generatedReverse
#print axioms foldInvariant
#print axioms generatedReverse_correct
#eval generatedReverse [1, 2, 3]
end Leant2Certificate
