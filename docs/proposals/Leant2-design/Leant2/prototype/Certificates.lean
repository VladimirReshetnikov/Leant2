import Lean

/-! Universal certificates for the exact finite grammar in experiments/cegis.py.
These proofs are written verification infrastructure, not synthesized proofs. -/
namespace Leant2Evidence

inductive Step where
  | nil
  | single
  | tail
  | append : Step → Step → Step
  deriving Repr, DecidableEq

def Step.eval {A : Type u} (s : Step) (head : A) (tailResult : List A) : List A :=
  match s with
  | .nil => []
  | .single => [head]
  | .tail => tailResult
  | .append left right => left.eval head tailResult ++ right.eval head tailResult

def Step.summary : Step → Nat × Nat
  | .nil => (0, 0)
  | .single => (0, 1)
  | .tail => (1, 0)
  | .append left right =>
      (left.summary.1 + right.summary.1, left.summary.2 + right.summary.2)

theorem Step.summary_sound {A : Type u} (s : Step) (head : A) (r : List A) :
    (s.eval head r).length = s.summary.1 * r.length + s.summary.2 := by
  induction s <;> simp_all [Step.eval, Step.summary, Nat.add_mul] <;> omega

def Step.run {A : Type u} (s : Step) : List A → List A
  | [] => []
  | x :: xs => s.eval x (s.run xs)

theorem Step.length_preserved {A : Type u} (s : Step)
    (a : s.summary.1 = 1) (b : s.summary.2 = 1) (xs : List A) :
    (s.run xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Step.run, Step.summary_sound, a, b, Nat.one_mul, ih]
    rfl

theorem Step.summary_necessary (s : Step)
    (h : ∀ xs : List Nat, (s.run xs).length = xs.length) :
    s.summary = (1, 1) := by
  have h1 := h [0]
  have h2 := h [0, 0]
  have b : s.summary.2 = 1 := by
    simpa [Step.run, Step.summary_sound] using h1
  simp [Step.run, Step.summary_sound, b] at h2
  have a : s.summary.1 = 1 := by omega
  exact Prod.ext a b

-- This is exactly the AST selected by the Python experiment.
def selectedStep : Step := Step.append Step.tail Step.single

theorem selected_correct {A : Type u} (xs : List A) :
    selectedStep.run xs = xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change selectedStep.run xs ++ [x] = (x :: xs).reverse
    rw [ih, List.reverse_cons]

#eval selectedStep.run [1, 2, 3, 4]
#print axioms Step.summary_sound
#print axioms Step.length_preserved
#print axioms Step.summary_necessary
#print axioms selected_correct
#eval Lean.versionString
end Leant2Evidence
