import Lean
namespace Leant2Certificates
theorem noPolymorphicMap : ((A B : Type) → A → B) → False := by
  intro f
  exact Empty.elim (f Unit Empty ())
theorem safePruneAt {C I O : Type} (run : C → I → O)
    (completion : C → Prop) (pre : I → Prop)
    (contract over : I → O → Prop) (x : I) (hx : pre x)
    (sound : ∀ c, completion c → over x (run c x))
    (exclude : ∀ y, over x y → ¬ contract x y) :
    ¬ ∃ c, completion c ∧ ∀ z, pre z → contract z (run c z) := by
  intro h
  obtain ⟨c, hc, hspec⟩ := h
  exact exclude (run c x) (sound c hc) (hspec x hx)
theorem finiteValidation {I : Type} (samples : List I)
    (complete : ∀ i, i ∈ samples) (R : I → Prop)
    (checked : ∀ i, i ∈ samples → R i) : ∀ i, R i := by
  intro i
  exact checked i (complete i)
inductive Tree where
  | leaf : Tree
  | branch : Tree → Tree → Tree
noncomputable def countRec (t : Tree) : Nat :=
  Tree.rec 1 (fun _ _ left right => left + right) t
def countEq : Tree → Nat
  | .leaf => 1
  | .branch left right => countEq left + countEq right
theorem loweringCorrect (t : Tree) : countEq t = countRec t := by
  induction t with
  | leaf => rfl
  | branch left right ihl ihr => simp [countEq, countRec, ihl, ihr]
#print axioms noPolymorphicMap
#print axioms safePruneAt
#print axioms finiteValidation
#print axioms loweringCorrect
#eval countEq (.branch .leaf (.branch .leaf .leaf))
