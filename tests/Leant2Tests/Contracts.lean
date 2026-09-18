import Leant2

/-! Behavioral contracts and type invention: kernel-evaluated residuals,
accumulator instantiation on Church encodings, universe-flexible frontier
types, and upfront refutation of unsatisfiable contracts. -/

/-! Church reverse needs `xs (R -> R) ...`: the list is folded at the
accumulator type of the goal (rule 7a). -/
abbrev CList (A : Type) := ∀ R : Type, (A → R → R) → R → R
def CList.enc {A : Type} (xs : List A) : CList A := fun _ step zero => xs.foldr step zero
def CList.dec {A : Type} (xs : CList A) : List A := xs (List A) List.cons []

#leant2_check f : (∀ A : Type, CList A → CList A)
  where CList.dec (f Nat (CList.enc [1, 2, 3])) = [3, 2, 1] ∧ CList.dec (f Nat (CList.enc [])) = []

/-! Sorts other than `Type` are inhabited from the frontier (`PUnit.{u}`);
type formers are filled through introduction. -/
#leant2_check f : (∀ A : Type, (Type 1 → A) → A) where @f Nat (fun _ => 37) = 37
#leant2_check f : (∀ A : Type, (Prop → A) → A) where @f Nat (fun _ => 37) = 37
#leant2_check f : (∀ A : Type, (∀ _F : Type → Type, A) → (∀ _F : Type, A) → A × A)
  where @f Nat (fun _ => 7) (fun _ => 9) = (7, 9)

/-! A contract no program satisfies is refuted before any search. -/
#leant2_none f : (∀ A B : Type, (A → B) → A → A → B × B) where False
#leant2_none f : (∀ A : Type, A → A) where (∀ n : Nat, f Nat n + 0 = n) ∧ False

/-! A quantified contract is proved by simplification, not by evaluation. -/
#leant2_check f : (∀ A : Type, A → A) where ∀ n : Nat, f Nat n + 0 = n

/-! Class methods are reached by projection, and an unused instance binder
is not a ranking defect. -/
class Ctx.C (α : Type) where out : Nat
#leant2_check f : (∀ (α : Type), [Ctx.C α] → List Nat)
  where (@f Nat (@Ctx.C.mk Nat 7) = [7]) ∧ (@f Nat (@Ctx.C.mk Nat 11) = [11])
#leant2_check f : (∀ (α : Type), [Ctx.C α] → α → α)
  where (@f Nat (@Ctx.C.mk Nat 7) 37 = 37) ∧ (@f Bool (@Ctx.C.mk Bool 11) true = true)
