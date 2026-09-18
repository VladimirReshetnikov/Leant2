import Leant2

/-! Fixtures from Leant's `synth-basic` and `synth-manual` transcripts. -/

#leant2_check (A × (B ⊕ C) → (A × B) ⊕ (A × C))
#leant2_check ((A → B → C) → (A → B) → A → C)
#leant2_check (a → a → a)
#leant2_check (Nat → Nat)
#leant2_check (∀ p q : Prop, (p ↔ q) → ¬p → ¬q)
#leant2_check (((A → B) → A) → (A → A))
#leant2_check ((a → b → c) → b → a → c)
#leant2_check ((b → c) → (a → b) → a → c)
#leant2_check ((A × B → C) → A → B → C)
#leant2_check (((A × B) × C) → A × (B × C))
#leant2_check (∀ p q : Prop, ¬(p ∨ q) ↔ ¬p ∧ ¬q)
#leant2_check (∀ p q : Prop, (p ↔ q) → (q ↔ p))
#leant2_check (∀ p : Prop, (p ↔ ¬p) → False)
#leant2_check ((S → A) → (A → S → B) → S → B)
#leant2_check (∀ a b : Type, Option a → (a → Option b) → Option b)

/-! Classical candidates. -/
#leant2_check (((A → B) → A) → A)
#leant2_check (∀ p : Prop, ¬¬p → p)

/-! Behavioral assertions. -/
#leant2_check f : (∀ A : Type, A → A → A) where f Nat 11 29 = 29 ∧ f Bool true false = false
#leant2_none f : (∀ A : Type, A → A) where False

/-! Refutations. -/
#leant2_none (∀ a b : Type, a → b)
#leant2_none (∀ a b : Type, Option a → b)
