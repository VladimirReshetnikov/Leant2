import Leant2

/-! Session axioms as providers, instance arguments determined by siblings,
and universe-polymorphic Church encodings (from Leant's provider and Church
fixtures). -/

namespace FiveBinder
axiom Five : Type → Type → Type → Type → Type → Type
axiom Token : Type
class Choice (one two three four five : Type 1) : Prop where witness : True
instance : Choice (∀ A : Type, A → A) (∀ B : Type, B → B → B) (∀ C : Type, C → C → C → C)
    (∀ D : Type, D → D → D → D → D) (∀ E : Type, E → E → E → E → E → E) := ⟨True.intro⟩
axiom chosen {one two three four five : Type 1} [Choice one two three four five] : Token
end FiveBinder

#leant2_check FiveBinder.Token
#leant2_check (∀ A B C D E : Type, (∀ a b c d e : Type, FiveBinder.Five a b c d e) → FiveBinder.Five E D C B A)

namespace Demo
axiom Seed : Type
axiom seedValue : Seed
axiom Token : Type
class C (a : Type) : Prop where witness : True
instance : C Nat := ⟨True.intro⟩
axiom global {a : Type} [C a] : Token
inductive A1 where | mk
inductive Good where | mk
instance : C Good := ⟨True.intro⟩
end Demo

#leant2_check Demo.Seed
#leant2_check (Demo.Seed → Demo.Seed)
#leant2_check (Nat → Demo.Token)
#leant2_check (Demo.A1 → Demo.Good → Demo.Token)

universe u v w
abbrev Church.Bool := ∀ e : Type u, e → e → e
abbrev Church.Pair (a : Type u) (b : Type v) := ∀ e : Type w, (a → b → e) → e
abbrev Church.List (a : Type u) := ∀ e : Type v, (a → e → e) → e → e
abbrev Church.Maybe (a : Type u) := ∀ e : Type v, e → (a → e) → e

#leant2_check Church.Bool
#leant2_check (∀ a b : Type _, Church.Pair a b → a)
#leant2_check (∀ a : Type _, Church.List a → Church.Maybe (Church.Pair a (Church.List a)))
#leant2_check (∀ a b : Type _, (a → b) → Church.List a → Church.List b)
#leant2_check (∀ a : Type _, a → Church.List a → a)
#leant2_check (∀ F : Type 1 → Type 1, (∀ a : Type 1, F a) → F (∀ b : Type, b → b))

namespace ChurchLayered
axiom Seed : Type
axiom seed : Seed
axiom G2 : Type 1 → Type 1 → Type 1
axiom maker2 : Seed → ∀ a : Type 1, a → Seed → ∀ b : Type 1, b → G2 a b
end ChurchLayered

#leant2_check (ChurchLayered.G2 (∀ a : Type, a → a) (∀ a : Type, a → a → a))
