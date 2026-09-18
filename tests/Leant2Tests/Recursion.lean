import Leant2

/-! Structural recursion discovered from recursor metadata (gate G4, first
slice): no library provider knows these types, so a recursive candidate must
be built from the recursor. Behavioral contracts force genuine recursion. -/

inductive T where
  | leaf : T
  | node : T → T → T
  deriving DecidableEq

#leant2_check f : T → Nat where f T.leaf = 1 ∧ f (T.node T.leaf T.leaf) = 2 ∧ f (T.node (T.node T.leaf T.leaf) T.leaf) = 3

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
  deriving DecidableEq

#leant2_check f : MyList Nat → Nat where f MyList.nil = 0 ∧ f (MyList.cons 3 MyList.nil) = 1 ∧ f (MyList.cons 3 (MyList.cons 4 MyList.nil)) = 2

#leant2_check f : (∀ α β : Type, (α → β) → MyList α → MyList β) where f Nat Nat (· + 1) (MyList.cons 1 MyList.nil) = MyList.cons 2 MyList.nil

#leant2_check f : Nat → Nat → Nat where f 2 3 = 5 ∧ f 0 4 = 4 ∧ f 3 0 = 3
