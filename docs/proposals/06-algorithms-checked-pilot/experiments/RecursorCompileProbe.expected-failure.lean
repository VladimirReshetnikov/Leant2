import Lean
inductive PilotTree where
  | leaf : PilotTree
  | branch : PilotTree → PilotTree → PilotTree
def countLeaves (t : PilotTree) : Nat :=
  PilotTree.rec 1 (fun _ _ left right => left + right) t
