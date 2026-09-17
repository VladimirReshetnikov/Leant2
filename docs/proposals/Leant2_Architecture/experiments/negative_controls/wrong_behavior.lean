import Lean
theorem wrong_behavior : (fun n : Nat => n) 0 = 1 := by rfl
