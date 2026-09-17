import Lean
namespace Leant2Fold
universe u v
theorem fold_contract {α : Type u} {β : Type v}
    (R : List α → β → Prop) (base : β) (step : α → β → β)
    (hbase : R [] base)
    (hstep : ∀ x xs value, R xs value → R (x :: xs) (step x value)) :
    ∀ xs, R xs (xs.foldr step base) := by
  intro xs
  induction xs with
  | nil => exact hbase
  | cons x xs ih => exact hstep x xs _ ih

def certifiedRecursor {α : Type u} {β : Type v}
    (R : List α → β → Prop) (base : {b : β // R [] b})
    (step : (x : α) → (xs : List α) →
      {b : β // R xs b} → {b : β // R (x :: xs) b}) :
    (xs : List α) → {b : β // R xs b}
  | [] => base
  | x :: xs => step x xs (certifiedRecursor R base step xs)

def indexFold {α : Type u} (xs : List α) : Nat → Option α :=
  xs.foldr (fun x rec i => match i with
    | 0 => some x
    | k + 1 => rec k) (fun _ => none)

def indexReference {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => indexReference xs k

theorem indexFold_correct {α : Type u} (xs : List α) :
    ∀ i, indexFold xs i = indexReference xs i := by
  induction xs with
  | nil => intro i; rfl
  | cons x xs ih =>
    intro i
    cases i with
    | zero => rfl
    | succ k => exact ih k

theorem noUniversalValue : ((α : Type) → α) → False :=
  fun f => nomatch f Empty

theorem noUniformConversion : ((α β : Type) → α → β) → False :=
  fun f => nomatch f Unit Empty ()

#eval (List.range 6).map (indexFold [10, 20, 30])
#print axioms fold_contract
#print axioms certifiedRecursor
#print axioms indexFold
#print axioms indexFold_correct
#print axioms noUniversalValue
#print axioms noUniformConversion
#eval Lean.versionString
end Leant2Fold
