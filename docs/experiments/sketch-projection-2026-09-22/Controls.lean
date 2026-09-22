import Lean

/-!
UNVALIDATED DRAFT: independent Lean-only controls, never synthesis providers.
Run in a separate fresh process. A pass verifies the original finite oracle,
known witness, and three separating wrong controls; it proves no search result.
-/

set_option linter.unusedVariables false
namespace BehaviorPartial
universe u v
abbrev CList (A : Type u) := ∀ R : Type, (A → R → R) → R → R
abbrev CMaybe (A : Type u) := ∀ R : Type, R → (A → R) → R
abbrev CEither (A : Type u) (B : Type v) := ∀ R : Type, (A → R) → (B → R) → R
abbrev CPair (A : Type u) (B : Type v) := ∀ R : Type, (A → B → R) → R
abbrev CBool := ∀ R : Type, R → R → R
def enc {A : Type} (xs : List A) : CList A := fun _ step zero => xs.foldr step zero
def dec {A : Type} (xs : CList A) : List A := xs (List A) List.cons []
def maybe {A : Type} (m : Option A) : CMaybe A := fun _ zero some => m.elim zero some
def either {A B : Type} (e : Sum A B) : CEither A B := fun _ onLeft onRight => e.elim onLeft onRight
def bool (flag : Bool) : CBool := fun _ yes no => if flag then yes else no
def pair {A B : Type} (p : A × B) : CPair A B := fun _ k => k p.1 p.2
def decPair {A B : Type} (p : CPair A B) : A × B := p (A × B) Prod.mk
def dict {A B : Type} (xs : List (A × B)) : CList (CPair A B) := fun _ step zero => xs.foldr (fun p rest => step (fun _ k => k p.1 p.2) rest) zero
end BehaviorPartial
def BehaviorPartial.check_foldr1 (f : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0))))) : Bool := ((((((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((-99) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((-99) : Int))) && ((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)))) && (((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((6) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((23) : Int))) && ((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((8) : Int)) && ((((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((7) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((99) : Int)))))) && ((((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((99) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int))) && ((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((6) : Int)))) && (((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((23) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((8) : Int))) && ((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((7) : Int)) && ((((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([] : (List Bool))))) == (false : Bool)) && (((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false] : (List Bool))))) == (false : Bool))))))) && (((((((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([true] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false,true,false] : (List Bool))))) == (true : Bool))) && ((((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false] : (List Bool))))) == (false : Bool)))) && (((((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([true] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false,true,false] : (List Bool))))) == (true : Bool))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(-99)] : (List Int))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(-99)] : (List Int))) && (((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))))))) && ((((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))) && (((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(2),(3),(4)] : (List Int)))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(3),(2),(4)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(99)] : (List Int))))) && (((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(99)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int)))) && ((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))) && ((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(2),(3),(4)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(3),(2),(4)] : (List Int)))))))))

namespace BehaviorPartialOracle
def head {A : Type} (d : A) (xs : List A) : A := match xs with | [] => d | x :: _ => x
def last {A : Type} (d : A) (xs : List A) : A := xs.foldl (fun _ x => x) d
def indexOr {A : Type} (d : A) (n : Int) : List A → A
  | [] => d
  | x :: xs => if n < 0 then d else if n = 0 then x else indexOr d (n - 1) xs
def foldl1 {A : Type} (d : A) (step : A → A → A) (xs : List A) : A := match xs with | [] => d | x :: rest => rest.foldl step x
def foldr1 {A : Type} (d : A) (step : A → A → A) (xs : List A) : A := (xs.foldr (fun x rest => some (rest.elim x (step x))) (none : Option A)).getD d
end BehaviorPartialOracle
namespace BehaviorPartialControl
def witness_foldr1 : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0)))) := fun A d step xs => BehaviorPartialOracle.foldr1 d step (BehaviorPartial.dec xs)
theorem witness_foldr1_passes : BehaviorPartial.check_foldr1 (BehaviorPartialControl.witness_foldr1) = true := by decide
def wrong_foldr1_always_default : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0)))) := fun _ d _ _ => d
theorem wrong_foldr1_always_default_rejected : BehaviorPartial.check_foldr1 BehaviorPartialControl.wrong_foldr1_always_default = false := by decide
def wrong_foldr1_wrong_association : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0)))) := fun A d step xs => BehaviorPartialOracle.foldl1 d step (BehaviorPartial.dec xs)
theorem wrong_foldr1_wrong_association_rejected : BehaviorPartial.check_foldr1 BehaviorPartialControl.wrong_foldr1_wrong_association = false := by decide
def wrong_foldr1_default_is_seed : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0)))) := fun A d step xs => (BehaviorPartial.dec xs).foldl step d
theorem wrong_foldr1_default_is_seed_rejected : BehaviorPartial.check_foldr1 BehaviorPartialControl.wrong_foldr1_default_is_seed = false := by decide
end BehaviorPartialControl
#print axioms BehaviorPartialControl.witness_foldr1
#print axioms BehaviorPartialControl.witness_foldr1_passes
#print axioms BehaviorPartialControl.wrong_foldr1_always_default
#print axioms BehaviorPartialControl.wrong_foldr1_always_default_rejected
#print axioms BehaviorPartialControl.wrong_foldr1_wrong_association
#print axioms BehaviorPartialControl.wrong_foldr1_wrong_association_rejected
#print axioms BehaviorPartialControl.wrong_foldr1_default_is_seed
#print axioms BehaviorPartialControl.wrong_foldr1_default_is_seed_rejected

namespace Foldr1CarrierControl

def carrierReference : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0)))) :=
  fun A d combine xs =>
    (xs (Option A)
      (fun x rest => some (rest.elim x (combine x))) none).getD d

theorem carrierReference_passes :
    BehaviorPartial.check_foldr1 carrierReference = true := by decide

-- Universal only for this known carrier term on encodings of native lists.
-- It is not a theorem about a synthesized term or every Church inhabitant.
theorem carrierReference_enc (A : Type) (d : A) (combine : A → A → A) (xs : List A) :
    carrierReference A d combine (BehaviorPartial.enc xs) =
      BehaviorPartialOracle.foldr1 d combine xs := by rfl

end Foldr1CarrierControl

#print axioms Foldr1CarrierControl.carrierReference
#print axioms Foldr1CarrierControl.carrierReference_passes
#print axioms Foldr1CarrierControl.carrierReference_enc
