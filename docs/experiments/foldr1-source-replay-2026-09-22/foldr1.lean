import Lean


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


/- Actual printed target and program from both accepted budget runs. The checker
above is copied from the unchanged original probe; no synthesis engine or
reference implementation is imported. -/
set_option maxHeartbeats 0
namespace ActualCarrierReplay
def program : (church0 : Type) →
  church0 →
    (church0 → church0 → church0) → ((church1 : Type) → (church0 → church1 → church1) → church1 → church1) → church0 :=
  fun A d combine =>
  (fun step init finish xs => finish (xs (Option A) step init))
    (fun a a_1 => some (Option.casesOn a_1 a fun val => combine a val)) none fun a => Option.casesOn a d fun val => val
theorem originalContract : BehaviorPartial.check_foldr1 program = true := by decide
#print axioms program
#print axioms originalContract
#eval do
  if BehaviorPartial.check_foldr1 program then
    IO.println "ALL_36_ORIGINAL_OBSERVATIONS_EXECUTED_TRUE"
  else
    throw (IO.userError "actual printed program failed compiled original observations")
end ActualCarrierReplay
