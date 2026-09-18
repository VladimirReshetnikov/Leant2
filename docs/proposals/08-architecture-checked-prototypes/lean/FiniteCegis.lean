import Lean
open Lean Elab Term
namespace Leant2Finite
inductive Circuit where
  | left | right | zero | one
  | neg : Circuit → Circuit
  | conj : Circuit → Circuit → Circuit
  | disj : Circuit → Circuit → Circuit
  | xor : Circuit → Circuit → Circuit
  deriving Repr, BEq
def Circuit.eval : Circuit → Bool → Bool → Bool
  | .left, a, _ => a
  | .right, _, b => b
  | .zero, _, _ => false
  | .one, _, _ => true
  | .neg p, a, b => !(p.eval a b)
  | .conj p q, a, b => p.eval a b && q.eval a b
  | .disj p q, a, b => p.eval a b || q.eval a b
  | .xor p q, a, b => Bool.xor (p.eval a b) (q.eval a b)
def exactSizeAux : Nat → Nat → List Circuit
  | 0, _ => []
  | _ + 1, 0 => []
  | _ + 1, 1 => [.left, .right, .zero, .one]
  | fuel + 1, n + 2 =>
      (exactSizeAux fuel (n + 1)).map Circuit.neg ++
      ((List.range (n + 1)).flatMap fun i =>
        (exactSizeAux fuel (i + 1)).flatMap fun p =>
          (exactSizeAux fuel (n + 1 - (i + 1))).flatMap fun q =>
            [.conj p q, .disj p q, .xor p q])
def exactSize (n : Nat) : List Circuit := exactSizeAux n n
def pool : List Circuit := (List.range 5).flatMap exactSize
def inputs : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]
def target (mask : Nat) (a b : Bool) : Bool :=
  mask.testBit ((if a then 2 else 0) + (if b then 1 else 0))
def agrees (c : Circuit) (mask : Nat) (ab : Bool × Bool) : Bool :=
  c.eval ab.1 ab.2 == target mask ab.1 ab.2
structure Result where
  candidate : Circuit
  examples : List (Bool × Bool)
  rounds : Nat
  deriving Repr
def cegis : Nat → List Circuit → Nat → List (Bool × Bool) → Nat → Option Result
  | 0, _, _, _, _ => none
  | fuel + 1, candidates, mask, examples, rounds => do
      let c ← candidates.find? fun c => examples.all (agrees c mask)
      match inputs.find? fun ab => !(agrees c mask ab) with
      | none => some ⟨c, examples, rounds + 1⟩
      | some ab => cegis fuel candidates mask (examples ++ [ab]) (rounds + 1)
def synthesize (mask : Nat) : Option Result := cegis 5 pool mask [] 0
def selected (mask : Nat) : Circuit :=
  ((synthesize mask).map Result.candidate).getD .zero
def verify (c : Circuit) (mask : Nat) : Bool := inputs.all (agrees c mask)
theorem verify_sound (c : Circuit) (mask : Nat) (h : verify c mask = true) :
    ∀ a b, c.eval a b = target mask a b := by
  intro a b
  cases a <;> cases b <;> simp_all [verify, inputs, agrees]
theorem all_found : ∀ m : Fin 16, (synthesize m.val).isSome = true := by decide
theorem all_correct : ∀ m : Fin 16, ∀ a b,
    (selected m.val).eval a b = target m.val a b := by decide
def Circuit.quote : Circuit → Expr
  | .left => mkConst ``Circuit.left
  | .right => mkConst ``Circuit.right
  | .zero => mkConst ``Circuit.zero
  | .one => mkConst ``Circuit.one
  | .neg p => mkApp (mkConst ``Circuit.neg) p.quote
  | .conj p q => mkApp2 (mkConst ``Circuit.conj) p.quote q.quote
  | .disj p q => mkApp2 (mkConst ``Circuit.disj) p.quote q.quote
  | .xor p q => mkApp2 (mkConst ``Circuit.xor) p.quote q.quote
elab "synth_bool" mask:num : term => do
  let m := mask.getNat
  if m >= 16 then throwError "truth-table mask must be below 16"
  let some result := synthesize m | throwError "bounded finite synthesis failed"
  return mkApp (mkConst ``Circuit.eval) result.candidate.quote
def generatedXor : Bool → Bool → Bool := synth_bool 6
theorem generatedXor_correct : ∀ a b, generatedXor a b = Bool.xor a b := by decide
#eval pool.length
#eval (List.range 16).map fun m => (m, synthesize m)
#print generatedXor
#print axioms verify_sound
#print axioms all_found
#print axioms all_correct
#print axioms generatedXor
#print axioms generatedXor_correct
#eval Lean.versionString
end Leant2Finite
