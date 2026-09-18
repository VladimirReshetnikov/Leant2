import Lean

/-! A finite, Lean-implemented CEGIS plugin experiment. No SMT solver or Mathlib.
The grammar is Boolean x, y, not, and, or; size counts all syntax-tree nodes.
Search runs as ordinary compiled Lean metaprogram code. The chosen syntax is
quoted as a literal kernel term; its universal specification is proved separately.
-/
open Lean Elab Term
namespace Leant2Finite

inductive BExpr where
  | x | y
  | neg : BExpr → BExpr
  | conj : BExpr → BExpr → BExpr
  | disj : BExpr → BExpr → BExpr
  deriving Repr, BEq, Inhabited

def BExpr.eval : BExpr → Bool → Bool → Bool
  | .x, x, _ => x
  | .y, _, y => y
  | .neg a, x, y => !(a.eval x y)
  | .conj a b, x, y => a.eval x y && b.eval x y
  | .disj a b, x, y => a.eval x y || b.eval x y

def BExpr.nodes : BExpr → Nat
  | .x | .y => 1
  | .neg a => 1 + a.nodes
  | .conj a b | .disj a b => 1 + a.nodes + b.nodes

/-- Exact-size dynamic programming; table[0] is intentionally empty. -/
def enumerate (bound : Nat) : Array (List BExpr) := Id.run do
  let mut table : Array (List BExpr) := #[[]]
  for n in [1:bound + 1] do
    let mut layer : List BExpr := if n == 1 then [.x, .y] else []
    if n > 1 then
      layer := layer ++ (table[n - 1]!).map BExpr.neg
      for left in [1:n - 1] do
        let right := n - 1 - left
        for a in table[left]! do
          for b in table[right]! do
            layer := layer ++ [.conj a b, .disj a b]
    table := table.push layer
  return table

abbrev Input := Bool × Bool

def inputs : List Input := [(false, false), (false, true), (true, false), (true, true)]
def expected (p : Input) : Bool := p.1 != p.2

def agrees (e : BExpr) (p : Input) : Bool := e.eval p.1 p.2 == expected p

structure Run where
  result : Option BExpr
  examples : List Input
  proposals : List BExpr
  deriving Repr

/-- Every added example is a concrete falsification of the current candidate. -/
def cegis (candidates : List BExpr) : Nat → List Input → List BExpr → Run
  | 0, samples, proposals => ⟨none, samples, proposals⟩
  | fuel + 1, samples, proposals =>
    match candidates.find? (fun e => samples.all (agrees e)) with
    | none => ⟨none, samples, proposals⟩
    | some e =>
      match inputs.find? (fun p => !(agrees e p)) with
      | none => ⟨some e, samples, proposals ++ [e]⟩
      | some p => cegis candidates fuel (samples ++ [p]) (proposals ++ [e])

def experiment : Run := cegis (enumerate 8).toList.flatten 5 [] []

def BExpr.quote : BExpr → Expr
  | .x => mkConst ``BExpr.x
  | .y => mkConst ``BExpr.y
  | .neg a => mkApp (mkConst ``BExpr.neg) a.quote
  | .conj a b => mkApp2 (mkConst ``BExpr.conj) a.quote b.quote
  | .disj a b => mkApp2 (mkConst ``BExpr.disj) a.quote b.quote

/-- Untrusted search returns syntax, not a theorem or a native_decide axiom. -/
elab "synthesize_xor%" : term => do
  let run := experiment
  match run.result with
  | none => throwError "finite CEGIS exhausted its declared grammar/budget"
  | some e =>
    logInfo m!"CEGIS: {run.proposals.length} proposals, {run.examples.length} counterexamples, {e.nodes} nodes"
    return e.quote

def synthesizedXor : BExpr := synthesize_xor%

theorem synthesizedXor_correct :
    ∀ x y : Bool, synthesizedXor.eval x y = (x != y) := by decide

/-- A successful test on one input is not an equivalence certificate. -/
theorem sampleCollision : BExpr.x.eval false false = BExpr.y.eval false false := rfl

theorem separatedLater : BExpr.x.eval false true ≠ BExpr.y.eval false true := by decide

/-- A genuine semantic negative certificate, independent of any search bound. -/
theorem impossibleSpecification : ¬ ∃ f : Bool → Bool, ∀ b, f b ≠ f b := by
  intro ⟨f, h⟩
  exact h false rfl

#eval (enumerate 8).toList.map List.length
#eval experiment
#eval inputs.map (fun p => synthesizedXor.eval p.1 p.2)
#eval Lean.versionString
#print synthesizedXor
#print axioms synthesizedXor
#print axioms synthesizedXor_correct
#print axioms sampleCollision
#print axioms separatedLater
#print axioms impossibleSpecification
end Leant2Finite
