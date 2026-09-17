import Lean

set_option autoImplicit false

namespace Leant2Behavior

/-- A deliberately finite program grammar, not an approximation of Lean types. -/
structure Affine where
  slope : Nat
  offset : Nat
  deriving DecidableEq, Repr

def Affine.eval (c : Affine) (n : Nat) : Nat := c.slope * n + c.offset
def Spec (f : Nat → Nat) : Prop := f 0 = 1 ∧ ∀ n, f (n + 1) = f n + 2
def canonical : Affine := ⟨2, 1⟩

theorem canonical_spec : Spec canonical.eval := by
  constructor
  · rfl
  · intro n
    simp only [Affine.eval, canonical, Nat.mul_add, Nat.mul_one]

/-- The universal verifier is complete only for this affine grammar. -/
theorem affine_spec_iff (c : Affine) : Spec c.eval ↔ c = canonical := by
  rcases c with ⟨a, b⟩
  constructor
  · rintro ⟨h0, hs⟩
    have h1 := hs 0
    simp [Affine.eval] at h0 h1
    have ha : a = 2 := by omega
    cases ha
    cases h0
    rfl
  · intro h
    simpa only [h] using canonical_spec

inductive Observation
  | base
  | step (n : Nat)
  deriving DecidableEq, Repr

def observe (f : Nat → Nat) : Observation → Prop
  | .base => f 0 = 1
  | .step n => f (n + 1) = f n + 2

instance (f : Nat → Nat) (o : Observation) : Decidable (observe f o) := by
  cases o <;> unfold observe <;> infer_instance

def passes (c : Affine) (o : Observation) : Bool := decide (observe c.eval o)

theorem replay_sound (c : Affine) (o : Observation)
    (rejected : passes c o = false) : ¬ Spec c.eval := by
  intro spec
  have observed : observe c.eval o := by
    cases o with
    | base => exact spec.1
    | step n => exact spec.2 n
  have passed : passes c o = true := by simpa [passes] using observed
  rw [passed] at rejected
  cases rejected

def certify (c : Affine) : Option {c : Affine // Spec c.eval} :=
  if h : c = canonical then
    some ⟨c, (affine_spec_iff c).mpr h⟩
  else none

def counterexample (c : Affine) : Option Observation :=
  [Observation.base, .step 0].find? (fun o => !passes c o)

structure Stats where
  considered : Nat := 0
  proofAttempts : Nat := 0
  pruned : Nat := 0
  inconclusive : Nat := 0
  deriving Repr

structure Outcome where
  winner : Option {c : Affine // Spec c.eval}
  stats : Stats
  bank : List Observation

def search (candidates : List Affine) (bank : List Observation := [])
    (stats : Stats := {}) : Outcome :=
  match candidates with
  | [] => ⟨none, stats, bank⟩
  | c :: rest =>
    let stats := { stats with considered := stats.considered + 1 }
    if bank.all (passes c) then
      let stats := { stats with proofAttempts := stats.proofAttempts + 1 }
      match certify c with
      | some winner => ⟨some winner, stats, bank⟩
      | none =>
        match counterexample c with
        | some o => search rest (bank ++ [o]) stats
        | none => search rest bank { stats with inconclusive := stats.inconclusive + 1 }
    else search rest bank { stats with pruned := stats.pruned + 1 }

def grammar : List Affine :=
  (List.range 5).flatMap fun a => (List.range 5).map fun b => ⟨a, b⟩

def run : Outcome := search grammar

theorem run_counts :
    run.stats.considered = 12 ∧ run.stats.proofAttempts = 3 ∧
    run.stats.pruned = 9 ∧ run.stats.inconclusive = 0 := by decide

theorem run_result :
    run.winner.map (fun c => (c.val.slope, c.val.offset)) = some (2, 1) := by decide

#eval (run.winner.map (fun c => (c.val.slope, c.val.offset)), run.stats, run.bank)
#print axioms canonical_spec
#print axioms affine_spec_iff
#print axioms replay_sound
#print axioms run_counts
#print axioms run_result
#eval Lean.versionString

end Leant2Behavior
