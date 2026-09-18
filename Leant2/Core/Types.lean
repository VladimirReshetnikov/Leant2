import Lean
/-!
# Leant2 core types

The result algebra, trust profiles, and the work ledger from the unified
proposal (Section 3.3, 3.4, and Decision 2.8).
-/
namespace Leant2

open Lean

/-- Trust profiles: which axioms a proof may use (Section 3.4). -/
inductive Profile where
  | strictConstructive
  | standard
  | projectRelative (extra : List Name)
  deriving Repr, Inhabited

def Profile.allowedAxioms : Profile → List Name
  | .strictConstructive => []
  | .standard => [``propext, ``Quot.sound, ``Classical.choice]
  | .projectRelative extra => [``propext, ``Quot.sound, ``Classical.choice] ++ extra

/-- Monotone work ledger. Charges are never refunded by rollback (Decision 2.8). -/
structure Ledger where
  ruleApplications : Nat := 0
  unifications : Nat := 0
  proofAttempts : Nat := 0
  candidates : Nat := 0
  rejected : Nat := 0
  deriving Repr, Inhabited

/-- Why a search stopped without a verified answer. -/
inductive NegativeKind where
  /-- A kernel-checked proof of `T -> False` (or of the negated contract). -/
  | impossible
  /-- The configured finite grammar was exhausted; not an impossibility claim. -/
  | grammarExhausted
  /-- The budget ran out; resumable in principle. -/
  | budgetExhausted
  deriving Repr, BEq, Inhabited

/-- One accepted candidate: closed program with its type and universe
parameters (remaining level metavariables are generalized by the gate),
closed proof of the contract (trivial when there is no contract), and the
audited axiom inventory. -/
structure Accepted where
  program : Expr
  programType : Expr
  levelParams : List Name
  proof : Expr
  axioms : Array Name
  classical : Bool
  deriving Inhabited

/-- Outcome of one query (Section 3.3, restricted to what is implemented). -/
inductive Outcome where
  | verified (cands : Array Accepted) (ledger : Ledger)
  | refutedAll (rejected : Nat) (ledger : Ledger)
  | negative (kind : NegativeKind) (cert : Option Accepted) (ledger : Ledger)
  | preflightError (msg : String)
  deriving Inhabited

end Leant2
