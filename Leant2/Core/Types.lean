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
  /-- A kernel-checked proof of `T -> False`. -/
  | impossible
  /-- A kernel-checked proof that no program of the type satisfies the contract. -/
  | contractImpossible
  /-- The configured finite grammar was exhausted; not an impossibility claim. -/
  | grammarExhausted
  /-- The budget ran out; resumable in principle. -/
  | budgetExhausted
  deriving Repr, BEq, Inhabited

/-- One accepted candidate: closed program with its actual checked type and
universe parameters (remaining level metavariables are generalized by the
gate), closed proof of the contract (trivial when there is no contract), and
the audited axiom inventory. A classical universe specialization is recorded
at its specialized type; it need not inhabit the original query type.

For an impossibility certificate, `program` is the refutation and
`programType` is its negative statement. The separate `proof` field is then
`True.intro`, not the refutation. `classical` records the presence of
`Classical.choice`; other axioms can occur even when it is false. -/
structure Accepted where
  program : Expr
  programType : Expr
  levelParams : List Name
  proof : Expr
  axioms : Array Name
  classical : Bool
  deriving Inhabited

/-- Outcome of one query (Section 3.3, restricted to what is implemented).
Verified outcomes contain at least one candidate. Semantic negatives
(`impossible` and `contractImpossible`) carry `some` checked certificate;
bounded negatives carry `none`. `refutedAll` reports rejected proposals,
not a proof that the target or contract is universally impossible.

These are engine invariants, not restrictions enforced by this datatype.
The public `synthesize` boundary checks candidate/certificate transport and
rejects malformed semantic outcomes with an exception. -/
inductive Outcome where
  | verified (cands : Array Accepted) (ledger : Ledger)
  | refutedAll (rejected : Nat) (ledger : Ledger)
  | negative (kind : NegativeKind) (cert : Option Accepted) (ledger : Ledger)
  | preflightError (msg : String)
  deriving Inhabited

register_option leant2.trace : Bool := {
  defValue := false
  descr := "leant2: print lane timings and depth progress"
}

register_option leant2.skipRules : String := {
  defValue := ""
  descr := "leant2: comma-separated search rules to disable, for experiments (7a,7b,9,9b,9c,rec,guards,composition,residual)"
}

register_option leant2.traceNodes : Bool := {
  defValue := false
  descr := "leant2: print every program checked against the contract (verbose)"
}

end Leant2
