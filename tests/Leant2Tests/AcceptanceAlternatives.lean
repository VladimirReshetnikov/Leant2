import Leant2.Frontend.Sketch.Run

/-! A rejected contract proof must not suppress a different proof for the same
program. The real residual instance below deliberately contains Classical.choice;
strict search must reject its canonical proof and still accept reflexivity.
No reference program, proof, or observer is supplied as a synthesis provider. -/

namespace Leant2Tests.AcceptanceAlternatives
open Lean Meta Elab Term Leant2

@[instance_reducible] private noncomputable def classicalReflexivity (n : Nat) : Decidable (n = n) :=
  isTrue (Classical.choice (show Nonempty (n = n) from ⟨rfl⟩))

attribute [local instance 100000] classicalReflexivity

private def contract : Expr :=
  mkLambda `n .default (mkConst ``Nat)
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (.bvar 0) (.bvar 0))

private def query : Query := {
  target := mkConst ``Nat, contract := some contract
  profile := .strictConstructive, providers := #[]
  budgetMs := 5000, maxCandidates := 1, graceMs := 0 }

private def checkFixture : MetaM Unit := do
  let residual ← mkResidual contract query.target
  let some (_, some decider) := residual[0]?
    | throwError "fixture did not synthesize its supplied residual decider"
  unless (decider.find? (·.isConstOf ``classicalReflexivity)).isSome do
    throwError "fixture did not retain the classical residual instance"
  let program := mkNatLit 0
  let proposition := contract.beta #[program]
  let decider := decider.beta #[program]
  unless (← kernelDecide proposition decider).1 == some true do
    throwError "classical residual does not reduce to true"
  let canonical := mkApp3 (mkConst ``of_decide_eq_true) proposition decider
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  let .error (.axiomViolation bad) ← gate .strictConstructive program query.target
      (some (canonical, mkApp contract program))
    | throwError "canonical proof was not rejected specifically by the strict axiom profile"
  unless bad.contains ``Classical.choice do
    throwError "canonical rejection did not identify Classical.choice"

private def verifyFallback (label : String) (outcome : Outcome) : MetaM Unit := do
  let .verified candidates work := outcome
    | throwError "{label}: rejected canonical proof suppressed ordinary reflexivity"
  unless candidates.size == 1 && work.rejected > 0 && work.candidates ≥ 2 do
    throwError "{label}: fixture did not reject one complete proof before accepting another"
  let some candidate := candidates[0]? | throwError "{label}: missing accepted candidate"
  unless candidate.axioms.isEmpty && !candidate.classical do
    throwError "{label}: strict fallback retained classical evidence"
  unless ← isDefEq candidate.program (mkNatLit 0) do
    throwError "{label}: fallback changed the first completed program"
  -- The engine retains the native property projection, and whnfR does not
  -- unfold it. Inspect the actual pair's proof field instead of assuming the
  -- exported expression itself has an Eq.refl head.
  unless candidate.proof.isAppOfArity ``Subtype.property 3 do
    throwError "{label}: accepted proof is not the native property projection"
  let pair := candidate.proof.getArg! 2
  unless pair.isAppOfArity ``Subtype.mk 4 do
    throwError "{label}: property projection does not contain the completed native pair"
  unless (pair.getArg! 3).isAppOfArity ``Eq.refl 2 do
    throwError "{label}: accepted proof field is not ordinary reflexivity"
  unless ← isDefEq (pair.getArg! 2) candidate.program do
    throwError "{label}: reflexivity proves a different program's contract"
  let .ok checked ← gate .strictConstructive candidate.program query.target
      (some (candidate.proof, mkApp contract candidate.program))
    | throwError "{label}: alternate proof does not replay at the original query"
  unless checked.axioms.isEmpty do throwError "{label}: independent replay used axioms"

run_elab do
  checkFixture
  verifyFallback "runQuery" (← runQuery query)

run_elab do
  checkFixture
  verifyFallback "synthesize" (← synthesize query)

run_elab do
  checkFixture
  let result ← Frontend.Sketch.synthesizeSketch query (← `(0))
  unless result.preparation.holes.isEmpty do throwError "fixed program acquired a sketch hole"
  verifyFallback "synthesizeSketch" result.outcome

end Leant2Tests.AcceptanceAlternatives
