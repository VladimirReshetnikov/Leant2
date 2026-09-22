import Leant2.Frontend.Sketch.Run

/-! Negative pruning must obey the query's axiom policy. These tests use an
environment decider that lies about reflexivity via an explicitly forbidden
axiom. The original query and its independent reflexivity proof are axiom-free;
no reference program/proof is supplied as a provider. -/

namespace Leant2Tests.PruningProfiles
open Lean Meta Elab Term Leant2

private axiom badAxiom : False

@[instance_reducible] private def badReflexivity (n : Nat) : Decidable (n = n) :=
  isFalse (fun _ => badAxiom)

attribute [local instance 100000] badReflexivity

private def contract : Expr :=
  mkLambda `n .default (mkConst ``Nat)
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (.bvar 0) (.bvar 0))

private def query : Query := {
  target := mkConst ``Nat, contract := some contract
  profile := .strictConstructive, providers := #[]
  budgetMs := 5000, maxCandidates := 1, graceMs := 0 }

private def context : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}, refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[], observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def configuration (c : Expr := contract) : MetaM SearchConfig := do
  return {
    profile := .strictConstructive
    pruningEvidenceCache := some (← IO.mkRef none)
    contract := some c, residual := ← mkResidual c (mkConst ``Nat) }

private def checkFixture : MetaM Unit := do
  let .ok checkedContract ← gate .strictConstructive contract (← inferType contract) none
    | throwError "original contract is not strict"
  unless checkedContract.axioms.isEmpty && query.providers.isEmpty do
    throwError "original inputs acquired a forbidden dependency/provider"
  let residual ← mkResidual contract query.target
  let some (_, some schema) := residual[0]?
    | throwError "fixture has no synthesized residual decider"
  unless (schema.find? (·.isConstOf ``badReflexivity)).isSome do
    throwError "fixture did not select badReflexivity"
  let program := mkNatLit 0
  let proposition := contract.beta #[program]
  let decider := schema.beta #[program]
  unless (← kernelDecide proposition decider).1 == some false do
    throwError "bad decider does not reduce to false"
  let canonical := mkApp3 (mkConst ``of_decide_eq_false) proposition decider
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))
  let .error (.axiomViolation bad) ← gate .strictConstructive canonical
      (mkApp (mkConst ``Not) proposition) none
    | throwError "bad negative certificate was not refused by the strict profile"
  unless bad.contains ``badAxiom do throwError "negative rejection lost badAxiom"
  let .ok negativeControl ← gate (.projectRelative [``badAxiom]) canonical
      (mkApp (mkConst ``Not) proposition) none
    | throwError "negative certificate is not valid under its explicit axiom"
  unless negativeControl.axioms.contains ``badAxiom do
    throwError "negative control has no badAxiom dependency"
  let .ok positive ← gate .strictConstructive program query.target
      (some (← mkEqRefl program, mkApp contract program))
    | throwError "independent Eq.refl does not satisfy the exact original query"
  unless positive.axioms.isEmpty do throwError "independent positive uses axioms"

private def verify (label : String) (outcome : Outcome) : MetaM Unit := do
  let .verified candidates _ := outcome
    | throwError "{label}: forbidden false evidence pruned the satisfiable query"
  unless candidates.size == 1 do throwError "{label}: expected one candidate"
  let candidate := candidates[0]!
  unless ← isDefEq candidate.program (mkNatLit 0) do
    throwError "{label}: changed the first completed program"
  let .ok replayed ← gate .strictConstructive candidate.program query.target
      (some (candidate.proof, mkApp contract candidate.program))
    | throwError "{label}: candidate fails original-query replay"
  unless replayed.axioms.isEmpty && candidate.axioms.isEmpty do
    throwError "{label}: accepted candidate uses axioms"

run_elab do
  checkFixture
  verify "runQuery" (← runQuery query)

run_elab do
  checkFixture
  verify "synthesize" (← synthesize query)

run_elab do
  checkFixture
  let result ← Frontend.Sketch.synthesizeSketch query (← `(0))
  unless result.preparation.holes.isEmpty do throwError "fixed sketch gained a hole"
  verify "synthesizeSketch" result.outcome

-- All four negative exits have direct controls, including the generic paths
-- with no precomputed residual. Trusted false still stops the proof portfolio.
run_elab do
  checkFixture
  let cfg ← configuration
  let ctx ← context
  unless (← (evalResidual cfg (mkNatLit 0)).run ctx) matches .stuck do
    throwError "residual accepted forbidden false evidence"
  let permissive := { cfg with profile := .projectRelative [``badAxiom] }
  unless (← (evalResidual permissive (mkNatLit 0)).run ctx) matches .refuted do
    throwError "explicitly allowed false evidence did not prune"
  let proposition := contract.beta #[mkNatLit 0]
  let generic := { cfg with residual := #[], contract := none }
  if ← (partialRefute generic proposition).run ctx then
    throwError "generic partialRefute accepted forbidden false evidence"
  let proofGoal ← mkFreshExprMVar proposition
  unless ← (proofPortfolio generic proofGoal.mvarId!).run ctx do
    throwError "generic portfolio did not try reflexivity after forbidden false"
  let proof ← instantiateMVars proofGoal
  let .ok checked ← gate .strictConstructive proof proposition none
    | throwError "generic portfolio fallback is not admissible"
  unless checked.axioms.isEmpty do throwError "portfolio fallback uses axioms"
  let falseProposition ← elabTerm (← `((0 : Nat) = 1)) none
  unless ← (partialRefute generic falseProposition).run ctx do
    throwError "trusted generic false stopped pruning"
  let falseGoal ← mkFreshExprMVar falseProposition
  if ← (proofPortfolio generic falseGoal.mvarId!).run ctx then
    throwError "trusted false goal was solved"
  if ← falseGoal.mvarId!.isAssigned then throwError "false portfolio assigned a proof"

-- A refused false conjunct is inconclusive, not an early exit: a later trusted
-- false conjunct can still refute, for closed and genuinely partial programs.
run_elab do
  let mixed ← elabTerm (← `(fun n : Nat => n = n ∧ False)) none
  let cfg ← configuration mixed
  let ctx ← context
  unless (← (evalResidual cfg (mkNatLit 0)).run ctx) matches .refuted do
    throwError "later trusted residual was skipped after an unauthorized false"
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let observations ← mkObservations mixed (mkConst ``Nat)
  let partialCfg := { cfg with observations }
  unless (← (evalResidual partialCfg pending).run ctx) matches .refuted do
    throwError "later trusted observation did not prune an open program"
  unless (← ctx.observationReport.get).statuses == #[some .stuck, some .refuted] do
    throwError "observation authorization did not continue to the later conjunct"
  if ← pending.mvarId!.isAssigned then throwError "pruning completed the remaining hole"

-- Raw observation-cache hits are reauthorized under the current profile. A
-- cached false is never itself the evidence, and the policy cache changes too.
run_elab do
  let observations ← mkObservations contract (mkConst ``Nat)
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let evidenceCache ← IO.mkRef none
  let authorize := fun profile p d => falseEvidenceAllowed profile p d (some evidenceCache)
  let (strict, cache) ← evalObservations observations pending #[] instantiatePartial
    (authorizeFalse := authorize .strictConstructive)
  unless strict.statuses == #[some .stuck] do throwError "strict observation pruned"
  let some (some entry) := cache[0]? | throwError "raw false was not cached"
  unless entry.reduced.isConstOf ``Bool.false do throwError "cache is not raw false"
  let (allowed, cache) ← evalObservations observations pending cache instantiatePartial
    (authorizeFalse := authorize (.projectRelative [``badAxiom]))
  unless allowed.refuted && allowed.reused == 1 && allowed.reductions == 0 do
    throwError "permissive profile did not authorize the same cached false"
  let (strictAgain, _) ← evalObservations observations pending cache instantiatePartial
    (authorizeFalse := authorize .strictConstructive)
  unless strictAgain.statuses == #[some .stuck] && strictAgain.reused == 1 &&
      strictAgain.reductions == 0 do
    throwError "profile-approved status leaked through raw cache reuse"

-- A lawful schema can reject one known component before its sibling is filled.
-- This guards against accidentally disabling all partial pruning.
run_elab do
  let pairType ← elabType (← `(Bool × Bool))
  let c ← elabTerm (← `(fun p : Bool × Bool => p.1 = true)) none
  let hole ← mkFreshExprMVar (mkConst ``Bool)
  let partialProgram ← mkAppM ``Prod.mk #[mkConst ``Bool.false, hole]
  let cfg : SearchConfig := {
    profile := .strictConstructive, contract := some c
    residual := ← mkResidual c pairType, observations := ← mkObservations c pairType }
  let ctx ← context
  unless (← (evalResidual cfg partialProgram).run ctx) matches .refuted do
    throwError "trusted partial false did not prune with an unresolved sibling"
  if ← hole.mvarId!.isAssigned then throwError "trusted partial pruning filled the sibling"
  -- Without observations the original residual path must retain this ability.
  unless (← (evalResidual { cfg with observations := #[] } partialProgram).run ctx) matches .refuted do
    throwError "trusted partial residual stopped pruning"

-- Incomplete/free-local generic evidence is conservative. Entire unreduced
-- schemas are audited, including unused expressions erased by beta reduction.
run_elab do
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let falseBody := Lean.mkConst ``False
  let openPredicate := mkApp (mkLambda `ignored .default (mkConst ``Nat) falseBody) pending
  let decider ← synthInstance (mkApp (mkConst ``Decidable) falseBody)
  if ← falseEvidenceAllowed .strictConstructive openPredicate decider then
    throwError "open schema was authorized"
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    if ← falseEvidenceAllowed .strictConstructive n decider then
      throwError "free-local evidence was authorized"
  let erased := mkApp (mkLambda `unused .default (mkConst ``False) decider)
    (mkConst ``badAxiom)
  unless erased.headBeta == decider do throwError "unused-argument fixture does not erase"
  if ← falseEvidenceAllowed .strictConstructive falseBody erased then
    throwError "audit reduced away a forbidden dependency"

-- Reusing the same declaration name after rollback must not reuse a judgment
-- from its previous environment. The cache itself deliberately survives.
run_elab withoutModifyingState do
  let cache ← IO.mkRef none
  let name ← mkFreshUserName `pruningEvidenceReplacement
  let name := (← getEnv).asyncPrefix?.getD `Leant2Tests.PruningProfiles ++ name
  let predicate := Lean.mkConst ``False
  let type := mkApp (mkConst ``Decidable) predicate
  let good ← synthInstance type
  let saved ← saveState
  addDecl <| .defnDecl {
    name, levelParams := [], type, value := good, hints := .abbrev, safety := .safe }
  unless ← falseEvidenceAllowed .strictConstructive predicate (mkConst name) (some cache) do
    throwError "trusted declaration was refused"
  saved.restore
  let bad := mkApp (mkLambda `unused .default predicate good) (mkConst ``badAxiom)
  addDecl <| .defnDecl {
    name, levelParams := [], type, value := bad, hints := .abbrev, safety := .safe }
  if ← falseEvidenceAllowed .strictConstructive predicate (mkConst name) (some cache) then
    throwError "environment replacement reused an obsolete evidence judgment"

namespace UnsafeEvidence

-- Never executed: it appears only in proof syntax discarded by reduction of
-- Decidable.isFalse. Its unchecked recursion has no axiom dependencies.
set_option linter.defProp false in
private unsafe def unsafeFalse (_n : Nat) : False := unsafeFalse 0

@[instance_reducible] private unsafe def unsafeReflexivity (n : Nat) : Decidable (n = n) :=
  isFalse (fun _ => unsafeFalse 0)

attribute [local instance 100001] unsafeReflexivity

private def checkUnsafe (predicate decider : Expr) : MetaM Unit := do
  unless (← kernelDecide predicate decider).1 == some false do
    throwError "unsafe evidence fixture does not reduce to false"
  let canonical := mkApp3 (mkConst ``of_decide_eq_false) predicate decider
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))
  let .error (.kernelRejected message) ← gate .strictConstructive canonical
      (mkApp (mkConst ``Not) predicate) none
    | throwError "safe gate did not reject the unsafe negative certificate"
  unless (message.splitOn "unsafe").length > 1 do
    throwError "negative certificate failed for a reason other than unsafety"
  -- Unsafety cannot be granted by an axiom allowlist.
  for profile in [.strictConstructive, .standard,
      .projectRelative [``unsafeFalse, ``unsafeReflexivity]] do
    if ← falseEvidenceAllowed profile predicate decider then
      throwError "axiom-free unsafe evidence authorized negative pruning"

run_elab do
  unless (← getConstInfo ``unsafeFalse).isUnsafe &&
      (← getConstInfo ``unsafeReflexivity).isUnsafe do
    throwError "unsafe fixture lost its declaration metadata"
  unless (← collectAxioms ``unsafeFalse).isEmpty &&
      (← collectAxioms ``unsafeReflexivity).isEmpty do
    throwError "unsafe fixture acquired an axiom dependency"
  let program := mkNatLit 0
  let proposition := contract.beta #[program]
  let negative := mkLambda `equality .default proposition
    (mkApp (mkConst ``unsafeFalse) program)
  checkUnsafe proposition (mkApp2 (mkConst ``Decidable.isFalse) proposition negative)
  let residual ← mkResidual contract query.target
  let some (predicate, some schema) := residual[0]?
    | throwError "native synthesis did not find the unsafe instance"
  unless (schema.find? (·.isConstOf ``unsafeReflexivity)).isSome do
    throwError "native synthesis did not select unsafeReflexivity"
  checkUnsafe (predicate.beta #[program]) (schema.beta #[program])
  if ← falseEvidenceAllowed .strictConstructive predicate schema then
    throwError "closed unsafe instance schema authorized pruning"
  let .ok independent ← gate .strictConstructive program query.target
      (some (← mkEqRefl program, mkApp contract program))
    | throwError "independent original-query reflexivity failed"
  unless independent.axioms.isEmpty do throwError "independent reflexivity uses axioms"
  verify "unsafe runQuery" (← runQuery query)
  verify "unsafe synthesize" (← synthesize query)
  let result ← Frontend.Sketch.synthesizeSketch query (← `(0))
  unless result.preparation.holes.isEmpty do throwError "fixed unsafe test gained a hole"
  verify "unsafe synthesizeSketch" result.outcome

end UnsafeEvidence
end Leant2Tests.PruningProfiles
