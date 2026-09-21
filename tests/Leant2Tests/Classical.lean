import Leant2.Frontend.Command

/-! Classical universe specialization must preserve fixed assignments and
dependent type structure. Specialized candidates are checked at, and report,
their actual specialized type; the original flexible query stays unchanged. -/
namespace Leant2Tests.Classical

open Lean Meta Elab Term Leant2

private def requireSpecialization (original expected : Expr) : MetaM Expr := do
  let some specialized ← atProp? original
    | throwError "unconstrained classical specialization was refused"
  unless ← withNewMCtxDepth (isDefEq specialized expected) do
    throwError "incorrect classical specialization: {specialized}, expected {expected}"
  return specialized

run_meta do
  let flexible ← mkFreshLevelMVar
  let fixed ← mkFreshLevelMVar
  let alias ← mkFreshLevelMVar
  assignLevelMVar fixed.mvarId! (.succ .zero)
  assignLevelMVar alias.mvarId! fixed
  let fixedBefore ← instantiateLevelMVars alias
  discard <| requireSpecialization (.sort flexible) (.sort .zero)
  discard <| requireSpecialization (.sort alias) (.sort (.succ .zero))
  -- A placeholder in `Type _` chooses Type 0, never Prop. Maxima and
  -- proposition-sensitive imax levels retain their normal Lean meaning.
  discard <| requireSpecialization (.sort (.succ flexible)) (.sort (.succ .zero))
  discard <| requireSpecialization (.sort (.max flexible (.succ .zero)))
    (.sort (.succ .zero))
  discard <| requireSpecialization (.sort (.imax (.succ .zero) flexible)) (.sort .zero)
  discard <| requireSpecialization (.sort (.succ (.param `u))) (.sort (.succ .zero))
  unless (← instantiateLevelMVars alias) == fixedBefore do
    throwError "classical specialization changed an existing universe assignment"
  unless (← instantiateLevelMVars flexible) == flexible do
    throwError "classical specialization assigned the original universe placeholder"

run_meta do
  let u ← mkFreshLevelMVar
  let target := mkForall `A .implicit (.sort u)
    (mkForall `a .default (.bvar 0) (.bvar 1))
  let expected := mkForall `A .implicit (.sort .zero)
    (mkForall `a .default (.bvar 0) (.bvar 1))
  let contract ← withLocalDeclD `f target fun f => do
    mkLambdaFVars #[f] (← mkEq f f)
  let specializedTarget ← requireSpecialization target expected
  let some specializedContract ← atProp? contract
    | throwError "dependent contract specialization was refused"
  unless ← withNewMCtxDepth (isDefEq specializedContract.bindingDomain! specializedTarget) do
    throwError "the contract and target used different universe substitutions"
  let program := mkLambda `A .implicit (.sort .zero)
    (mkLambda `a .default (.bvar 0) (.bvar 0))
  let proof ← mkEqRefl program
  let proofType := specializedContract.beta #[program]
  let .ok accepted ← gate .standard program specializedTarget (some (proof, proofType))
    | throwError "the specialized dependent program/contract failed kernel acceptance"
  unless accepted.programType == specializedTarget && accepted.levelParams.isEmpty do
    throwError "the specialized candidate was reported at a different type"
  unless (← instantiateLevelMVars u) == u && target.hasLevelMVar do
    throwError "checking a specialized contract changed its original query"

run_meta do
  let u ← mkFreshLevelMVar
  let before ← getPostponed
  modifyPostponed fun pending => pending.push {
    ref := Syntax.missing, lhs := u, rhs := .succ .zero, ctx? := none }
  unless (← atProp? (.sort u)).isNone do
    throwError "specialization ignored an unresolved universe constraint"
  unless (← instantiateLevelMVars u) == u && (← getPostponed).size == before.size + 1 do
    throwError "refused specialization changed original constraints"
  setPostponed before

run_elab do
  -- Exact public-query elaboration of the previously timing-out Basic fixture.
  -- Its auto-bound sorts are fresh level metavariables, not named parameters.
  let .ok querySyntax := Parser.runParserCategory (← getEnv) `term "(((A → B) → A) → A)"
    | throwError "could not parse the public Peirce query"
  let (target, _) ← elabQuery none querySyntax none
  unless target.hasLevelMVar do throwError "Peirce fixture lost its flexible universes"
  let originalLevels := collectLevelMVarIds target
  let some expected ← atProp? target | throwError "Peirce specialization was refused"
  let result ← runQuery {
    target, budgetMs := 5000, maxCandidates := 1, graceMs := 0 }
  let .verified candidates _ := result
    | throwError "Peirce query failed under its unchanged five-second focused budget"
  let candidate := candidates[0]!
  unless ← withNewMCtxDepth (isDefEq candidate.programType expected) do
    throwError "Peirce candidate was not reported at its specialized Prop type"
  unless candidate.classical do throwError "Peirce candidate omitted its classical evidence"
  for id in originalLevels do
    unless (← instantiateLevelMVars (.mvar id)) == .mvar id do
      throwError "classical search assigned an original Peirce universe"

end Leant2Tests.Classical
