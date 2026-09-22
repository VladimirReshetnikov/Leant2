import Leant2.API

/-! Native metaprogram consumers of the closed-query API. Positive answers and
refutation certificates are checked after restoration, with adversarial input,
output, universe, axiom-policy, and cancellation fixtures. -/

namespace Leant2Tests.LibraryAPI
open Lean Meta Elab Term Leant2
universe u

private def expectOutputError (query : Query) (outcome : Outcome) : MetaM Unit := do
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let rejected ← try
    discard <| API.exportOutcome originalCore originalMeta query outcome
    pure false
  catch ex =>
    if Leant2.isInterrupt ex then throw ex
    pure true
  unless rejected do throwError "invalid engine output was not rejected exceptionally"

private def first (outcome : Outcome) : MetaM Accepted := do
  let .verified candidates _ := outcome | throwError "API fixture did not synthesize"
  let some candidate := candidates[0]? | throwError "API returned no verified candidates"
  return candidate

private def replay (candidate : Accepted) (profile : Profile) : MetaM Unit := do
  let .ok programAxioms ← kernelCheckAndAudit `Leant2Tests.API candidate.program
      candidate.programType candidate.levelParams false
    | throwError "returned API program does not replay after restoration"
  let proofType ← inferType candidate.proof
  let .ok proofAxioms ← kernelCheckAndAudit `Leant2Tests.API candidate.proof
      proofType candidate.levelParams true
    | throwError "returned API proof does not replay after restoration"
  unless (programAxioms ++ proofAxioms).all profile.allowedAxioms.contains do
    throwError "returned API evidence violates the selected profile"

run_meta do
  -- Universe parameters are explicit and rigid; no elaborator syntax is needed.
  let target := mkForall `A .default (mkSort (.param `u))
    (mkForall `x .default (.bvar 0) (.bvar 1))
  let beforeCore ← getThe Core.State
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let beforeMeta ← getThe Meta.State
  let candidate ← first (← Leant2.synthesize {
    target, profile := .strictConstructive, providers := #[]
    budgetMs := 5000, maxCandidates := 1, graceMs := 0 })
  unless !(← pending.mvarId!.isAssigned) &&
      (← getMCtx).mvarCounter == beforeMeta.mctx.mvarCounter &&
      (← getEnv).constants.map₂.toList.map Prod.fst ==
        beforeCore.env.constants.map₂.toList.map Prod.fst &&
      (← getThe Core.State).messages.toList.length == beforeCore.messages.toList.length do
    throwError "synthesize changed caller state"
  replay candidate .strictConstructive
  unless ← isDefEq candidate.programType target do throwError "identity changed type"
  unless candidate.levelParams == [`u] do
    throwError "identity changed its named universe parameters"

run_meta do
  -- The explicit Prop marker enters the engine's existing classical lane;
  -- bare named Sort parameters alone do not enable that lane.
  let target ← withLocalDeclD `marker (mkSort .zero) fun marker =>
    withLocalDeclD `A (mkSort (.param `u)) fun a =>
      withLocalDeclD `B (mkSort (.param `u)) fun b => do
        let hypothesis ← mkArrow (← mkArrow a b) a
        mkForallFVars #[marker, a, b] (← mkArrow hypothesis a)
  let some specialized ← atProp? target | throwError "specialization fixture unavailable"
  let candidate ← first (← Leant2.synthesize {
    target, profile := .standard, providers := #[], budgetMs := 5000
    maxCandidates := 1, graceMs := 0 })
  replay candidate .standard
  unless ← isDefEq candidate.programType specialized do
    throwError "public API failed to preserve the specialized actual type"
  unless (← kernelCheckAndAudit `Leant2Tests.API candidate.program target
      [`u] false) matches .error _ do
    throwError "specialized answer unexpectedly proves the original polymorphic target"

run_elab do
  let target ← elabType (← `(Nat → Nat))
  let contract ← elabTerm (← `(fun f : Nat → Nat => f 0 = 0 ∧ f 2 = 2)) none
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let contract ← instantiateMVars contract
  let candidate ← first (← Leant2.synthesize {
    target, contract := some contract, profile := .strictConstructive
    budgetMs := 5000, maxCandidates := 1, graceMs := 0 })
  replay candidate .strictConstructive
  -- Check the returned proof against the actual original contract, not just
  -- against its inferred type. The Nat fixture has no universe specialization.
  let .ok _ ← kernelCheckAndAudit `Leant2Tests.API candidate.proof
      (mkApp contract candidate.program) candidate.levelParams true
    | throwError "API returned a proof for a different contract"

private def preflight (query : Query) : MetaM Unit := do
  match ← Leant2.synthesize query with
  | .preflightError _ => pure ()
  | _ => throwError "malformed input was not a preflight error"

run_meta do
  let expressionHole ← mkFreshExprMVar (mkSort (.succ .zero))
  let universeHole ← mkFreshLevelMVar
  preflight { target := expressionHole }
  preflight { target := mkSort universeHole }
  preflight { target := .bvar 0 }
  preflight { target := mkNatLit 0 }
  preflight { target := mkConst ``Nat, maxCandidates := 0 }
  preflight { target := mkConst ``Nat, providers := #[`DefinitelyMissingAPIProvider] }
  preflight {
    target := mkConst ``Nat
    contract := some (mkLambda `x .default (mkConst ``Nat) (mkConst ``Bool.true)) }
  withLocalDeclD `hidden (mkSort (.succ .zero)) fun localType =>
    preflight { target := localType }
  unless !(← expressionHole.mvarId!.isAssigned) &&
      (← instantiateLevelMVars universeHole) == universeHole do
    throwError "preflight assigned an incoming hole"

run_meta do
  -- Resource pressure during native input checking is exceptional, not a
  -- malformed-input result or a bounded-search outcome.
  let target := (List.range 64).foldl
    (fun ty _ => mkForall `x .default (mkConst ``Nat) ty) (mkConst ``Nat)
  let originalMeta ← getThe Meta.State
  let originalCore ← getThe Core.State
  let exhausted ← tryCatchRuntimeEx (do
    withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := 1, currRecDepth := 0 }) do
      discard <| Leant2.synthesize { target }
    pure false) (fun ex => pure ex.isMaxRecDepth)
  unless exhausted do throwError "preflight recursion pressure became an ordinary outcome"
  unless (← getMCtx).mvarCounter == originalMeta.mctx.mvarCounter &&
      (← getEnv).constants.map₂.toList.map Prod.fst ==
        originalCore.env.constants.map₂.toList.map Prod.fst do
    throwError "preflight resource exception leaked caller state"

run_meta do
  -- Ambient hypotheses are not input to this closed-query API.
  withLocalDeclD `contradiction (mkConst ``False) fun _ => do
    let outcome ← Leant2.synthesize {
      target := mkConst ``False
      profile := .strictConstructive, budgetMs := 1000, maxCandidates := 1 }
    match outcome with
    | .verified .. => throwError "API used an ambient hypothesis"
    | .negative .impossible (some certificate) _ => replay certificate .strictConstructive
    | _ => throwError "False fixture lost its constructive refutation positive control"

run_elab do
  -- Prerequisite regression: native simp should find the same propext-bearing
  -- refutation as the exact reference below. Neither axiom choice nor provider
  -- provenance is inferred from Accepted.classical (which detects choice only).
  let target ← elabType (← `(Unit))
  let contract ← elabTerm (← `(fun (_ : Unit) => True ≠ (True ∧ True))) none
  let negType ← elabType (← `(∀ (_ : Unit), ¬(True ≠ (True ∧ True))))
  let exactRefutation ← elabTerm (← `(fun (_ : Unit) h =>
    h (propext ⟨fun _ => ⟨True.intro, True.intro⟩, fun _ => True.intro⟩))) (some negType)
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let contract ← instantiateMVars contract
  let negType ← instantiateMVars negType
  let exactRefutation ← instantiateMVars exactRefutation
  let .ok reference ← gate .standard exactRefutation negType none
    | throwError "standard reference refutation failed"
  unless reference.axioms.contains ``propext do throwError "fixture did not use propext"
  unless (← gate .strictConstructive exactRefutation negType none) matches .error _ do
    throwError "strict gate accepted the propext reference"
  let standard ← Leant2.synthesize {
    target, contract := some contract
    profile := .standard, budgetMs := 1000, maxCandidates := 1 }
  match standard with
  | .negative .contractImpossible (some certificate) _ =>
    replay certificate .standard
    unless certificate.axioms.contains ``propext do
      throwError "standard certificate omitted its axiom inventory"
    let .ok _ ← kernelCheckAndAudit `Leant2Tests.API certificate.program
        negType certificate.levelParams true
      | throwError "contract refutation proved the wrong statement"
  | _ => throwError "standard contract refutation lacked a replayable certificate"
  let strict ← Leant2.synthesize {
    target, contract := some contract
    profile := .strictConstructive, budgetMs := 1000, maxCandidates := 1 }
  if strict matches .negative .contractImpossible _ _ then
    throwError "strict query accepted the standard-only refutation"

run_meta do
  -- A candidate may reference a fresh theorem before export. After extraction
  -- and complete rollback, the returned expression must use only old constants.
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let exported ← try
    let prefixName := (← getEnv).asyncPrefix?.getD `Leant2Tests.API
    let name := prefixName ++ (← mkFreshUserName `temporaryProof)
    addDecl (.thmDecl {
      name, levelParams := [], type := mkConst ``True
      value := mkConst ``True.intro })
    API.exportCandidate originalCore originalMeta .strictConstructive {
      program := mkConst name, programType := mkConst ``True, levelParams := [],
      proof := mkConst ``True.intro, axioms := #[], classical := false }
  finally
    modifyThe Meta.State fun _ => originalMeta
    modifyThe Core.State fun _ => originalCore
  replay exported .strictConstructive
  unless exported.program == Lean.mkConst ``True.intro do
    throwError "new theorem body was not extracted"

run_meta do
  -- Specialization of a fresh theorem's universe arguments must be applied to
  -- its body before rollback, and no undeclared level may survive extraction.
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let target ← mkEq (mkNatLit 0) (mkNatLit 0)
  let exported ← try
    let prefixName := (← getEnv).asyncPrefix?.getD `Leant2Tests.API
    let name := prefixName ++ (← mkFreshUserName `polymorphicProof)
    let (type, proof) ← withLocalDeclD `A (mkSort (.param `u)) fun a =>
      withLocalDeclD `x a fun x => do
        return (← mkForallFVars #[a, x] (← mkEq x x),
          ← mkLambdaFVars #[a, x] (← mkEqRefl x))
    addDecl (.thmDecl { name, levelParams := [`u], type, value := proof })
    API.exportCandidate originalCore originalMeta .strictConstructive {
      program := mkApp2 (mkConst name [.succ .zero]) (mkConst ``Nat) (mkNatLit 0),
      programType := target, levelParams := [], proof := mkConst ``True.intro,
      axioms := #[], classical := false }
  finally
    modifyThe Meta.State fun _ => originalMeta
    modifyThe Core.State fun _ => originalCore
  replay exported .strictConstructive
  unless exported.levelParams.isEmpty &&
      (collectLevelParams {} exported.program).params.isEmpty &&
      (← isDefEq (← inferType exported.program) target) do
    throwError "export changed theorem type or left an undeclared universe parameter"

run_meta do
  -- An independently well-typed proof of True is still the wrong proof for an
  -- original Nat equality contract. This is an output validation exception.
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let contract ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkLambdaFVars #[n] (← mkEq n (mkNatLit 0))
  let rejected ← try
    discard <| API.exportCandidate originalCore originalMeta .strictConstructive {
      program := mkNatLit 0, programType := mkConst ``Nat, levelParams := [],
      proof := mkConst ``True.intro, axioms := #[], classical := false }
      (some { target := mkConst ``Nat, contract := some contract })
    pure false
  catch ex =>
    if Leant2.isInterrupt ex then throw ex
    pure true
  unless rejected do throwError "export accepted evidence for a different contract"

run_meta do
  -- Output transport failure is an exception, not preflightError or a bounded
  -- search negative. New axioms cannot be imported by transport, even if the
  -- chosen project-relative profile happens to list that new name.
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  try
    let prefixName := (← getEnv).asyncPrefix?.getD `Leant2Tests.API
    let name := prefixName ++ (← mkFreshUserName `temporaryAxiom)
    addDecl (.axiomDecl { name, levelParams := [], type := mkConst ``True, isUnsafe := false })
    let rejected ← try
      discard <| API.exportCandidate originalCore originalMeta (.projectRelative [name]) {
        program := mkConst name, programType := mkConst ``True, levelParams := [],
        proof := mkConst ``True.intro, axioms := #[name], classical := false }
      pure false
    catch ex =>
      if Leant2.isInterrupt ex then throw ex
      pure true
    unless rejected do throwError "API exported a fresh axiom"
  finally
    modifyThe Meta.State fun _ => originalMeta
    modifyThe Core.State fun _ => originalCore

run_meta do
  let certificate : Accepted := {
    program := mkConst ``True.intro, programType := mkConst ``True,
    levelParams := [], proof := mkConst ``True.intro, axioms := #[], classical := false }
  let query : Query := { target := mkConst ``Nat, profile := .strictConstructive }
  expectOutputError query (.verified #[] {})
  expectOutputError query (.negative .impossible none {})
  expectOutputError query (.negative .impossible (some certificate) {})
  expectOutputError query (.negative .contractImpossible (some certificate) {})
  expectOutputError query (.negative .budgetExhausted (some certificate) {})
  expectOutputError query (.negative .grammarExhausted (some certificate) {})
  let contract := mkLambda `n .default (mkConst ``Nat) (mkConst ``False)
  let query := { query with contract := some contract }
  expectOutputError query (.negative .contractImpossible none {})
  expectOutputError query (.negative .contractImpossible (some certificate) {})

run_meta do
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let wrongType : Accepted := {
    program := mkNatLit 0, programType := mkConst ``Nat, levelParams := []
    proof := mkConst ``True.intro, axioms := #[], classical := false }
  expectOutputError { target := mkConst ``Bool, profile := .strictConstructive }
    (.verified #[wrongType] {})
  let target := mkForall `A .default (mkSort (.param `u))
    (mkForall `x .default (.bvar 0) (.bvar 1))
  let specialized := target.instantiateLevelParams [`u] [.zero]
  let candidate : Accepted := {
    program := mkLambda `A .default (mkSort .zero)
      (mkLambda `x .default (.bvar 0) (.bvar 0))
    programType := specialized, levelParams := []
    proof := mkConst ``True.intro, axioms := #[], classical := false }
  let contract := mkLambda `f .default target (mkConst ``False)
  expectOutputError { target, contract := some contract, profile := .strictConstructive }
    (.verified #[candidate] {})
  let positiveContract := mkLambda `f .default target (mkConst ``True)
  let .verified exported _ ← API.exportOutcome originalCore originalMeta {
      target, contract := some positiveContract, profile := .strictConstructive }
      (.verified #[candidate] {})
    | throwError "valid specialized-contract positive control failed"
  unless exported[0]!.programType == specialized do
    throwError "specialized-contract export changed the actual program type"

run_meta do
  -- Only the contract carries this universe: the actual Nat program type
  -- stays unchanged, so checking programType alone cannot recover the original
  -- polymorphic contract. Replay the returned proof's actual type separately.
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let statement ← withLocalDeclD `A (mkSort (.param `u)) fun a => do
    let nonempty := mkApp (mkConst ``Nonempty [.param `u]) a
    mkForallFVars #[a] (← mkArrow nonempty nonempty)
  let contract := mkLambda `n .default (mkConst ``Nat) statement
  let specialized := statement.instantiateLevelParams [`u] [.zero]
  let proof ← forallTelescope specialized fun locals _ => mkLambdaFVars locals locals[1]!
  let candidate : Accepted := {
    program := mkNatLit 0, programType := mkConst ``Nat, levelParams := []
    proof, axioms := #[], classical := false }
  let query : Query := {
    target := mkConst ``Nat, contract := some contract, profile := .strictConstructive }
  let originalProof ← forallTelescope statement fun locals _ => mkLambdaFVars locals locals[1]!
  let originalCandidate := { candidate with proof := originalProof, levelParams := [`u] }
  let .verified originalExported _ ← API.exportOutcome originalCore originalMeta query
      (.verified #[originalCandidate] {})
    | throwError "original polymorphic-contract positive control failed"
  unless originalExported[0]!.levelParams == [`u] &&
      (← isDefEq (← inferType originalExported[0]!.proof) statement) do
    throwError "export changed the original proof type or its universe parameter"
  let .verified exported _ ← API.exportOutcome originalCore originalMeta query
      (.verified #[candidate] {})
    | throwError "contract-only specialization positive control failed"
  unless exported[0]!.programType == query.target &&
      (← isDefEq (← inferType exported[0]!.proof) specialized) do
    throwError "contract-only specialization lost its actual proof type"
  unless (← kernelCheckAndAudit `Leant2Tests.API exported[0]!.proof
      (mkApp contract exported[0]!.program) [`u] true) matches .error _ do
    throwError "specialized proof unexpectedly established the original contract"
  expectOutputError query (.verified #[{ candidate with proof := mkConst ``True.intro }] {})

axiom unusedContractPremise : Nat

run_meta do
  -- A definitionally irrelevant term in the original contract still belongs
  -- to the audited statement. Captured proof-type audit alone would miss it.
  let candidate : Accepted := {
    program := mkNatLit 0, programType := mkConst ``Nat, levelParams := []
    proof := mkConst ``True.intro, axioms := #[], classical := false }
  let contract := mkLambda `n .default (mkConst ``Nat)
    (mkLet `unused (mkConst ``Nat) (mkConst ``unusedContractPremise) (mkConst ``True))
  let query : Query := {
    target := mkConst ``Nat, contract := some contract, profile := .strictConstructive }
  expectOutputError query (.verified #[candidate] {})
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let .verified exported _ ← API.exportOutcome originalCore originalMeta
      { query with profile := .projectRelative [``unusedContractPremise] }
      (.verified #[candidate] {})
    | throwError "project-relative original-contract positive control failed"
  unless exported[0]!.axioms.contains ``unusedContractPremise do
    throwError "original contract dependency was omitted from the audit"

run_meta do
  let originalCore ← getThe Core.State
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let token ← IO.CancelToken.new
  token.set
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  let interrupted ← try
    withTheReader Core.Context (fun ctx => { ctx with cancelTk? := some token }) do
      discard <| Leant2.synthesize { target := mkConst ``Nat }
    pure false
  catch ex => pure ex.isInterrupt
  unless interrupted && !(← pending.mvarId!.isAssigned) &&
      (← getEnv).constants.map₂.toList.map Prod.fst ==
        originalCore.env.constants.map₂.toList.map Prod.fst do
    throwError "API swallowed cancellation or changed caller state"

inductive RankingInterrupt where
  | value

run_meta do
  -- The native pretty-printer executes in an isolated IO context and catches
  -- delaborator exceptions. A local ppExt callback instead cancels the actual
  -- query token after observing metavariables created by real search.
  let token ← IO.CancelToken.new
  let reachedRanking ← IO.mkRef false
  let searchMutated ← IO.mkRef false
  let beforeHookCore ← getThe Core.State
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let originalMeta ← getThe Meta.State
  let printers := ppExt.getState (← getEnv)
  modifyEnv fun env => ppExt.setState env { printers with
    ppExprWithInfos := fun ctx e => do
      if e == Lean.mkConst ``RankingInterrupt.value then
        reachedRanking.set true
        searchMutated.set (ctx.mctx.mvarCounter > originalMeta.mctx.mvarCounter)
        token.set
      printers.ppExprWithInfos ctx e }
  let originalCore ← getThe Core.State
  try
    let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
    let interrupted ← try
      withTheReader Core.Context (fun ctx => { ctx with cancelTk? := some token }) do
        discard <| Leant2.synthesize {
          target := mkConst ``RankingInterrupt
          profile := .strictConstructive, budgetMs := 1000, maxCandidates := 1, graceMs := 0 }
      pure false
    catch ex => pure ex.isInterrupt
    unless interrupted && (← reachedRanking.get) && (← searchMutated.get) do
      throwError "API did not propagate ranking cancellation after real search mutations"
    unless !(← pending.mvarId!.isAssigned) &&
        (← getMCtx).mvarCounter == originalMeta.mctx.mvarCounter &&
        (← getEnv).constants.map₂.toList.map Prod.fst ==
          originalCore.env.constants.map₂.toList.map Prod.fst &&
        (← getThe Core.State).messages.toList.length == originalCore.messages.toList.length do
      throwError "mid-query API interruption leaked speculative state"
  finally
    modifyThe Meta.State fun _ => originalMeta
    modifyThe Core.State fun _ => beforeHookCore

end Leant2Tests.LibraryAPI
