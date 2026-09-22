import Leant2.Frontend.Sketch

/-! Whole-program completion and original-query replay. Provider inventories
are explicit; known witnesses and observers are not synthesis providers. Native
preparation/closure and joint-enumeration tests live in separate modules. -/

namespace Leant2Tests.Sketch
open Lean Meta Elab Term Leant2 Frontend.Sketch
universe u v

private def query (target : TSyntax `term) (contract : Option (TSyntax `term) := none)
    (providers : Array Name := #[]) : TermElabM Query := do
  let target ← elabType target
  let contract ← contract.mapM fun stx => elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  return {
    target := ← instantiateMVars target
    contract := ← contract.mapM instantiateMVars
    profile := .strictConstructive, providers
    budgetMs := 5000, maxCandidates := 1, graceMs := 0 }

private def first (result : Result) (holes : Nat) : TermElabM Accepted := do
  unless result.preparation.holes.size == holes do throwError "wrong prepared-hole count"
  let .verified candidates _ := result.outcome
    | throwError "sketch completion failed: {← outcomeMessage result.outcome}"
  let some candidate := candidates[0]? | throwError "empty verified sketch result"
  return candidate

private def replay (query : Query) (candidate : Accepted) : MetaM Unit := do
  unless ← isDefEq candidate.programType query.target do
    throwError "completion changed the original target"
  let .ok programAxioms ← kernelCheckAndAudit `Leant2Tests.Sketch
      candidate.program query.target candidate.levelParams false
    | throwError "completion does not independently replay at the original type"
  let proofAxioms ← match query.contract with
    | none => pure #[]
    | some contract => do
      let .ok axioms ← kernelCheckAndAudit `Leant2Tests.Sketch candidate.proof
          (mkApp contract candidate.program) candidate.levelParams true
        | throwError "completion proof does not establish the original whole contract"
      pure axioms
  unless (programAxioms ++ proofAxioms).all query.profile.allowedAxioms.contains do
    throwError "completion violated the requested axiom profile"
  unless (programAxioms ++ proofAxioms).all candidate.axioms.contains do
    throwError "completion omitted an original-statement axiom dependency"

run_elab do
  let q ← query (← `(∀ A : Type, A → A))
    (some (← `(fun f : ∀ A : Type, A → A => ∀ A x, f A x = x)))
  let candidate ← first (← synthesizeSketch q
    (← `(fun (A : Type) (value : A) => (?body : A)))) 1
  replay q candidate

run_elab do
  -- Independent named universes are fixed by the original target. The one
  -- owned pending goal lives under four native binders and closure wrappers.
  let uLevel : TSyntax `level := ⟨(mkIdent `u).raw⟩
  let vLevel : TSyntax `level := ⟨(mkIdent `v).raw⟩
  withLevelNames [`u, `v] do
  let q ← query (← `(∀ (A : Sort $uLevel) (B : Sort $vLevel), A → B → A))
  let candidate ← first (← synthesizeSketch q
    (← `(fun (A : Sort $uLevel) (B : Sort $vLevel) (a : A) (_b : B) => (?body : A)))) 1
  replay q candidate
  unless candidate.levelParams.contains `u && candidate.levelParams.contains `v do
    throwError "completion lost one of the original universe parameters"

run_elab do
  -- Neither the closed step nor seed sees xs; the fixed fold cannot be
  -- bypassed by simply returning an observed list argument from a hole.
  let q ← query (← `(List Nat → Nat))
    (some (← `(fun f : List Nat → Nat =>
      f [] = 1 ∧ f [2] = 3 ∧ f [2, 3] = 6 ∧ f [0, 4, 0] = 5))) #[``Nat.add]
  let candidate ← first (← synthesizeSketch q (← `(
    (fun (step : Nat → Nat → Nat) (init : Nat) (xs : List Nat) =>
      List.foldr step init xs) ?step ?init))) 2
  replay q candidate
  let contract ← elabTerm (← `(fun f : List Nat → Nat => f [5, 8] = 14 ∧ f [0, 0] = 1)) none
  synthesizeSyntheticMVarsNoPostponing
  let contract ← instantiateMVars contract
  let obligation ← mkFreshExprMVar (contract.beta #[candidate.program])
  unless ← tacticProve obligation.mvarId! do throwError "held-out fold observations failed"
  let .ok _ ← gate .strictConstructive candidate.program q.target
      (some (← instantiateMVars obligation, mkApp contract candidate.program))
    | throwError "held-out fold proof did not independently replay"

run_elab do
  -- The public provider inventory includes List.length before binary Nat.add.
  -- Completing the smaller seed interface first keeps this real two-hole
  -- continuation productive without dropping any provider or changing the body.
  let q ← query (← `(List Nat → Nat))
    (some (← `(fun f : List Nat → Nat =>
      f [] = 1 ∧ f [2] = 3 ∧ f [2, 3] = 6 ∧ f [0, 4, 0] = 5))) curatedProviders
  let q := { q with maxCandidates := 12, graceMs := 400 }
  let candidate ← first (← synthesizeSketch q (← `(
    (fun (step : Nat → Nat → Nat) (init : Nat) (xs : List Nat) =>
      List.foldr step init xs) ?step ?init))) 2
  replay q candidate

run_elab do
  let q ← query (← `(Nat)) (some (← `(fun n : Nat => n = 1)))
  let candidate ← first (← synthesizeSketch q (← `(1))) 0
  replay q candidate
  let wrong ← synthesizeSketch q (← `(0))
  unless wrong.preparation.holes.isEmpty do throwError "invented a hole in supplied complete body"
  match wrong.outcome with
  | .refutedAll count _ => unless count > 0 do throwError "no fixed-body rejection was recorded"
  | .negative .grammarExhausted none _ | .negative .budgetExhausted none _ => pure ()
  | _ => throwError "wrong fixed body was accepted or claimed universally impossible"

run_elab do
  let q ← query (← `(Nat)) (some (← `(fun _ : Nat => False)))
  let result ← synthesizeSketch q (← `(?body))
  let .negative .contractImpossible (some certificate) _ := result.outcome
    | throwError "False sketch contract was not independently certified impossible"
  let expected ← withLocalDeclD `f q.target fun f =>
    mkForallFVars #[f] (mkApp (mkConst ``Not) (mkApp q.contract.get! f))
  let .ok axioms ← kernelCheckAndAudit `Leant2Tests.Sketch certificate.program
      expected certificate.levelParams true
    | throwError "sketch contract-refutation certificate did not replay"
  unless axioms.isEmpty do throwError "literal False refutation used axioms"

axiom fixedProgram : Nat
axiom originalContractDependency : Nat

run_elab do
  let q ← query (← `(Nat))
  let source ← `(fixedProgram)
  for profile in [.strictConstructive, .standard] do
    if (← synthesizeSketch { q with profile } source).outcome matches .verified .. then
      throwError "fixed sketch source bypassed the requested axiom profile"
  let q := { q with profile := .projectRelative [``fixedProgram] }
  let candidate ← first (← synthesizeSketch q source) 0
  replay q candidate
  unless candidate.axioms.contains ``fixedProgram do throwError "fixed dependency was omitted"

run_elab do
  let q ← query (← `(Nat))
  let contract := mkLambda `f .default q.target
    (mkLet `unused (mkConst ``Nat) (mkConst ``originalContractDependency) (mkConst ``True))
  let q := { q with contract := some contract }
  if (← synthesizeSketch q (← `(0))).outcome matches .verified .. then
    throwError "completion erased an axiom in the original contract syntax"
  let q := { q with profile := .projectRelative [``originalContractDependency] }
  let candidate ← first (← synthesizeSketch q (← `(0))) 0
  replay q candidate

private def observeAll (action : TermElabM α) : TermElabM (Except Exception α) := do
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch ex => return .error ex

private unsafe def isolated (action : TermElabM α) : TermElabM (Except Exception α) := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  let termState ← getThe Term.State
  let result ← observeAll action
  unless ptrEq coreState (← getThe Core.State) && ptrEq metaState (← getThe Meta.State) &&
      ptrEq termState (← getThe Term.State) do
    throwError "sketch controller changed the caller's exact Core/Meta/Term records"
  return result

run_elab do
  let q ← query (← `(Nat))
  let source ← `((?body : Nat))
  let caller ← mkFreshExprMVar (mkConst ``Nat) .natural `body
  let level ← mkFreshLevelMVar
  let .ok result ← isolated (synthesizeSketch q source)
    | throwError "isolated synthesis failed"
  replay q (← first result 1)
  unless !(← caller.mvarId!.isAssigned) && (← instantiateLevelMVars level) == level do
    throwError "sketch completion assigned an unrelated caller hole"
  let malformed ← `((?same, ?same))
  let product ← mkAppM ``Prod #[q.target, q.target]
  let .error ex ← isolated (synthesizeSketch { q with target := product } malformed)
    | throwError "duplicate named holes were accepted"
  unless (← ex.toMessageData.toString).startsWith "leant2 sketch: preparation failed:" do
    throwError "preparation failure was misclassified as a bounded miss"
  let token ← IO.CancelToken.new
  token.set
  let .error ex ← isolated <| withTheReader Core.Context
      (fun context => { context with cancelTk? := some token }) (synthesizeSketch q source)
    | throwError "pre-cancelled sketch synthesis succeeded"
  unless ex.isInterrupt do throwError "sketch controller swallowed native cancellation"

run_elab do
  let q ← query (← `(Nat))
  let source ← `(0)
  let hole ← mkFreshExprMVar (mkSort (.succ .zero))
  let level ← mkFreshLevelMVar
  let unknown := `Leant2Tests.Sketch.unavailableProvider
  if (← getEnv).contains unknown then throwError "invalid provider fixture unexpectedly exists"
  let nonProp := mkLambda `n .default q.target (mkNatLit 0)
  let invalid := [
    { q with target := mkNatLit 0 },
    { q with target := hole },
    { q with target := mkSort level },
    { q with contract := some nonProp },
    { q with providers := #[unknown] },
    { q with maxCandidates := 0 }]
  for malformed in invalid do
    let .error ex ← isolated (synthesizeSketch malformed source)
      | throwError "malformed native sketch query reached completion"
    unless (← ex.toMessageData.toString).startsWith "leant2 sketch: preparation failed:" do
      throwError "malformed native query was not classified as preparation failure"
  unless !(← hole.mvarId!.isAssigned) && (← instantiateLevelMVars level) == level do
    throwError "malformed query validation assigned incoming holes"

inductive RankingInterrupt where
  | value

run_elab do
  -- Native pretty-printing has its own exception recovery. Capture the real
  -- cancellation token and set it after observing actual search mutations;
  -- the controller must check it again before returning a portable outcome.
  let q ← query (← `(RankingInterrupt))
  let source ← `((?body : RankingInterrupt))
  let token ← IO.CancelToken.new
  let reached ← IO.mkRef false
  let mutated ← IO.mkRef false
  let beforeHookCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let printers := ppExt.getState (← getEnv)
  modifyEnv fun env => ppExt.setState env { printers with
    ppExprWithInfos := fun context expression => do
      if expression == Lean.mkConst ``RankingInterrupt.value then
        reached.set true
        mutated.set (context.mctx.mvarCounter > originalMeta.mctx.mvarCounter)
        token.set
      printers.ppExprWithInfos context expression }
  try
    let .error ex ← isolated <| withTheReader Core.Context
        (fun context => { context with cancelTk? := some token }) (synthesizeSketch q source)
      | throwError "completion returned after ranking cancelled the query"
    unless ex.isInterrupt && (← reached.get) && (← mutated.get) do
      throwError "completion did not propagate cancellation after real search work"
  finally
    modifyThe Meta.State fun _ => originalMeta
    modifyThe Core.State fun _ => beforeHookCore

end Leant2Tests.Sketch
