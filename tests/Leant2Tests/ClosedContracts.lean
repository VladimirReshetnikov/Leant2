import Leant2

/-! Exact closed-root residual checks are distinct from partial observations and
local proof search. These fixtures build native Subtype goals, retain their
original proof obligations, and check both evaluator outcomes and continuation
transactions. Reference proofs are never providers for the tested search. -/
namespace Leant2Tests.ClosedContracts

open Lean Meta Elab Term Leant2

private def context : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def observeAll (action : MetaM α) : MetaM (Except Exception α) := do
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch ex => return .error ex

private structure Fixture where
  root : Expr
  program : MVarId
  proof : MVarId
  cfg : SearchConfig

private def makeRoot (type contract : Expr) : MetaM Fixture := do
  let root ← mkFreshExprMVar (← mkAppM ``Subtype #[contract])
  let children ← root.mvarId!.apply (← mkConstWithFreshMVarLevels ``Subtype.mk)
    { newGoals := .all, synthAssignedInstances := false, allowSynthFailures := true }
  unless children.length == 2 do throwError "fixture did not produce native program/property goals"
  return {
    root
    program := children[0]!
    proof := children[1]!
    cfg := { root := some root.mvarId!, contract := some contract,
             residual := ← mkResidual contract type } }

private def closedRoot (program contract : Expr) : MetaM Fixture := do
  let fixture ← makeRoot (← inferType program) contract
  fixture.program.assign program
  return fixture

private def zeroContract : Expr :=
  mkLambda `n .default (mkConst ``Nat)
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (.bvar 0) (mkNatLit 0))

private def constantContract (type proposition : Expr) : Expr :=
  mkLambda `candidate .default type proposition

private def requireIneligible (ctx : SearchCtx) (cfg : SearchConfig) (g : MVarId) : MetaM Unit := do
  let before ← getMCtx
  let result ← (evalClosedRootContract cfg g).run ctx
  unless result.isNone do throwError "ineligible exact-root check ran"
  let ledger ← ctx.ledger.get
  unless ledger.proofAttempts == 0 && ledger.rejected == 0 &&
      (← ctx.refutedPrograms.get).isEmpty && (← ctx.observationCache.get).isEmpty do
    throwError "ineligible exact-root check changed accounting or observation state"
  if (← getMCtx).mvarCounter != before.mvarCounter ||
      (← getMCtx).lmvarCounter != before.lmvarCounter then
    throwError "ineligible exact-root check introduced metavariables"

run_meta do
  let fixture ← closedRoot (mkNatLit 1) zeroContract
  let ctx ← context
  for _ in [:2] do
    let some .refuted ← (evalClosedRootContract fixture.cfg fixture.proof).run ctx
      | throwError "false exact closed contract was not refuted"
  let ledger ← ctx.ledger.get
  unless ledger.proofAttempts == 2 && ledger.rejected == 1 &&
      (← ctx.refutedPrograms.get).contains (mkNatLit 1) do
    throwError "exact closed refutation attempt/cache accounting changed"
  if ← fixture.proof.isAssigned then throwError "refutation assigned the proof goal"
  if ← (search fixture.cfg (pure true) 0 [{ mvar := fixture.proof, depth := 1 }]).run ctx then
    throwError "refuted closed root reached the leaf"
  unless (← ctx.ledger.get).rejected == 1 do throwError "cached refutation was counted again"

run_meta do
  let fixture ← closedRoot (mkNatLit 0) zeroContract
  let ctx ← context
  let found ← (search fixture.cfg (pure true) 0 [{ mvar := fixture.proof, depth := 1 }]).run ctx
  unless found do throwError "true exact closed contract was not solved"
  let proof ← instantiateMVars (mkMVar fixture.proof)
  let target ← instantiateMVars (← fixture.proof.getType)
  let .ok _ ← gate .strictConstructive proof target none
    | throwError "early contract proof failed final strict kernel/profile gate"
  let ledger ← ctx.ledger.get
  unless ledger.proofAttempts == 1 && ledger.rejected == 0 &&
      (← ctx.refutedPrograms.get).isEmpty do
    throwError "successful exact contract was charged/refuted incorrectly"

run_meta do
  -- The early canonical proof is only one alternative. Its rejection must
  -- restore the goal and permit an ordinary refl proof of the same target.
  let fixture ← closedRoot (mkNatLit 0) zeroContract
  let ctx ← context
  let sawDecider ← IO.mkRef false
  let sawRefl ← IO.mkRef false
  let leaf : Leaf := do
    let proof ← instantiateMVars (mkMVar fixture.proof)
    if proof.getAppFn.isConstOf ``of_decide_eq_true then
      sawDecider.set true
      return false
    if proof.getAppFn.isConstOf ``Eq.refl then
      sawRefl.set true
      return true
    return false
  unless ← (search fixture.cfg leaf 0 [{ mvar := fixture.proof, depth := 1 }]).run ctx do
    throwError "rejected canonical proof suppressed an ordinary proof alternative"
  unless (← sawDecider.get) && (← sawRefl.get) do
    throwError "fixture did not exercise both canonical and ordinary proof shapes"

run_meta do
  -- A different closed sibling proposition is not the root contract.
  let fixture ← closedRoot (mkNatLit 1) zeroContract
  let sibling ← mkFreshExprMVar (mkConst ``True)
  let ctx ← context
  requireIneligible ctx fixture.cfg sibling.mvarId!
  unless ← (search fixture.cfg (pure true) 0 [{ mvar := sibling.mvarId!, depth := 1 }]).run ctx do
    throwError "unrelated True sibling was pruned by the root's false contract"
  unless (← ctx.ledger.get).rejected == 0 do throwError "sibling search cached a root refutation"

run_meta do
  -- Even when the requested target matches cfg.contract, the actual Subtype
  -- predicate must match; stale/cross-root configuration is ineligible.
  let fixture ← closedRoot (mkNatLit 1) zeroContract
  let contract := constantContract (mkConst ``Nat) (mkConst ``True)
  let cfg := { fixture.cfg with contract := some contract, residual := ← mkResidual contract (mkConst ``Nat) }
  let sibling ← mkFreshExprMVar (mkConst ``True)
  let ctx ← context
  requireIneligible ctx cfg sibling.mvarId!

run_meta do
  -- Native induction creates an actual delayed/partial function assignment.
  -- A closed, constant property must not cause the remaining program hole to
  -- be treated as a fully native closed root.
  let type ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let contract := constantContract type (mkConst ``True)
  let fixture ← makeRoot type contract
  let (n, body) ← fixture.program.intro1P
  let branches ← body.induction n ``Nat.rec
  unless branches.size == 2 do throwError "native open-root fixture needs two branches"
  branches[0]!.mvarId.assign (mkNatLit 0)
  let ctx ← context
  requireIneligible ctx fixture.cfg fixture.proof
  if ← branches[1]!.mvarId.isAssigned then throwError "open program branch was filled by contract check"
  -- An entirely unassigned root is also ineligible.
  let emptyRoot ← mkFreshExprMVar (← fixture.root.mvarId!.getType)
  requireIneligible ctx { fixture.cfg with root := some emptyRoot.mvarId! } fixture.proof

run_meta do
  -- Unresolved universe dependencies are not a closed program/type.
  let level ← mkFreshLevelMVar
  let type := Lean.mkConst ``PUnit [level]
  let program := Lean.mkConst ``PUnit.unit [level]
  let fixture ← closedRoot program (constantContract type (mkConst ``True))
  let ctx ← context
  requireIneligible ctx fixture.cfg fixture.proof
  if (getLevelMVarAssignmentExp (← getMCtx) level.mvarId!).isSome then
    throwError "closure test assigned an incoming universe"

run_meta do
  -- Both absence of precomputed residuals and explicit portfolio ablation
  -- preserve ordinary construction without exact-root accounting.
  for disabled in [false, true] do
    let fixture ← closedRoot (mkNatLit 0) zeroContract
    let cfg := if disabled then { fixture.cfg with proofPortfolio := false }
      else { fixture.cfg with residual := #[] }
    let ctx ← context
    requireIneligible ctx cfg fixture.proof
    unless ← (search cfg (pure true) 0 [{ mvar := fixture.proof, depth := 1 }]).run ctx do
      throwError "disabled exact evaluator suppressed ordinary reflexivity"
    unless (← ctx.ledger.get).rejected == 0 do throwError "disabled evaluator refuted a program"

run_meta do
  -- A missing supplied decider is stuck, not a license to prune; ordinary
  -- proof construction is still available.
  let fixture ← closedRoot (mkNatLit 0) zeroContract
  let cfg := { fixture.cfg with residual := #[(zeroContract, none)] }
  let ctx ← context
  let some .stuck ← (evalClosedRootContract cfg fixture.proof).run ctx
    | throwError "missing residual decider did not preserve stuck result"
  unless (← ctx.ledger.get).proofAttempts == 1 && (← ctx.ledger.get).rejected == 0 do
    throwError "stuck residual accounting changed"
  unless ← (search cfg (pure true) 0 [{ mvar := fixture.proof, depth := 1 }]).run ctx do
    throwError "stuck residual suppressed ordinary proof construction"

opaque opaqueTrueDecider : Decidable True := isTrue True.intro

private noncomputable def classicalTrueDecider (n : Nat) : Decidable (n = n) :=
  isTrue (Classical.choice (show Nonempty (n = n) from ⟨rfl⟩))

run_meta do
  -- Kernel reduction can see the isTrue constructor without using its proof.
  -- The original strict gate still rejects the canonical proof's classical
  -- dependency, and the search must then find an ordinary constructive proof.
  let contract := mkLambda `n .default (mkConst ``Nat)
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (.bvar 0) (.bvar 0))
  let fixture ← closedRoot (mkNatLit 0) contract
  let cfg := { fixture.cfg with residual := #[(contract, some (mkConst ``classicalTrueDecider))] }
  let ctx ← context
  let rejectedCanonical ← IO.mkRef false
  let acceptedOrdinary ← IO.mkRef false
  let leaf : Leaf := do
    let proof ← instantiateMVars (mkMVar fixture.proof)
    let target ← instantiateMVars (← fixture.proof.getType)
    match ← gate .strictConstructive proof target none with
    | .error _ =>
      if proof.getAppFn.isConstOf ``of_decide_eq_true then rejectedCanonical.set true
      return false
    | .ok _ =>
      if proof.getAppFn.isConstOf ``Eq.refl then acceptedOrdinary.set true
      return true
  unless ← (search cfg leaf 0 [{ mvar := fixture.proof, depth := 1 }]).run ctx do
    throwError "strict rejection of the canonical proof suppressed constructive fallback"
  unless (← rejectedCanonical.get) && (← acceptedOrdinary.get) do
    throwError "strict-profile fixture did not reject classical evidence then accept reflexivity"

run_meta do
  -- Once a supplied exact residual is stuck, later generic proof work remains
  -- available and receives its own charge; it does not retry the exact residual.
  let fixture ← closedRoot (mkNatLit 0) zeroContract
  let cfg := { fixture.cfg with residual := #[(zeroContract, none)] }
  let ctx ← context
  let some .stuck ← (evalClosedRootContract cfg fixture.proof).run ctx
    | throwError "generic fallback fixture needs a stuck exact residual"
  unless ← (proofPortfolio cfg fixture.proof (exactContractTried := true)).run ctx do
    throwError "stuck exact check disabled generic proof work"
  unless (← ctx.ledger.get).proofAttempts == 2 && (← ctx.ledger.get).rejected == 0 do
    throwError "generic proof work after a stuck exact check was not separately accounted"

run_meta do
  let contract := constantContract (mkConst ``Nat) (mkConst ``True)
  let fixture ← closedRoot (mkNatLit 0) contract
  let supplied := mkLambda `n .default (mkConst ``Nat) (mkConst ``opaqueTrueDecider)
  let cfg := { fixture.cfg with residual := #[(contract, some supplied)] }
  let ctx ← context
  let some .stuck ← (evalClosedRootContract cfg fixture.proof).run ctx
    | throwError "opaque supplied decider was replaced by an invented decider"
  if ← fixture.proof.isAssigned then throwError "stuck opaque decider assigned a proof"
  unless ← (search cfg (pure true) 0 [{ mvar := fixture.proof, depth := 1 }]).run ctx do
    throwError "opaque-decider fallback could not use True.intro"

run_meta do
  -- Closed false equality may still be provable in an inconsistent local
  -- context. Only LocalProof/ordinary search may discharge that obligation.
  withLocalDeclD `contradiction (mkConst ``False) fun _ => do
    let fixture ← closedRoot (mkNatLit 1) zeroContract
    let ctx ← context
    requireIneligible ctx fixture.cfg fixture.proof
    unless ← (search fixture.cfg (pure true) 0 [{ mvar := fixture.proof, depth := 2 }]).run ctx do
      throwError "nonempty local context failed to reach contradiction proof service"
    unless (← ctx.refutedPrograms.get).isEmpty && (← ctx.ledger.get).rejected == 0 do
      throwError "local contradiction was globally cached as a refutation"

run_meta do
  let fixture ← closedRoot (mkNatLit 0) zeroContract
  let sibling ← mkFreshExprMVar (mkConst ``False)
  let ctx ← context
  if ← (search fixture.cfg (pure true) 0
      [{ mvar := fixture.proof, depth := 1 }, { mvar := sibling.mvarId!, depth := 0 }]).run ctx then
    throwError "early proved contract bypassed an unsolved sibling"
  if (← fixture.proof.isAssigned) || (← sibling.mvarId!.isAssigned) then
    throwError "rejected proof continuation leaked an assignment"

run_meta do
  -- Native cancellation after the leaf returns must be observed even when
  -- there are no remaining search goals, and restore the assigned proof.
  for stop in [false, true] do
    let fixture ← closedRoot (mkNatLit 0) zeroContract
    let ctx ← context
    let token ← IO.CancelToken.new
    let visited ← IO.mkRef false
    let result ← observeAll <| withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
      (search fixture.cfg (do visited.set true; token.set; return stop) 0
        [{ mvar := fixture.proof, depth := 1 }]).run ctx
    let .error ex := result | throwError "early proof continuation swallowed cancellation"
    unless ex.isInterrupt && (← visited.get) do throwError "cancellation fixture did not reach its leaf"
    if ← fixture.proof.isAssigned then throwError "cancelled early proof was committed"

end Leant2Tests.ClosedContracts
