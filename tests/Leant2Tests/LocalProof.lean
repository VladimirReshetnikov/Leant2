import Leant2.Proof.Local

/-!
Exercise the proof service directly in exact original goals and verify its
isolation on successful, failed, exhausted, and interrupted tactic attempts.
Public query acceptance is tested separately from these service-level checks.
-/
namespace Leant2Tests.LocalProof

open Lean Meta Elab Term Leant2
open Leant2.LocalProof

private def context : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def requireSolved (result : Result) : MetaM Expr := do
  match result with
  | .solved proof => return proof
  | .unresolved => throwError "local proof service left the goal unresolved"
  | .unsupportedDependency => throwError "local proof service refused a dependency"
  | .resourceExhausted => throwError "local proof service exhausted its local budget"

private def requireUnresolved (result : Result) : MetaM Unit := do
  let .unresolved := result | throwError "expected an unresolved proof attempt"

private def requireUnsupported (result : Result) : MetaM Unit := do
  let .unsupportedDependency := result | throwError "open dependency was not suspended"

private def requireResource (result : Result) : MetaM Unit := do
  let .resourceExhausted := result | throwError "local resource exhaustion was misclassified"

private def gateOriginal (term target : Expr) : MetaM Unit := do
  let term ← instantiateMVars term
  if term.hasExprMVar || term.hasFVar || term.hasSorry then
    throwError "original goal did not become a closed proof/program"
  let .ok accepted ← gate .standard term target none
    | throwError "kernel/axiom gate rejected the original target"
  unless ← withNewMCtxDepth (isDefEq accepted.programType target) do
    throwError "proof service changed the original requested type"

private def proveIntroduced (target : Expr) : MetaM Unit := do
  let original ← mkFreshExprMVar target
  let mut goal := original.mvarId!
  while (← goal.withContext <| whnf (← goal.getType)).isForall do
    let (_, next) ← goal.intro1P
    goal := next
  let ctx ← context
  discard <| requireSolved (← (discharge goal).run ctx)
  gateOriginal original target

run_elab do
  -- Ordinary construction supplies the Fin value; the local service proves
  -- its bound. No Nat.zero_lt_succ proof provider is registered.
  let target ← elabType (← `(∀ n : Nat, Fin (n + 1)))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let original ← mkFreshExprMVar target
  let (_, finGoal) ← original.mvarId!.intro1P
  let children ← finGoal.withContext do
    finGoal.apply (← mkConstWithFreshMVarLevels ``Fin.mk) { newGoals := .all }
  let ctx ← context
  -- Data fields precede proof discharge even if native apply returned the
  -- dependent proof obligation first. The proof service never assigns data.
  for child in children do
    child.withContext do
      let type ← instantiateMVars (← child.getType)
      unless ← isProp type do
        unless ← isDefEq type (mkConst ``Nat) do throwError "unexpected Fin field"
        child.assign (mkNatLit 0)
  for child in children do
    unless ← child.isAssigned do
      discard <| requireSolved (← (discharge child).run ctx)
  gateOriginal original target

run_elab do
  -- Original quantified transitivity, with Nat.le_trans withheld.
  proveIntroduced (← elabType (← `(∀ a b c : Nat, a ≤ b → b ≤ c → a ≤ c)))
  -- A local induction hypothesis is available to simp_all.
  proveIntroduced (← elabType (← `(∀ (A : Type) (xs ys : List A),
    ys.length = xs.length → ∀ a : A, (a :: ys).length = (a :: xs).length)))
  -- The target itself need not contain a free variable for local reasoning.
  proveIntroduced (← elabType (← `(∀ n : Nat, n < n → False)))
  proveIntroduced (← elabType (← `(∀ n : Nat, n < n → (1 : Nat) = 0)))
  proveIntroduced (← elabType (← `(∀ (p : Prop) [Decidable p], p → p)))

run_meta do
  let goal ← mkFreshExprMVar (mkConst ``False)
  let ctx ← context
  requireUnresolved (← (discharge goal.mvarId!).run ctx)
  if ← goal.mvarId!.isAssigned then throwError "consistent False goal was assigned"

run_elab do
  -- A partial simplifier tier must not stop the portfolio before arithmetic.
  let target ← elabType (← `(∀ a b c : Nat, a ≤ b → b ≤ c → a ≤ c))
  let root ← mkFreshExprMVar target
  let mut goal := root.mvarId!
  while (← goal.withContext <| whnf (← goal.getType)).isForall do
    let (_, next) ← goal.intro1P
    goal := next
  let reachedSecond ← IO.mkRef false
  let ctx ← context
  let first : Tier := { name := `partial, action := do
    -- This succeeds with a residual goal, as a partially effective simp can.
    Tactic.evalTactic (← `(tactic| try simp only [Nat.add_zero])) }
  let second : Tier := { name := `arithmetic, action := do
    reachedSecond.set true
    Tactic.evalTactic (← `(tactic| omega)) }
  discard <| requireSolved (← (dischargeWith {} goal #[first, second]).run ctx)
  unless ← reachedSecond.get do throwError "partial tactic suppressed the next tier"
  gateOriginal root target

/-! Unresolved dependencies are refused before any tactic can instantiate
program holes or change local declarations, including hidden local let values. -/
run_meta do
  let p ← mkFreshExprMVar (mkSort .zero)
  let goal ← mkFreshExprMVar p
  let ctx ← context
  requireUnsupported (← (discharge goal.mvarId!).run ctx)
  if (← p.mvarId!.isAssigned) || (← goal.mvarId!.isAssigned) then
    throwError "target dependency was assigned"

run_meta do
  let α ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `x α fun _ => do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let ctx ← context
    requireUnsupported (← (discharge goal.mvarId!).run ctx)
    if (← α.mvarId!.isAssigned) || (← goal.mvarId!.isAssigned) then
      throwError "local type dependency was assigned"

run_meta do
  let value ← mkFreshExprMVar (mkConst ``Nat)
  withLetDecl `hidden (mkConst ``Nat) value (nondep := true) (kind := .implDetail) fun _ => do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let ctx ← context
    requireUnsupported (← (discharge goal.mvarId!).run ctx)
    if (← value.mvarId!.isAssigned) || (← goal.mvarId!.isAssigned) then
      throwError "hidden local value dependency was assigned"

/-! Incoming universe metavariables are rigid. A proof at the incoming universe
is permitted, but cannot assign either its level or an unrelated sibling hole. -/
run_meta do
  let u ← mkFreshLevelMVar
  withLocalDeclD `A (mkSort u) fun α => do
    withLocalDeclD `x α fun x => do
      let target ← mkEq x x
      let goal ← mkFreshExprMVar target
      let sibling ← mkFreshExprMVar (mkConst ``Bool)
      let before ← getMCtx
      let ctx ← context
      let pf ← requireSolved (← (discharge goal.mvarId!).run ctx)
      unless ← withNewMCtxDepth (isDefEq (← inferType pf) target) do
        throwError "proof at original universe changed type"
      if getLevelMVarAssignmentExp (← getMCtx) u.mvarId! !=
          getLevelMVarAssignmentExp before u.mvarId! then
        throwError "original universe was assigned"
      if ← sibling.mvarId!.isAssigned then throwError "unrelated sibling was assigned"

private def rejectTier (tier : Tier) (target : Expr := mkConst ``True) : MetaM Unit := do
  let goal ← mkFreshExprMVar target
  let before ← getMCtx
  let ctx ← context
  requireUnresolved (← (dischargeWith {} goal.mvarId! #[tier]).run ctx)
  if (← goal.mvarId!.isAssigned) || (← getMCtx).mvarCounter != before.mvarCounter ||
      (← getMCtx).lmvarCounter != before.lmvarCounter then
    throwError "rejected proof escaped the scratch state"

run_meta do
  rejectTier { name := `clearWithoutProof, action := Tactic.setGoals [] }
  rejectTier { name := `loggedError, action := do
    logError "speculative tactic reported an error"
    (← Tactic.getMainGoal).assign (mkConst ``True.intro)
    Tactic.setGoals [] }
  rejectTier { name := `unfinishedAssignment, action := do
    let scratch ← Tactic.getMainGoal
    let unfinished ← mkFreshExprMVar (← scratch.getType)
    scratch.assign unfinished
    Tactic.setGoals [] }
  rejectTier { name := `unfinishedDelayedAssignment, action := do
    let scratch ← Tactic.getMainGoal
    let unfinished ← mkFreshExprMVar (← scratch.getType)
    assignDelayedMVar scratch #[] unfinished.mvarId!
    Tactic.setGoals [] }
  rejectTier { name := `wrongOriginalType, action := do
    (← Tactic.getMainGoal).assign (mkNatLit 0)
    Tactic.setGoals [] }
  rejectTier { name := `sorry, action := do
    let scratch ← Tactic.getMainGoal
    scratch.assign (← mkSorry (← scratch.getType) true)
    Tactic.setGoals [] }
  rejectTier { name := `escapedFreeLocal, action := do
    let scratch ← Tactic.getMainGoal
    withLocalDeclD `scratchProof (mkConst ``True) fun h => scratch.assign h
    Tactic.setGoals [] }
  rejectTier { name := `escapedUniverse, action := do
    let scratch ← Tactic.getMainGoal
    let fresh ← mkFreshLevelMVar
    scratch.assign (mkApp2 (mkConst ``Eq.refl [fresh]) (mkSort .zero) (mkConst ``True))
    Tactic.setGoals [] } (← mkEq (mkConst ``True) (mkConst ``True))

run_meta do
  -- A locally valid proof at level 0 must not solve a target at a rigid
  -- incoming level by assigning that incoming universe during replay.
  let u ← mkFreshLevelMVar
  let target := mkApp (mkConst ``Nonempty [u]) (mkConst ``PUnit [u])
  let proof := mkApp2 (mkConst ``Nonempty.intro [.zero])
    (mkConst ``PUnit [.zero]) (mkConst ``PUnit.unit [.zero])
  rejectTier { name := `wouldAssignIncomingUniverse, action := do
    (← Tactic.getMainGoal).assign proof
    Tactic.setGoals [] } target
  if (getLevelMVarAssignmentExp (← getMCtx) u.mvarId!).isSome then
    throwError "proof replay assigned an incoming universe"

run_elab do
  -- Fully resolved delayed assignments are accepted; the unfinished delayed
  -- fixture above must fail because extraction still contains its pending hole.
  -- Use native introduction so the delayed assignment has its real telescope.
  let target ← elabType (← `(True → True))
  let goal ← mkFreshExprMVar target
  let ctx ← context
  let tier : Tier := { name := `completedDelayedAssignment, action := do
    Tactic.evalTactic (← `(tactic| intro h; exact h)) }
  discard <| requireSolved (← (dischargeWith {} goal.mvarId! #[tier]).run ctx)
  gateOriginal goal target

private def scratchName : MetaM Name := do
  let prefixName := (← getEnv).asyncPrefix?.getD `Leant2Tests
  return prefixName ++ (← mkFreshUserName `localProofScratch)

run_meta do
  -- Native omega exports an auxiliary theorem; nested theorem bodies must be
  -- copied before rollback without retaining their environment declarations.
  let firstName ← scratchName
  let secondName ← scratchName
  let goal ← mkFreshExprMVar (mkConst ``True)
  let ctx ← context
  let tier : Tier := { name := `auxiliaryTheorems, action := do
    addDecl (.thmDecl {
      name := firstName, levelParams := [], type := mkConst ``True
      value := mkConst ``True.intro })
    addDecl (.thmDecl {
      name := secondName, levelParams := [], type := mkConst ``True
      value := mkConst firstName })
    (← Tactic.getMainGoal).assign (mkConst secondName)
    Tactic.setGoals [] }
  let proof ← requireSolved (← (dischargeWith {} goal.mvarId! #[tier]).run ctx)
  if (← getEnv).contains firstName || (← getEnv).contains secondName then
    throwError "auxiliary theorem declaration escaped"
  if (proof.find? fun e => e.isConstOf firstName || e.isConstOf secondName).isSome then
    throwError "auxiliary theorem reference escaped extraction"
  gateOriginal goal (mkConst ``True)

run_meta do
  -- Universe parameters of an exported theorem body must be instantiated at
  -- the use site before the theorem declaration is rolled back.
  let theoremName ← scratchName
  let (theoremType, theoremProof) ← withLocalDeclD `A (mkSort (.param `u)) fun α => do
    withLocalDeclD `x α fun x => do
      let type ← mkEq x x
      let proof ← mkEqRefl x
      return (← mkForallFVars #[α, x] type, ← mkLambdaFVars #[α, x] proof)
  let target ← mkEq (mkNatLit 0) (mkNatLit 0)
  let goal ← mkFreshExprMVar target
  let ctx ← context
  let tier : Tier := { name := `universeAuxiliaryTheorem, action := do
    addDecl (.thmDecl {
      name := theoremName, levelParams := [`u], type := theoremType
      value := theoremProof })
    (← Tactic.getMainGoal).assign
      (mkApp2 (mkConst theoremName [.succ .zero]) (mkConst ``Nat) (mkNatLit 0))
    Tactic.setGoals [] }
  discard <| requireSolved (← (dischargeWith {} goal.mvarId! #[tier]).run ctx)
  if (← getEnv).contains theoremName then throwError "polymorphic theorem escaped"
  gateOriginal goal target

run_meta do
  -- Exceeding the explicit auxiliary-export bound is resource exhaustion,
  -- never ordinary failure and never a logical refutation.
  let goal ← mkFreshExprMVar (mkConst ``True)
  let before ← getMCtx
  let ctx ← context
  let tier : Tier := { name := `auxiliaryExpansionLimit, action := do
    let mut proof : Expr := mkConst ``True.intro
    for _ in [:65] do
      let name ← scratchName
      addDecl (.thmDecl {
        name, levelParams := [], type := mkConst ``True
        value := proof })
      proof := mkConst name
    (← Tactic.getMainGoal).assign proof
    Tactic.setGoals [] }
  requireResource (← (dischargeWith {} goal.mvarId! #[tier]).run ctx)
  if (← goal.mvarId!.isAssigned) || (← getMCtx).mvarCounter != before.mvarCounter then
    throwError "auxiliary expansion limit did not restore the original goal"

run_meta do
  -- This term is well typed in the speculative environment only. It must be
  -- rejected by replay after the auxiliary declaration is removed.
  let name ← scratchName
  rejectTier { name := `escapedDeclaration, action := do
    addDecl (.axiomDecl {
      name, levelParams := [], type := mkConst ``True
      isUnsafe := false })
    (← Tactic.getMainGoal).assign (mkConst name)
    Tactic.setGoals [] }
  if (← getEnv).contains name then throwError "speculative declaration escaped"

private structure StateWitness where
  mvars : Nat
  levels : Nat
  messages : Nat
  infoEnabled : Bool
  deriving BEq

private def stateWitness : MetaM StateWitness := do
  return {
    mvars := (← getMCtx).mvarCounter
    levels := (← getMCtx).lmvarCounter
    messages := (← getThe Core.State).messages.toList.length
    infoEnabled := (← getThe Core.State).infoState.enabled }

private def contaminate (sibling : MVarId) (level : LMVarId) (name : Name)
    : Tactic.TacticM Unit := do
  -- Direct assignment is deliberately adversarial. Even a tactic bypassing
  -- the ordinary unifier's depth guard must not commit unrelated changes.
  sibling.assign (mkConst ``Bool.true)
  assignLevelMVar level .zero
  discard <| mkFreshExprMVar (mkConst ``Nat)
  discard <| mkFreshLevelMVar
  logInfo "speculative local proof message"
  modifyThe Core.State fun s => { s with infoState := { s.infoState with enabled := false } }
  addDecl (.axiomDecl {
    name, levelParams := [], type := mkConst ``True
    isUnsafe := false })

private def requireRestored (before : StateWitness) (goal sibling : MVarId)
    (level : LMVarId) (name : Name) : MetaM Unit := do
  unless (← stateWitness) == before do throwError "speculative state was not fully restored"
  if (← goal.isAssigned) || (← sibling.isAssigned) ||
      (getLevelMVarAssignmentExp (← getMCtx) level).isSome || (← getEnv).contains name then
    throwError "speculative assignments or declaration escaped"

run_meta do
  -- Successful probing also rolls back everything except the final original
  -- goal assignment. This callback deliberately bypasses normal depth guards.
  let goal ← mkFreshExprMVar (mkConst ``True)
  let sibling ← mkFreshExprMVar (mkConst ``Bool)
  let level ← mkFreshLevelMVar
  let name ← scratchName
  let before ← stateWitness
  let ctx ← context
  let tier : Tier := { name := `successIsolation, action := do
    contaminate sibling.mvarId! level.mvarId! name
    (← Tactic.getMainGoal).assign (mkConst ``True.intro)
    Tactic.setGoals [] }
  discard <| requireSolved (← (dischargeWith {} goal.mvarId! #[tier]).run ctx)
  requireRestored before sibling.mvarId! sibling.mvarId! level.mvarId! name
  unless ← goal.mvarId!.isAssigned do throwError "successful proof was not committed"

run_meta do
  -- The unifier cannot assign incoming expression or universe holes even
  -- inside a successful tier; restoring alone must not be the only defense.
  let goal ← mkFreshExprMVar (mkConst ``True)
  let sibling ← mkFreshExprMVar (mkConst ``Bool)
  let level ← mkFreshLevelMVar
  let assignedByUnifier ← IO.mkRef false
  let ctx ← context
  let tier : Tier := { name := `rigidIncomingHoles, action := do
    if ← isDefEq sibling (mkConst ``Bool.true) then assignedByUnifier.set true
    if ← isDefEq (mkSort level) (mkSort .zero) then assignedByUnifier.set true
    (← Tactic.getMainGoal).assign (mkConst ``True.intro)
    Tactic.setGoals [] }
  discard <| requireSolved (← (dischargeWith {} goal.mvarId! #[tier]).run ctx)
  if ← assignedByUnifier.get then throwError "incoming hole was not rigid during proof search"
  if (← sibling.mvarId!.isAssigned) ||
      (getLevelMVarAssignmentExp (← getMCtx) level.mvarId!).isSome then
    throwError "incoming hole assignment escaped"

run_meta do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let sibling ← mkFreshExprMVar (mkConst ``Bool)
  let level ← mkFreshLevelMVar
  let name ← scratchName
  let before ← stateWitness
  let ctx ← context
  let tier : Tier := { name := `ordinaryFailure, action := do
    contaminate sibling.mvarId! level.mvarId! name
    throwError "ordinary speculative tactic failure" }
  requireUnresolved (← (dischargeWith {} goal.mvarId! #[tier]).run ctx)
  requireRestored before goal.mvarId! sibling.mvarId! level.mvarId! name
  unless (← ctx.ledger.get).proofAttempts == 1 do throwError "rollback refunded proof work"

run_meta do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let sibling ← mkFreshExprMVar (mkConst ``Bool)
  let level ← mkFreshLevelMVar
  let name ← scratchName
  let before ← stateWitness
  let ctx ← context
  let tier : Tier := { name := `heartbeat, action := do
    contaminate sibling.mvarId! level.mvarId! name
    IO.addHeartbeats 100000
    checkSystem "leant2.localProof.test" }
  requireResource (← (dischargeWith { tacticHeartbeats := 64 }
    goal.mvarId! #[tier]).run ctx)
  requireRestored before goal.mvarId! sibling.mvarId! level.mvarId! name

run_meta do
  -- Heartbeats spent before a tier do not consume its fresh bounded budget.
  IO.addHeartbeats 100000
  let goal ← mkFreshExprMVar (mkConst ``True)
  let ctx ← context
  let tier : Tier := { name := `freshBudget, action := do
    checkSystem "leant2.localProof.test"
    Tactic.evalTactic (← `(tactic| exact True.intro)) }
  discard <| requireSolved (← (dischargeWith { tacticHeartbeats := 64 }
    goal.mvarId! #[tier]).run ctx)

/-! Run a private copy of Meta/Core on the underlying EIO boundary. Unlike
Lean's normal catch handlers, this can observe a genuine user-interrupt
exception without aborting the test module. No worker process is required. -/
private def isolated (act : MetaM Unit) : MetaM (Except Exception Unit) := do
  let metaContext ← readThe Meta.Context
  let metaState ← getThe Meta.State
  let coreContext ← readThe Core.Context
  let coreState ← getThe Core.State
  (act.run' metaContext metaState).run' coreContext coreState |>.toBaseIO

private def cancellationTest (userInterrupt : Bool) : MetaM Unit := do
  let restored ← IO.mkRef false
  let outcome ← isolated do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let sibling ← mkFreshExprMVar (mkConst ``Bool)
    let level ← mkFreshLevelMVar
    let name ← scratchName
    let before ← stateWitness
    let ctx ← context
    let tier : Tier := { name := `cancel, action := do
      contaminate sibling.mvarId! level.mvarId! name
      if userInterrupt then throwInterruptException
      -- Fire the SearchCtx grace deadline after the tactic has changed state. The
      -- service must check it after extraction and before committing a proof.
      ctx.graceDeadline.set (some 0)
      (← Tactic.getMainGoal).assign (mkConst ``True.intro)
      Tactic.setGoals [] }
    try
      discard <| (dischargeWith {} goal.mvarId! #[tier]).run ctx
    finally
      requireRestored before goal.mvarId! sibling.mvarId! level.mvarId! name
      restored.set true
  unless ← restored.get do throwError "cancellation did not restore before propagation"
  let .error ex := outcome | throwError "cancellation was swallowed"
  if userInterrupt then
    unless ex.isInterrupt do throwError "user cancellation was misclassified"
  else
    match ex with
    | .internal id _ =>
      unless id == graceExceptionId do throwError "grace exception identity changed"
    | _ => throwError "grace completion was misclassified"

run_meta do
  cancellationTest false
  cancellationTest true

run_meta do
  let unknownInternalId ← registerInternalExceptionId `localProofTestUnknownInternal
  let restored ← IO.mkRef false
  let outcome ← isolated do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let sibling ← mkFreshExprMVar (mkConst ``Bool)
    let level ← mkFreshLevelMVar
    let name ← scratchName
    let before ← stateWitness
    let ctx ← context
    let tier : Tier := { name := `unknownInternal, action := do
      contaminate sibling.mvarId! level.mvarId! name
      throw (.internal unknownInternalId) }
    try
      discard <| (dischargeWith {} goal.mvarId! #[tier]).run ctx
    finally
      requireRestored before goal.mvarId! sibling.mvarId! level.mvarId! name
      restored.set true
  unless ← restored.get do throwError "unknown exception escaped without restoration"
  match outcome with
  | .error (.internal id _) =>
    unless id == unknownInternalId do throwError "unknown exception identity changed"
  | _ => throwError "unknown internal exception was swallowed or misclassified"

end Leant2Tests.LocalProof
