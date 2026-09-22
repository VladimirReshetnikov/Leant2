import Leant2.Engine

/-! Upfront semantic negatives carry profile-respecting certificates that
replay after rollback. The internal proof callback isolates export, failure,
and cancellation boundaries from proof-search scheduling. -/
namespace Leant2Tests.ContractRefutation

open Lean Meta Elab Leant2
open Lean.Elab.Term hiding mkConst

private def unitQuery (contract : TSyntax `term) (profile : Profile := .standard) : TermElabM Query := do
  let target := mkConst ``Unit
  let contract ← elabTermEnsuringType contract (← mkArrow target (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  return { target, contract := some (← instantiateMVars contract), profile,
           budgetMs := 0, maxCandidates := 1, graceMs := 0 }

private def falseQuery : Query := {
  target := mkConst ``Unit
  contract := some (mkLambda `f .default (mkConst ``Unit) (mkConst ``False))
  profile := .strictConstructive, budgetMs := 0 }

private def falseRefutation : Expr :=
  mkLambda `f .default (mkConst ``Unit)
    (mkLambda `h .default (mkConst ``False) (.bvar 0))

private def assertReplay (profile : Profile) (certificate : Accepted) : MetaM Unit := do
  let .ok checked ← gate profile certificate.program certificate.programType none
    | throwError "negative certificate does not replay after rollback"
  unless checked.axioms == certificate.axioms do
    throwError "negative certificate axiom inventory changed on replay"

private def requireSome (certificate : Option Accepted) : MetaM Accepted := do
  let some certificate := certificate | throwError "expected a portable contract refutation"
  return certificate

run_elab do
  -- The equality of these distinct propositions uses propext. A classical
  -- flag is insufficient: only choice, not propext, sets that flag.
  let query ← unitQuery (← `(fun (_ : Unit) => True ≠ (True ∧ True)))
  let explicit ← elabTerm (← `(
    fun (_ : Unit) (h : True ≠ (True ∧ True)) =>
      h (propext
        ⟨(fun (_ : True) => And.intro True.intro True.intro),
         (fun (_ : True ∧ True) => True.intro)⟩))) none
  synthesizeSyntheticMVarsNoPostponing
  let explicit ← instantiateMVars explicit
  let worker : MVarId → MetaM Bool := fun goal => do goal.assign explicit; return true
  let ledger ← IO.mkRef ({} : Ledger)
  let certificate ← requireSome (← tryRefuteContract? query ledger worker)
  unless certificate.axioms.contains ``propext do throwError "fixture lost its propext dependency"
  assertReplay .standard certificate
  if (← tryRefuteContract? { query with profile := .strictConstructive } ledger worker).isSome then
    throwError "strict policy accepted a propext-bearing refutation"
  unless (← ledger.get).proofAttempts == 2 do throwError "profile rejection refunded proof work"
  -- Exercise the actual portfolio and Engine wiring, not just the callback.
  let .negative .contractImpossible (some native) work ← runQuery query
    | throwError "standard engine did not return a contract certificate"
  unless native.axioms.contains ``propext && work.proofAttempts == 1 do
    throwError "native refutation lost its dependency or attempt accounting"
  assertReplay .standard native
  if (← runQuery { query with profile := .strictConstructive }) matches
      .negative .contractImpossible .. then
    throwError "strict engine accepted the standard-only upfront refutation"

run_meta do
  let .negative .contractImpossible (some certificate) work ← runQuery falseQuery
    | throwError "literal False lost its constructive impossibility certificate"
  unless certificate.axioms.isEmpty && work.proofAttempts == 1 do
    throwError "constructive certificate policy or accounting changed"
  assertReplay .strictConstructive certificate

axiom projectEquality : True = (True ∧ True)

axiom contractDomainDependency : Nat

run_meta do
  -- The domain is definitionally Nat, but its unused axiom is part of the
  -- original contract. Beta-reducing the contract before auditing erases it.
  let domain := mkLet `unused (mkConst ``Nat)
    (mkConst ``contractDomainDependency) (mkConst ``Nat)
  let contract := mkLambda `f .default domain (mkConst ``False)
  let query : Query := {
    target := mkConst ``Nat, contract := some contract, budgetMs := 0 }
  let proof := mkLambda `f .default (mkConst ``Nat)
    (mkLambda `h .default (mkConst ``False) (.bvar 0))
  let worker : MVarId → MetaM Bool := fun goal => do goal.assign proof; return true
  let ledger ← IO.mkRef ({} : Ledger)
  for profile in [.strictConstructive, .standard] do
    if (← tryRefuteContract? { query with profile } ledger worker).isSome then
      throwError "refutation erased an original contract-domain axiom dependency"
  let profile := Profile.projectRelative [``contractDomainDependency]
  let certificate ← requireSome (← tryRefuteContract? { query with profile } ledger worker)
  unless certificate.axioms.contains ``contractDomainDependency &&
      certificate.programType.foldConsts (init := false)
        (fun name found => found || name == ``contractDomainDependency) do
    throwError "refutation lost the original statement's axiom inventory"
  assertReplay profile certificate
  let .negative .contractImpossible (some native) _ ← runQuery { query with profile }
    | throwError "project-relative original-statement refutation failed"
  unless native.axioms.contains ``contractDomainDependency do
    throwError "native refutation bypassed the original-statement audit"
  assertReplay profile native

run_elab do
  let query ← unitQuery (← `(fun (_ : Unit) => True ≠ (True ∧ True)))
  let proof ← elabTerm (← `(fun (_ : Unit) (h : True ≠ (True ∧ True)) => h projectEquality)) none
  synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let worker : MVarId → MetaM Bool := fun goal => do goal.assign proof; return true
  let ledger ← IO.mkRef ({} : Ledger)
  for profile in [.standard, .strictConstructive] do
    if (← tryRefuteContract? { query with profile } ledger worker).isSome then
      throwError "unapproved project axiom certified an impossibility result"
  let profile := Profile.projectRelative [``projectEquality]
  let certificate ← requireSome (← tryRefuteContract? { query with profile } ledger worker)
  unless certificate.axioms.contains ``projectEquality do throwError "project dependency was omitted"
  assertReplay profile certificate

run_meta do
  -- Freeze once: a level placeholder becomes a rigid certificate parameter,
  -- and substituting it back recovers the exact original negative formula.
  let level ← mkFreshLevelMVar
  let target := mkConst ``PUnit [.succ level]
  let contract := mkLambda `f .default target (mkConst ``False)
  let query : Query := { target, contract := some contract, profile := .strictConstructive, budgetMs := 0 }
  let ledger ← IO.mkRef ({} : Ledger)
  let certificate ← requireSome (← tryRefuteContract? query ledger)
  unless certificate.levelParams.length == 1 do throwError "negative universe generalization changed"
  let original ← withLocalDeclD `f target fun f =>
    mkForallFVars #[f] (mkApp (mkConst ``Not) (contract.beta #[f]))
  let reopened := certificate.programType.instantiateLevelParams certificate.levelParams [level]
  unless ← withNewMCtxDepth (isDefEq reopened original) do
    throwError "certificate describes a different generalized negative statement"
  unless (← instantiateLevelMVars level) == level do throwError "refutation assigned an incoming universe"
  assertReplay .strictConstructive certificate
  let .negative .contractImpossible (some native) _ ← runQuery query
    | throwError "raw Engine flexible-universe contract did not retain its certificate"
  unless (← instantiateLevelMVars level) == level do throwError "raw Engine specialized the query universe"
  assertReplay .strictConstructive native

private def scratchName : MetaM Name := do
  let namePrefix := (← getEnv).asyncPrefix?.getD `Leant2Tests.ContractRefutation
  return namePrefix ++ (← mkFreshUserName `aux)

run_meta do
  -- A new theorem's body is copied before its declaration is rolled back.
  -- New axioms and definitions are deliberately not exportable.
  for kind in [0, 1, 2] do
    let name ← scratchName
    let arrow ← mkArrow (mkConst ``False) (mkConst ``False)
    let body := mkLambda `h .default (mkConst ``False) (.bvar 0)
    let worker : MVarId → MetaM Bool := fun goal => do
      match kind with
      | 0 => addDecl (.thmDecl { name, levelParams := [], type := arrow, value := body })
      | 1 => addDecl (.axiomDecl { name, levelParams := [], type := arrow, isUnsafe := false })
      | _ => addDecl (.defnDecl { name, levelParams := [], type := arrow, value := body,
                                  hints := .abbrev, safety := .safe })
      goal.assign (mkLambda `f .default (mkConst ``Unit) (mkConst name))
      return true
    let ledger ← IO.mkRef ({} : Ledger)
    let result ← tryRefuteContract? falseQuery ledger worker
    if (← getEnv).contains name then throwError "refutation auxiliary declaration escaped rollback"
    if kind == 0 then
      let certificate ← requireSome result
      if certificate.program.foldConsts (init := false) (fun n found => found || n == name) then
        throwError "portable certificate still mentions a rolled-back theorem"
      assertReplay .strictConstructive certificate
    else if result.isSome then
      throwError "refutation exported a new axiom or definition"
    unless (← ledger.get).proofAttempts == 1 do throwError "export rejection refunded proof work"

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

private def contaminate (sibling : MVarId) (level : LMVarId) (name : Name) : MetaM Unit := do
  sibling.assign (mkConst ``Bool.true)
  assignLevelMVar level .zero
  discard <| mkFreshExprMVar (mkConst ``Nat)
  discard <| mkFreshLevelMVar
  logInfo "speculative upfront refutation message"
  modifyThe Core.State fun s => { s with infoState := { s.infoState with enabled := false } }
  addDecl (.axiomDecl { name, levelParams := [], type := mkConst ``True, isUnsafe := false })

private def requireRestored (before : StateWitness) (sibling : MVarId) (level : LMVarId)
    (name : Name) : MetaM Unit := do
  unless (← stateWitness) == before do throwError "upfront refutation did not restore full native state"
  if (← sibling.isAssigned) || (getLevelMVarAssignmentExp (← getMCtx) level).isSome ||
      (← getEnv).contains name then throwError "upfront refutation leaked a speculative assignment/declaration"

run_meta do
  for mode in [0, 1, 2] do
    let sibling ← mkFreshExprMVar (mkConst ``Bool)
    let level ← mkFreshLevelMVar
    let name ← scratchName
    let ledger ← IO.mkRef ({} : Ledger)
    let before ← stateWitness
    let worker : MVarId → MetaM Bool := fun goal => do
      contaminate sibling.mvarId! level.mvarId! name
      if mode == 1 then throwError "ordinary proof failure"
      if mode == 2 then
        Core.throwMaxHeartbeat `contractRefutationTest `maxHeartbeats 1
        return false
      goal.assign falseRefutation
      return true
    let result ← tryRefuteContract? falseQuery ledger worker
    requireRestored before sibling.mvarId! level.mvarId! name
    unless result.isSome == (mode == 0) do throwError "incorrect refutation success/failure classification"
    unless (← ledger.get).proofAttempts == 1 do throwError "restoration refunded upfront proof work"

run_meta do
  let sibling ← mkFreshExprMVar (mkConst ``Bool)
  let level ← mkFreshLevelMVar
  let ledger ← IO.mkRef ({} : Ledger)
  let worker : MVarId → MetaM Bool := fun goal => do
    if ← isDefEq sibling (mkConst ``Bool.true) then throwError "incoming expression hole was not rigid"
    if ← isDefEq (.sort level) (.sort .zero) then throwError "incoming universe hole was not rigid"
    goal.assign falseRefutation
    return true
  discard <| requireSome (← tryRefuteContract? falseQuery ledger worker)
  -- A true callback with an unassigned or nested goal is not a proof.
  if (← tryRefuteContract? falseQuery ledger (fun _ => pure true)).isSome then
    throwError "empty proof callback certified an impossibility result"
  if (← tryRefuteContract? falseQuery ledger (fun goal => do
      let nested ← mkFreshExprMVar (← goal.getType)
      goal.assign nested
      return true)).isSome then
    throwError "unfinished nested proof escaped extraction"

run_meta do
  -- Deferred input is not an attempted proof and must not become frozen by
  -- silently forgetting the caller's unresolved universe constraints.
  let ledger ← IO.mkRef ({} : Ledger)
  let proposition ← mkFreshExprMVar (mkSort .zero)
  let openQuery := { falseQuery with
    contract := some (mkLambda `f .default (mkConst ``Unit) proposition) }
  if (← tryRefuteContract? openQuery ledger).isSome then throwError "open contract was refuted"
  if ← proposition.mvarId!.isAssigned then throwError "refutation assigned a caller proposition"
  withoutModifyingState do
    let level ← mkFreshLevelMVar
    modifyPostponed fun pending => pending.push {
      ref := Syntax.missing, lhs := level, rhs := .succ .zero, ctx? := none }
    let size := (← getPostponed).size
    if (← tryRefuteContract? falseQuery ledger).isSome then
      throwError "refutation silently dropped a pending universe equation"
    unless (← getPostponed).size == size do throwError "refutation changed pending universe equations"
  unless (← ledger.get).proofAttempts == 0 do throwError "unsupported preparation was counted as a proof attempt"

private def isolated (action : MetaM Unit) : MetaM (Except Exception Unit) := do
  let metaContext ← readThe Meta.Context
  let metaState ← getThe Meta.State
  let coreContext ← readThe Core.Context
  let coreState ← getThe Core.State
  (action.run' metaContext metaState).run' coreContext coreState |>.toBaseIO

run_meta do
  -- Exceptions must restore before escaping, preserving native identity.
  let unknown ← registerInternalExceptionId `contractRefutationTestUnknown
  for cancel in [true, false] do
    let restored ← IO.mkRef false
    let outcome ← isolated do
      let sibling ← mkFreshExprMVar (mkConst ``Bool)
      let level ← mkFreshLevelMVar
      let name ← scratchName
      let ledger ← IO.mkRef ({} : Ledger)
      let token ← IO.CancelToken.new
      let before ← stateWitness
      let worker : MVarId → MetaM Bool := fun _ => do
        contaminate sibling.mvarId! level.mvarId! name
        if cancel then
          token.set
          Core.checkInterrupted
          return false
        throw (.internal unknown)
      try
        withTheReader Core.Context (fun context => { context with cancelTk? := some token }) do
          discard <| tryRefuteContract? falseQuery ledger worker
      finally
        requireRestored before sibling.mvarId! level.mvarId! name
        unless (← ledger.get).proofAttempts == 1 do throwError "interruption refunded proof work"
        restored.set true
    unless ← restored.get do throwError "exception escaped before full restoration"
    let .error ex := outcome | throwError "native cancellation or unknown exception was swallowed"
    if cancel then
      unless ex.isInterrupt do throwError "native cancellation changed identity"
    else
      match ex with
      | .internal id _ => unless id == unknown do throwError "internal exception changed identity"
      | _ => throwError "internal exception changed classification"

end Leant2Tests.ContractRefutation
