import Leant2.API
import Leant2.Frontend.Sketch.Prepare
import Leant2.Frontend.Sketch.Projection

/-! Completion of an owned, closed sketch. The supplied expression is the real
root of every pass; all program holes and the whole-contract proof share one
search continuation. Only complete, portable accepted objects escape. -/

namespace Leant2.Frontend.Sketch
open Lean Meta Elab Term

structure Result where
  outcome : Outcome
  preparation : Report

private def complete (expression : Expr) : Bool :=
  !expression.hasExprMVar && !expression.hasLevelMVar && !expression.hasFVar &&
  !expression.hasLooseBVars && !expression.hasSorry

private def prepareQuery (query : Query) : TermElabM Query := do
  let target ← instantiateMVars query.target
  let contract ← query.contract.mapM instantiateMVars
  unless complete target && contract.all complete do
    throwError "target and contract must be closed and free of holes and sorry"
  unless query.maxCandidates > 0 do throwError "maxCandidates must be positive"
  withLCtx {} #[] do
    check target
    unless (← whnf (← inferType target)).isSort do
      throwError "the expected expression must be a type"
    if let some contract := contract then
      check contract
      unless ← isDefEq (← inferType contract) (← mkArrow target (mkSort .zero)) do
        throwError "the contract must have type target → Prop"
    for provider in query.providers do
      unless (← getEnv).contains provider do throwError "unknown provider {provider}"
  return { query with target, contract }

/-- Transport first, then independently check the exact original query pair.
The general API's optional universe specialization is not used for sketches. -/
private def exportExact (originalCore : Core.State) (originalMeta : Meta.State)
    (query : Query) (candidate : Accepted) : MetaM Accepted := do
  let candidate ← API.exportCandidate originalCore originalMeta query.profile candidate
  let savedCore ← getThe Core.State
  let savedMeta ← getThe Meta.State
  try
    modifyThe Core.State fun _ => originalCore
    modifyThe Meta.State fun _ => originalMeta
    withNewMCtxDepth <| withLCtx {} #[] do
      Core.checkInterrupted
      unless ← isDefEq candidate.programType query.target do
        throwError "the completed program changed the original target"
      let proof := query.contract.map fun contract =>
        (candidate.proof, mkApp contract candidate.program)
      let .ok checked ← gate query.profile candidate.program query.target proof
        | throwError "the completed program or proof does not replay at the original query"
      Core.checkInterrupted
      return checked
  finally
    modifyThe Meta.State fun _ => savedMeta
    modifyThe Core.State fun _ => savedCore

private initialize outputValidationExceptionId : InternalExceptionId ←
  registerInternalExceptionId `leant2SketchOutputValidation

/-- Ordinary export errors cannot be swallowed by search's branch-failure
handler. Only this owned wrapper is converted back outside the search scope. -/
private def protectExport (action : MetaM Accepted) : MetaM Accepted :=
  tryCatchRuntimeEx action fun ex => do
    if Leant2.isInterrupt ex || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
    throw (.internal outputValidationExceptionId
      (({} : KVMap).setString `message (← ex.toMessageData.toString)))

/-- Fill the smaller interfaces first: an initializer before a binary step,
for example. Preparation has already frozen every hole's type and context, so
this only orders independent owned goals. Stable ties retain source order;
every goal remains in the same backtracking continuation. -/
private def orderHoles (holes : Array OwnedHole) : MetaM (Array OwnedHole) := do
  let keyed ← holes.mapM fun hole => hole.pending.withContext do
    let arity ← forallTelescopeReducing hole.declaration.type fun arguments _ =>
      pure arguments.size
    return (hole, arity)
  return (keyed.insertionSort fun a b => a.2 < b.2).map Prod.fst

/-- Observe only at an original owned-hole boundary, after a preceding whole
hole has been completed. Search-created children remain outside this hook's
eligibility test. Unsupported projections preserve ordinary search; native
resource, cancellation, and unrelated internal exceptions retain identity. -/
private def pruneOwnedHole (projection : Projection.State) (profile : Profile)
    (contract : Expr) (observations : Array Observation) (goal : MVarId) : SearchM Bool := do
  unless projection.prepared.holes.any (·.pending == goal) do return false
  unless ← projection.prepared.holes.anyM (fun hole => hole.pending.isAssigned) do
    return false
  let context ← read
  let observe : MetaM Bool := do
    let report ← Projection.observe projection profile contract observations
      (checkDeadline.run context)
    context.observationReport.set report
    return report.refuted
  return ← tryCatchRuntimeEx observe fun exception => do
    if Leant2.isInterrupt exception || exception.isMaxHeartbeat || exception.isMaxRecDepth then
      throw exception
    return false

/-- Optional setup runs only for an eligible sketch, inside its lane budget.
Observations must be portable closed schemas before their preparation state is
restored. Unsupported setup retains the original completion path. -/
private def prepareProjection? (prepared : Prepared) (contract : Expr)
    (check : MetaM Unit) : MetaM (Option (Projection.State × Array Observation)) := do
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let prepare : MetaM (Option (Projection.State × Array Observation)) := do
    try
      check
      let some projection ← Projection.tryBuild prepared check | return none
      let observations ← mkObservations contract prepared.expected
      check
      let observations ← observations.mapM fun observation => do
        let predicate ← instantiateMVars observation.predicate
        let decider ← observation.decider.mapM instantiateMVars
        unless complete predicate && decider.all complete do
          throwError "sketch projection: observation schema is not closed and frozen"
        return { observation with predicate, decider }
      check
      if observations.isEmpty then return none
      return some (projection, observations)
    finally
      modifyThe Meta.State fun _ => originalMeta
      modifyThe Core.State fun _ => originalCore
  tryCatchRuntimeEx prepare fun exception => do
    if Leant2.isInterrupt exception || exception.isMaxHeartbeat || exception.isMaxRecDepth then
      throw exception
    return none

private def runPrepared (query : Query) (prepared : Prepared)
    (originalCore : Core.State) (originalMeta : Meta.State) : MetaM Outcome :=
  withLCtx {} #[] <| withTheReader Core.Context (fun context =>
      { context with maxHeartbeats := 0 }) do
    Core.checkInterrupted
    let ledger ← IO.mkRef ({} : Ledger)
    -- This proves a statement about every program of the original type,
    -- independent of the chosen skeleton. Other failures remain bounded.
    if let some certificate ← tryRefuteContract? query ledger then
      return ← API.exportOutcome originalCore originalMeta query
        (.negative .contractImpossible (some certificate) (← ledger.get))
    let providers ← mkProviders query.providers
    let frontier ← defaultTypeFrontier
    let residual ← match query.contract with
      | some contract => mkResidual contract query.target
      | none => pure #[]
    let skip := ((leant2.skipRules.get (← getOptions)).splitOn ",").map
      (fun part => part.trimAscii.toString) |>.filter (· != "")
    let pruningEvidenceCache ← IO.mkRef none
    let configuration : SearchConfig := {
      providers, profile := query.profile, pruningEvidenceCache := some pruningEvidenceCache
      typeFrontier := frontier, contract := query.contract, residual
      recursionFirst := query.contract.isSome
      -- Native closed-root checks remain active. The separate owned-hole
      -- projection does not enable generic partial closure expansion.
      skip := "residual" :: skip }
    let orderedHoles ← orderHoles prepared.holes
    let preparedCore ← getThe Core.State
    let preparedMeta ← getThe Meta.State
    let found ← IO.mkRef (#[] : Array Accepted)
    let seen ← IO.mkRef (#[] : Array Expr)
    let grace ← IO.mkRef (none : Option Nat)
    let timedOut ← IO.mkRef false
    let refuted ← IO.mkRef ({} : Std.HashSet Expr)
    let completed ← IO.mkRef 0
    let initializePass (depth : Nat) : SearchM EnumerationSeed := do
      checkDeadline
      modifyThe Meta.State fun _ => preparedMeta
      modifyThe Core.State fun _ => preparedCore
      unless (← getMCtx).depth == prepared.depth do
        throwError "leant2 sketch: prepared graph changed its owned depth"
      let mut goals := orderedHoles.toList.map fun hole =>
        ({ mvar := hole.pending, depth } : Goal)
      let (rootType, value) ← match query.contract with
        | none => pure (query.target, prepared.expression)
        | some contract => do
          -- The exact closed-root evaluator recognizes this beta-instantiated
          -- goal. Acceptance still audits the original unreduced application.
          let proof ← mkFreshExprMVar (contract.beta #[prepared.expression])
          goals := goals ++ [{ mvar := proof.mvarId!, depth }]
          let rootType ← mkAppM ``Subtype #[contract]
          -- The predicate is fixed input; asking higher-order unification to
          -- reconstruct it from the proof fails while program holes remain.
          let value := mkApp4 (Lean.mkConst ``Subtype.mk [← getLevel query.target])
            query.target contract prepared.expression proof
          pure (rootType, value)
      let root ← mkFreshExprMVar rootType
      root.mvarId!.assign value
      return { root := root.mvarId!, goals }
    let accept (expression : Expr) : SearchM Bool := do
      -- Zero-hole supplied terms also pass the real cancellation/deadline gate.
      checkDeadline
      let (program, proof) ← match query.contract with
        | none => pure (expression, none)
        | some contract => do
          let program ← whnfR (← mkAppM ``Subtype.val #[expression])
          let proof ← mkAppM ``Subtype.property #[expression]
          pure (program, some (proof, mkApp contract program))
      let program ← instantiateMVars program
      let proof ← proof.mapM fun (value, type) => do
        return (← instantiateMVars value, ← instantiateMVars type)
      unless complete program && proof.all (fun (value, type) =>
          complete value && complete type) do return false
      if (← seen.get).contains program then return false
      charge fun work => { work with candidates := work.candidates + 1 }
      match ← gate query.profile program query.target proof with
      | .error _ =>
        charge fun work => { work with rejected := work.rejected + 1 }
        return false
      | .ok candidate =>
        let portable ← protectExport (exportExact originalCore originalMeta query candidate)
        Core.checkInterrupted
        -- Rejection of one proof must not suppress another proof of the same
        -- program's contract under the requested axiom profile.
        seen.modify (·.push program)
        found.modify (·.push portable)
        if (← grace.get).isNone then
          grace.set (some ((← IO.monoMsNow) + query.graceMs))
        if (← found.get).size ≥ query.maxCandidates then return true
        return (← IO.monoMsNow) > (← grace.get).getD 0
    withLane ledger refuted grace timedOut query.budgetMs (name := "sketch") fun context => do
      let configuration ← if prepared.holes.size < 2 || skip.contains "sketchProjection" then
          pure configuration
        else match query.contract with
          | none => pure configuration
          | some contract => do
            let projection? ← prepareProjection? prepared contract (checkDeadline.run context)
            match projection? with
            | none => pure configuration
            | some (projection, observations) => pure { configuration with
                partialPruner := some (pruneOwnedHole projection query.profile contract observations) }
      enumerateInitialized context configuration initializePass accept
        (do return !(← found.get).isEmpty) [2, 3, 4, 5, 6, 7, 9, 12] completed
    let candidates ← found.get
    let work ← ledger.get
    if !candidates.isEmpty then return .verified (← rankCandidates candidates) work
    if work.rejected > 0 && query.contract.isSome then
      return .refutedAll work.rejected work
    return .negative (if ← timedOut.get then .budgetExhausted else .grammarExhausted)
      none work

/-- Complete up to four explicitly named holes in a closed whole-function
sketch. Fixed syntax is retained and completion uses the exact original query;
there is no fallback to unconstrained or universe-specialized search.

The prepared native graph is valid only inside its consumer. Complete portable
outcomes and a name/count report are the only returned values. Caller Core,
Meta, and Term state is restored on every exit; external IO is not rolled back.
The budget is cooperative and does not bound preparation, export, or ranking. -/
def synthesizeSketch (query : Query) (sketch : TSyntax `term) : TermElabM Result := do
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  let originalTerm ← getThe Term.State
  let entered ← IO.mkRef false
  let outcome ← IO.mkRef (none : Option Outcome)
  try
    tryCatchRuntimeEx (do
      Core.checkInterrupted
      let query ← prepareQuery query
      let preparation ← withPreparedSketch query.target sketch fun prepared => do
        entered.set true
        let result ← runPrepared query prepared originalCore originalMeta
        outcome.set (some result)
      let some result ← outcome.get | throwError "leant2 sketch: missing completion outcome"
      Core.checkInterrupted
      return { outcome := result, preparation }) fun ex => do
        if let .internal id payload := ex then
          if id == outputValidationExceptionId then
            throwError "leant2 sketch: output validation failed: {payload.getString `message}"
        if Leant2.isInterrupt ex || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
        if ← entered.get then throw ex
        if (← ex.toMessageData.toString).startsWith "leant2 sketch: preparation failed:" then
          throw ex
        throwError "leant2 sketch: preparation failed: {ex.toMessageData}"
  finally
    modifyThe Term.State fun _ => originalTerm
    modifyThe Meta.State fun _ => originalMeta
    modifyThe Core.State fun _ => originalCore

end Leant2.Frontend.Sketch
