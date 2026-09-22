import Leant2.Frontend.Suggestion
import Lean.Meta.Tactic.TryThis

/-! Expected-type term and tactic frontends. Search uses the standard axiom
profile; local hypotheses are parameters of the certified closed query. -/
namespace Leant2.Frontend

open Lean Meta Elab Term Tactic

private def prepareExpected (expectedType? : Option Expr) (postpone := true) : TermElabM LocalQuery := do
  let some expectedType := expectedType? | do
    if postpone then tryPostpone
    throwError "synth%: an expected type is required"
  match ← prepareLocalQuery expectedType with
  | .ok query => return query
  | .error .unresolvedDependency =>
    if postpone then tryPostpone
    throwError "leant2: the expected type or local context contains unresolved metavariables"
  | .error .unsupportedDependency =>
    throwError "leant2: the expected type depends on an unsupported local declaration"

private def localProviders : TermElabM (Array Name) := do
  let providers := curatedProviders ++ (← sessionConstants)
  let current := (← read).declName?
  return providers.filter (fun name => current != some name)

/-- Return the exact checked expression; compiler adapters are supplementary
checked declarations and do not replace that expression. -/
private def synthesizeExpected (query : LocalQuery) : TermElabM Expr := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  let termState ← getThe Term.State
  let (result, _) ← tryFinally' (do
    let value ← synthesizeLocal query (← localProviders) (leant2.budgetMs.get (← getOptions))
    Presentation.prepareProgram value
    return value) fun result? => do
      if result?.isNone then
        modifyThe Term.State fun _ => termState
        modifyThe Meta.State fun _ => metaState
        modifyThe Core.State fun _ => coreState
  return result

syntax (name := synthTerm) "synth%" : term

@[term_elab synthTerm] def elabSynthTerm : TermElab := fun _ expectedType? =>
  withoutErrToSorry do
    synthesizeExpected (← prepareExpected expectedType?)

syntax (name := leant2Tactic) "leant2" : tactic

/-- Validate generated source against the pre-synthesis state. Complete state
restoration also drops auxiliary definitions emitted by speculative parsing.
Native cancellation and runtime exceptions keep their original identity.
This internal validation seam is also exercised with diagnostic-producing and
goal-producing elaborators. Existing sibling goals must remain unsolved. -/
def validatesSuggestion (initial : Tactic.SavedState) (goal : MVarId)
    (query : LocalQuery) (tacticSyntax : TSyntax `tactic) : TacticM Bool := do
  let current ← Tactic.saveState
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  let termState ← getThe Term.State
  let tacticState ← getThe Tactic.State
  try
    initial.restore
    let siblings := (← getUnsolvedGoals).filter (· != goal)
    let pendingRecursors := (← getThe Term.State).letRecsToLift.length
    let errorsBefore := ((← getThe Core.State).messages.toList.filter
      (·.severity == .error)).length
    withoutErrToSorry <| withoutRecover <| evalTactic tacticSyntax
    if ((← getThe Core.State).messages.toList.filter (·.severity == .error)).length > errorsBefore then
      return false
    unless (← getUnsolvedGoals) == siblings do return false
    unless ← goal.isAssigned do return false
    let value ← instantiateMVars (mkMVar goal)
    if value.hasLevelMVar || value.hasSorry || value.hasLooseBVars then return false
    if value.hasExprMVar then
      -- Native local recursion stays behind synthetic opaque metavariables
      -- until the enclosing declaration's mutual-definition closure runs.
      -- Finish that pipeline only after this replay passed the goal/diagnostic
      -- guards; the completed temporary declaration must itself be hole-free.
      unless (← getThe Term.State).letRecsToLift.length > pendingRecursors do return false
      initial.restore
      return ← goal.withContext <| validateCompletedSuggestion query tacticSyntax
    goal.withContext do
      let closed ← mkLambdaFVars query.locals value (usedOnly := false) (usedLetOnly := false)
      return (← replayLocalCandidate query .standard closed).isSome
  catch ex =>
    if Leant2.isInterrupt ex then throw ex
    return false
  finally
    current.restore
    modifyThe Tactic.State fun _ => tacticState
    modifyThe Term.State fun _ => termState
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

private def suggest (ref : Syntax) (initial : Tactic.SavedState) (goal : MVarId)
    (query : LocalQuery) (value : Expr) : TacticM Unit := do
  try
    let tacticSyntax ← goal.withContext <| withExposedNames do
      let term ← Presentation.programSyntax value
      `(tactic| exact $term)
    if ← validatesSuggestion initial goal query tacticSyntax then
      Meta.Tactic.TryThis.addSuggestion ref { suggestion := tacticSyntax }
      return
    let exposed ← `(tactic| (expose_names; $tacticSyntax))
    if ← validatesSuggestion initial goal query exposed then
      Meta.Tactic.TryThis.addSuggestion ref { suggestion := exposed }
      return
    logInfo "leant2: synthesized a checked term; a replayable source suggestion was unavailable"
  catch ex =>
    if Leant2.isInterrupt ex then throw ex
    logInfo "leant2: synthesized a checked term; a replayable source suggestion was unavailable"

@[tactic leant2Tactic] def evalLeant2 : Tactic := fun stx => do
  let initial ← Tactic.saveState
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  let termState ← getThe Term.State
  let tacticState ← getThe Tactic.State
  let (result, _) ← tryFinally' (do
    let goal ← getMainGoal
    goal.withContext do
      let query ← prepareExpected (some (← goal.getType)) (postpone := false)
      let value ← synthesizeExpected query
      unless ← goal.checkedAssign value do
        throwError "leant2: checked assignment to the original goal failed"
      replaceMainGoal []
      suggest stx initial goal query value) fun result? => do
        if result?.isNone then
          modifyThe Tactic.State fun _ => tacticState
          modifyThe Term.State fun _ => termState
          modifyThe Meta.State fun _ => metaState
          modifyThe Core.State fun _ => coreState
  return result

end Leant2.Frontend
