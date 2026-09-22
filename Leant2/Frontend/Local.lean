import Leant2.Frontend.Command

/-!
Local synthesis closes the caller's accessible context, searches in isolation,
and replays the answer at the original type before reopening the telescope.
The engine's own accepted type can differ after classical specialization, so
its acceptance alone is not sufficient for an enclosing Lean declaration.
-/
namespace Leant2.Frontend

open Lean Meta

inductive PreparationFailure where
  | unresolvedDependency
  | unsupportedDependency
  deriving BEq, Inhabited

/-- A closed original goal and the exact arguments needed to reopen it.
Genuine lets remain in the telescope; nondependent haves become parameters. -/
structure LocalQuery where
  target : Expr
  closedTarget : Expr
  locals : Array Expr
  arguments : Array Expr
  levelParams : List Name

private def restoring (action : MetaM α) : MetaM α := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  try action finally
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

/-- No unresolved caller hole is an input to synthesis. Recursive auxiliary
locals and unrelated implementation details are not additional providers. -/
def prepareLocalQuery (expectedType : Expr) : MetaM (Except PreparationFailure LocalQuery) := do
  let target ← instantiateMVars expectedType
  if target.hasMVar || target.hasLevelMVar then return .error .unresolvedDependency
  let mut locals := #[]
  let mut arguments := #[]
  for decl in (← getLCtx) do
    if decl.isAuxDecl || decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if type.hasMVar || type.hasLevelMVar then return .error .unresolvedDependency
    -- Hidden nondependent have-values are not semantically available and need
    -- not remain type-correct. Respect LocalDecl.value?'s default policy.
    if let some value := decl.value? then
      let value ← instantiateMVars value
      if value.hasMVar || value.hasLevelMVar then return .error .unresolvedDependency
    locals := locals.push decl.toExpr
    if !decl.isLet then arguments := arguments.push decl.toExpr
  let closedTarget ← mkForallFVars locals target (usedOnly := false) (usedLetOnly := false)
  let closedTarget ← instantiateMVars closedTarget
  if closedTarget.hasFVar || closedTarget.hasLooseBVars || closedTarget.hasSorry then
    return .error .unsupportedDependency
  if closedTarget.hasMVar || closedTarget.hasLevelMVar then return .error .unresolvedDependency
  let levelParams := (collectLevelParams {} closedTarget).params.toList
  return .ok { target, closedTarget, locals, arguments, levelParams }

/-- Independent original-environment replay. This public internal seam also
lets adversarial tests submit malformed or specialized engine candidates. -/
def replayLocalCandidate (query : LocalQuery) (profile : Profile) (program : Expr) :
    MetaM (Option Expr) := restoring <| withNewMCtxDepth do
  if program.hasMVar || program.hasLevelMVar || program.hasFVar ||
      program.hasLooseBVars || program.hasSorry then return none
  let usedLevels := (collectLevelParams {} program).params.toList
  unless usedLevels.all query.levelParams.contains do return none
  -- The original target, not the candidate's recorded specialized type, is
  -- supplied to the synchronous kernel check and the requested axiom policy.
  match ← withLCtx {} #[] <| gate profile program query.closedTarget none with
  | .error _ => return none
  | .ok _ => pure ()
  let value := mkAppN program query.arguments
  if value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then return none
  unless (collectFVars {} value).fvarIds.all (fun id => query.locals.contains (mkFVar id)) do
    return none
  check value
  unless ← isDefEq (← inferType value) query.target do return none
  -- Reclosing also checks the meaning of preserved lets and the argument map.
  let closedValue ← mkLambdaFVars query.locals value (usedOnly := false) (usedLetOnly := false)
  match ← withLCtx {} #[] <| gate profile closedValue query.closedTarget none with
  | .error _ => return none
  | .ok _ => return some value

/-- Search with a closed local telescope, restoring all speculative native
state. Keep the engine's bounded collection and ranking; replay candidates in
that order. Failure is a frontend failure, never a proof of the local goal's
mathematical impossibility. No result aliases or declarations are published. -/
def synthesizeLocal (query : LocalQuery) (providers : Array Name) (budgetMs : Nat)
    (profile : Profile := .standard) : MetaM Expr := do
  let outcome ← restoring <| withNewMCtxDepth <| withLCtx {} #[] do
    runQuery { target := query.closedTarget, providers, budgetMs, profile }
  match outcome with
  | .verified candidates _ =>
    for candidate in candidates do
      if let some value ← replayLocalCandidate query profile candidate.program then
        return value
    throwError "leant2: synthesis failed: no accepted candidate replays at the original expected type"
  | .negative .budgetExhausted .. =>
    throwError "leant2: synthesis failed: budget exhausted without a result at the expected type"
  | .preflightError message => throwError "leant2: {message}"
  | _ => throwError "leant2: synthesis failed: no term found at the expected type within the search bounds"

end Leant2.Frontend
