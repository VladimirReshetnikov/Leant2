import Leant2.Frontend.Sketch.Prepare
import Leant2.Accept.Gate
import Leant2.Behavior.Observations
import Leant2.Native.Pruning

/-! Typed views of prepared sketches for conservative whole-owned-hole
observation checks. Native closure expansion runs only after ground, typed
placeholder assignments in an isolated weakened copy of the owned graph.
Partly completed holes remain opaque; the original graph is never committed.
-/

namespace Leant2.Frontend.Sketch.Projection
open Lean Meta

private def frozen (e : Expr) : Bool :=
  !e.hasExprMVar && !e.hasLevelMVar && !e.hasLooseBVars && !e.hasSorry

private def closed (e : Expr) : Bool := frozen e && !e.hasFVar

/-- Restore all backtrackable state even when native resource/cancel exceptions
are not caught by an ordinary MetaM exception handler. No depth increment. -/
private def isolated (action : MetaM α) : MetaM α := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  try action
  finally
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

private def requireDepth (depth : Nat) : MetaM Unit := do
  unless (← getMCtx).depth == depth do
    throwError "projection: changed owned metavariable depth"

/-- Synchronous safe declaration check, including the expression's exact type.
The returned environment is inspected only for axiom accounting, never installed
persistently. Universes must already be rigid; there is no generalization. -/
private def replay (e type : Expr) : MetaM Unit := withLCtx {} #[] do
  unless closed e && closed type do
    throwError "projection: replay input is not closed and frozen"
  let params := (collectLevelParams (collectLevelParams {} type) e).params.toList
  let .ok _ ← kernelCheckAndAudit `Leant2.Frontend.Sketch.Projection e type params false
    | throwError "projection: independent safe kernel replay failed"
  pure ()

private def requireCdeclContext (declaration : MetavarDecl) : MetaM Unit :=
  withLCtx declaration.lctx declaration.localInstances do
    -- Preparation checks native instantiations but deliberately preserves the
    -- original declarations. Assigned inference variables may remain in their
    -- stored syntax; unresolved dependencies are still forbidden here.
    let type ← instantiateMVars declaration.type
    unless frozen type do
      throwError "projection: graph declaration type is not frozen"
    Meta.check type
    unless (← whnf (← inferType type)).isSort do
      throwError "projection: graph declaration is not a type"
    for entry in declaration.lctx do
      if entry.isAuxDecl then throwError "projection: auxiliary original local excluded"
      match entry with
      | .ldecl .. => throwError "projection: original let/have local excluded"
      | .cdecl .. => pure ()
      let type ← instantiateMVars entry.type
      unless frozen type do
        throwError "projection: local declaration type is not frozen"
      Meta.check type

structure HoleInterface where
  owned : OwnedHole
  arguments : Array Expr
  closedType : Expr

/-- Lifetime is the enclosing prepared callback: interfaces retain original
goal identities. Only skeleton and its closed type are portable expressions. -/
structure State where
  prepared : Prepared
  interfaces : Array HoleInterface
  skeleton : Expr
  skeletonType : Expr

private def graphIds (prepared : Prepared) : Array MVarId := Id.run do
  let mut out := prepared.holes.map (·.pending)
  for wrapper in prepared.wrappers do
    for id in #[wrapper.outer, wrapper.pending] do
      unless out.contains id do out := out.push id
  return out

/-- Both scope and type are checked. checkedAssign by itself checks only the
dependency condition. Inputs may mention only locals available in this goal. -/
private def typedAssign (goal : MVarId) (value : Expr) : MetaM Unit := goal.withContext do
  unless (← goal.isAssignable) && !(← goal.isAssigned) && !(← goal.isDelayedAssigned) do
    throwError "projection: assignment target is not an open owned-depth goal"
  Meta.check value
  unless ← isDefEq (← inferType value) (← goal.getType) do
    throwError "projection: assignment type mismatch"
  unless ← goal.checkedAssign value do
    throwError "projection: assignment dependency check failed"

private def withParameters (interfaces : Array HoleInterface)
    (consume : Array Expr → MetaM α) : MetaM α := do
  let nested := interfaces.foldr (init := consume) fun item next parameters =>
    withLocalDeclD item.owned.spec.sourceName item.closedType fun parameter =>
      next (parameters.push parameter)
  nested #[]

/-- Build before search assigns any original owned hole. The caller's check
keeps preparation within its cooperative resource/cancellation policy. -/
def build (prepared : Prepared)
    (check : MetaM Unit := Core.checkInterrupted) : MetaM State :=
  isolated <| withLCtx {} #[] do
    requireDepth prepared.depth
    check
    unless closed prepared.expected do throwError "projection: expected type is not frozen"
    let ids := graphIds prepared
    unless ids.size ≤ 256 do throwError "projection: graph inventory limit"
    for id in ids do
      check
      let declaration ← id.getDecl
      unless declaration.depth == prepared.depth do throwError "projection: foreign graph depth"
      requireCdeclContext declaration
    for wrapper in prepared.wrappers do
      let some assignment ← getDelayedMVarAssignment? wrapper.outer
        | throwError "projection: native delayed wrapper disappeared"
      unless assignment.mvarIdPending == wrapper.pending && assignment.fvars == wrapper.arguments do
        throwError "projection: native delayed wrapper changed"
      if ← wrapper.outer.isAssigned then
        throwError "projection: cached wrapper assignment before construction"
    let interfaces ← prepared.holes.mapM fun owned => owned.pending.withContext do
      unless !(← owned.pending.isAssigned) && !(← owned.pending.isDelayedAssigned) do
        throwError "projection: build requires original open owned holes"
      let arguments := owned.declaration.lctx.getFVars
      let closedType ← mkForallFVars arguments owned.declaration.type
        (usedOnly := false) (usedLetOnly := false)
      let closedType ← instantiateMVars closedType
      unless closed closedType do throwError "projection: incomplete closed hole interface"
      return { owned, arguments, closedType : HoleInterface }
    withParameters interfaces fun parameters => do
      let parameterContext ← getLCtx
      -- Uniform prefix weakening preserves every original fvar identity and
      -- relative order; parameter types are closed and introduce no instances.
      -- No source expression, delayed fvar array, or universe is rewritten.
      for id in ids do
        let declaration ← id.getDecl
        let weakened := declaration.lctx.foldl
          (fun context entry => context.addDecl entry) parameterContext
        id.modifyDecl fun original => { original with lctx := weakened }
      check
      for index in [:interfaces.size] do
        check
        let some item := interfaces[index]? | throwError "projection: missing hole interface"
        let value := mkAppN parameters[index]! item.arguments
        unless frozen value do throwError "projection: placeholder assignment contains a hole"
        typedAssign item.owned.pending value
      check
      requireDepth prepared.depth
      let projected ← instantiateMVars prepared.expression
      unless frozen projected do throwError "projection: native closure expansion remains incomplete"
      Meta.check projected
      unless ← isDefEq (← inferType projected) prepared.expected do
        throwError "projection: projected original root changed type"
      check
      let skeleton ← mkLambdaFVars parameters projected (usedOnly := false)
      let skeletonType ← mkForallFVars parameters prepared.expected (usedOnly := false)
      check
      replay skeleton skeletonType
      check
      requireDepth prepared.depth
      return { prepared, interfaces, skeleton, skeletonType }

/-- Partial assignments, including ordinary assignments containing fresh child
goals, are opaque. A complete body must close in the ORIGINAL frozen context,
not a search-modified context or the weakened projection context. -/
private def completedClosure? (item : HoleInterface) : MetaM (Option Expr) := do
  let body ← instantiateMVars (mkMVar item.owned.pending)
  if body.hasExprMVar then return none
  unless frozen body do throwError "projection: completed body has unresolved universe or sorry"
  withLCtx item.owned.declaration.lctx item.owned.declaration.localInstances do
    Meta.check body
    unless ← isDefEq (← inferType body) item.owned.declaration.type do
      throwError "projection: completed body changed original hole type"
    let value ← mkLambdaFVars item.arguments body (usedOnly := false) (usedLetOnly := false)
    let value ← instantiateMVars value
    unless closed value do throwError "projection: completed body escaped its original telescope"
    replay value item.closedType
    return some value

/-- The callback must not retain free placeholders. No cross-call cache or
search child inspection. Every exit restores native instantiation's changes. -/
def withView (projection : State)
    (consume : Array Expr → Expr → Array Bool → MetaM α)
    (check : MetaM Unit := Core.checkInterrupted) : MetaM α := isolated do
  requireDepth projection.prepared.depth
  check
  let completed ← projection.interfaces.mapM fun item => do
    check
    let result ← completedClosure? item
    check
    return result
  withLCtx {} #[] <| withParameters projection.interfaces fun parameters => do
    let arguments := Array.zipWith (fun value placeholder => value.getD placeholder) completed parameters
    -- Keep even unused completed-interface arguments in the evidence syntax.
    -- Only the kernel observation evaluator may erase them by reduction.
    let view := mkAppN projection.skeleton arguments
    unless frozen view do throwError "projection: view is not metavariable-free"
    Meta.check view
    unless ← isDefEq (← inferType view) projection.prepared.expected do
      throwError "projection: view changed exact original target"
    let closedView ← mkLambdaFVars parameters view (usedOnly := false)
    check
    replay closedView projection.skeletonType
    check
    let result ← consume parameters view (completed.map Option.isSome)
    check
    requireDepth projection.prepared.depth
    return result

/-- Unsupported ordinary shapes disable this optional projection. Every
internal or runtime exception remains owned by its caller, including native
cancellation, deadline/grace/quota exceptions, heartbeat and recursion limits.
The underlying build restores native state before this handler runs. -/
def tryBuild (prepared : Prepared) (check : MetaM Unit := Core.checkInterrupted) :
    MetaM (Option State) :=
  tryCatchRuntimeEx (do return some (← build prepared check)) fun exception =>
    match exception with
    | .internal .. => throw exception
    | .error .. =>
      if exception.isInterrupt || exception.isRuntime || exception.isMaxHeartbeat ||
          exception.isMaxRecDepth then throw exception
      else pure none

/-- Evaluate supplied necessary observations on a typed parametric view. A
false result must be authorized by the query profile in three unreduced
schemas: the full original contract application, the actual predicate, and
the actual decider. Keeping application syntax preserves dependencies erased
by beta reduction or observation decomposition. The caller is responsible for
supplying observations that are necessary conditions of that contract.

There is no cross-call cache and no accepted result/proof assignment. Ordinary
unsupported failures may throw; the integrating optional search rule can
treat them as inconclusive. Native/resource exceptions preserve identity. -/
def observe (projection : State) (profile : Profile) (originalContract : Expr)
    (observations : Array Observation) (check : MetaM Unit := Core.checkInterrupted) :
    MetaM ObservationReport :=
  withView projection (fun parameters view _ => do
    let authorize (predicate decider : Expr) : MetaM Bool := do
      check
      let original := mkApp originalContract view
      Meta.check original
      unless ← isDefEq (← inferType original) (mkSort .zero) do
        throwError "projection: original contract is not a proposition"
      let schema ← mkLambdaFVars parameters original (usedOnly := false)
      let schemaType ← mkForallFVars parameters (mkSort .zero) (usedOnly := false)
      check
      replay schema schemaType
      check
      let originalAllowedNow ← falseEvidenceAllowed profile schema schema
      unless originalAllowedNow do return false
      let proposition := mkApp predicate view
      let decision := mkApp decider view
      let predicateSchema ← mkLambdaFVars parameters proposition (usedOnly := false)
      let deciderSchema ← mkLambdaFVars parameters decision (usedOnly := false)
      let predicateType ← mkForallFVars parameters (← inferType proposition) (usedOnly := false)
      let deciderType ← mkForallFVars parameters (← inferType decision) (usedOnly := false)
      check
      replay predicateSchema predicateType
      replay deciderSchema deciderType
      check
      falseEvidenceAllowed profile predicateSchema deciderSchema
    let (report, _) ← evalObservations observations view #[] instantiateMVars check authorize
    return report) check

end Leant2.Frontend.Sketch.Projection
