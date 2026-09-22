import Leant2.Frontend.Sketch.Projection

/-! Conservative observation of a prepared hole containing fresh search
children. Closed typed interfaces ground an isolated native graph; original
contexts, raw dependencies and the full original contract remain authoritative.
Unsupported graphs disable this optional pruning attempt. -/
namespace Leant2.Frontend.Sketch.ChildProjection
open Lean Meta
open Leant2 Leant2.Frontend.Sketch

def frozen (e : Expr) : Bool :=
  !e.hasExprMVar && !e.hasLevelMVar && !e.hasLooseBVars && !e.hasSorry

def closed (e : Expr) : Bool := frozen e && !e.hasFVar

def isolated (action : MetaM α) : MetaM α := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  try action
  finally
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

def replay (value type : Expr) : MetaM Unit := withLCtx {} #[] do
  unless closed value && closed type do throwError "child projection: open replay input"
  let params := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let .ok _ ← kernelCheckAndAudit `Leant2.Frontend.Sketch.ChildProjection value type params false
    | throwError "child projection: safe kernel replay failed"

def typedAssign (goal : MVarId) (value : Expr) : MetaM Unit := goal.withContext do
  unless (← goal.isAssignable) && !(← goal.isAssigned) && !(← goal.isDelayedAssigned) do
    throwError "child projection: assignment target is not open at current depth"
  Meta.check value
  unless ← isDefEq (← inferType value) (← goal.getType) do
    throwError "child projection: assignment type mismatch"
  unless ← goal.checkedAssign value do throwError "child projection: scope mismatch"

structure State where
  base : Projection.State
  /-- Persistent membership only; never reinstalled by extraction. -/
  beforeSearch : MetavarContext

/-- Native introduction creates synthetic opaque goals, while native apply
uses forallMetaTelescopeReducing's natural kind. Kind alone grants no ownership:
both still require fresh baseline membership, exact depth and frozen scopes.
Synthetic elaborator obligations remain outside this fragment. -/
def admissibleChildKind (kind : MetavarKind) : Bool :=
  kind.isNatural || kind.isSyntheticOpaque

def build (prepared : Prepared) (check : MetaM Unit := Core.checkInterrupted) : MetaM State := do
  let beforeSearch ← getMCtx
  let base ← Projection.build prepared check
  return { base, beforeSearch }

/-- Admission limits for optional extraction. Reaching a limit is
inconclusive and preserves ordinary search. IO counters are not refunded by
backtrackable native-state restoration. -/
structure Limits where
  nodes : Nat := 64
  leaves : Nat := 8
  syntaxNodes : Nat := 8192
  constants : Nat := 256

structure Node where
  id : MVarId
  declaration : MetavarDecl
  regular : Option Expr
  delayed : Option DelayedMetavarAssignment

structure Inventory where
  nodes : Array Node := #[]
  constants : Array Expr := #[]
  auditSeen : Array MVarId := #[]
  syntaxNodes : Nat := 0

private def step (ref : IO.Ref Inventory) (limits : Limits) (check : MetaM Unit) : MetaM Unit := do
  check
  let current ← ref.get
  if current.syntaxNodes ≥ limits.syntaxNodes then throwError "child projection: syntax quota"
  ref.modify fun state => { state with syntaxNodes := state.syntaxNodes + 1 }

/-- Raw syntax collection: no instantiation, beta reduction, or whnf here.
Returned mvars are graph edges; constants retain their actual universe instances. -/
private partial def scan (ref : IO.Ref Inventory) (limits : Limits) (check : MetaM Unit)
    (expression : Expr) : MetaM (Array MVarId) := do
  step ref limits check
  match expression with
  | .mvar id => return #[id]
  | .const .. =>
    unless (← ref.get).constants.contains expression do
      if (← ref.get).constants.size ≥ limits.constants then
        throwError "child projection: constant inventory quota"
      ref.modify fun state => { state with constants := state.constants.push expression }
    return #[]
  | .app fn arg => return (← scan ref limits check fn) ++ (← scan ref limits check arg)
  | .lam _ domain body _ | .forallE _ domain body _ =>
    return (← scan ref limits check domain) ++ (← scan ref limits check body)
  | .letE _ type value body _ =>
    return (← scan ref limits check type) ++ (← scan ref limits check value) ++
      (← scan ref limits check body)
  | .mdata _ body | .proj _ _ body => scan ref limits check body
  | _ => return #[]

/-- Types can retain assigned inference nodes from an outer elaboration depth.
They are read for dependency inventory only, never weakened or assigned here. -/
private partial def auditSyntax (ref : IO.Ref Inventory) (limits : Limits)
    (check : MetaM Unit) (expression : Expr) (path : Array MVarId := #[]) : MetaM Unit := do
  for id in ← scan ref limits check expression do
    if path.contains id then throwError "child projection: cyclic audit dependency"
    if (← ref.get).auditSeen.contains id then continue
    if (← ref.get).auditSeen.size ≥ limits.nodes then
      throwError "child projection: audit graph quota"
    ref.modify fun state => { state with auditSeen := state.auditSeen.push id }
    let declaration ← id.getDecl
    auditSyntax ref limits check declaration.type (path.push id)
    for entry in declaration.lctx do
      auditSyntax ref limits check entry.type (path.push id)
      if let some value := entry.value? (allowNondep := true) then
        auditSyntax ref limits check value (path.push id)
    if let some value ← getExprMVarAssignment? id then
      auditSyntax ref limits check value (path.push id)
    else if let some delayed ← getDelayedMVarAssignment? id then
      auditSyntax ref limits check (mkMVar delayed.mvarIdPending) (path.push id)

private partial def visit (ref : IO.Ref Inventory) (limits : Limits) (check : MetaM Unit)
    (depth : Nat) (id : MVarId) (path : Array MVarId := #[]) : MetaM Unit := do
  check
  if path.contains id then throwError "child projection: cyclic native graph"
  if (← ref.get).nodes.any (·.id == id) then return
  if (← ref.get).nodes.size ≥ limits.nodes then throwError "child projection: node quota"
  let declaration ← id.getDecl
  unless declaration.depth == depth do throwError "child projection: foreign graph depth"
  let regular ← getExprMVarAssignment? id
  let delayed ← getDelayedMVarAssignment? id
  if regular.isSome && delayed.isSome then
    throwError "child projection: dual regular/delayed assignment is outside this fragment"
  ref.modify fun state => { state with nodes := state.nodes.push { id, declaration, regular, delayed } }
  auditSyntax ref limits check declaration.type
  for entry in declaration.lctx do
    auditSyntax ref limits check entry.type
    if let some value := entry.value? (allowNondep := true) then
      auditSyntax ref limits check value
  if let some value := regular then
    if value.hasSorry || value.hasLooseBVars then throwError "child projection: invalid raw assignment"
    unless (collectFVars {} value).fvarIds.all (fun fvar => (declaration.lctx.find? fvar).isSome) do
      throwError "child projection: raw assignment escaped its context"
    for next in ← scan ref limits check value do
      visit ref limits check depth next (path.push id)
  else if let some link := delayed then
    let pending ← link.mvarIdPending.getDecl
    for argument in link.fvars do
      let .fvar fvar := argument | throwError "child projection: non-fvar delayed argument"
      unless (pending.lctx.find? fvar).isSome do throwError "child projection: delayed argument escaped"
    visit ref limits check depth link.mvarIdPending (path.push id)

private def validateContext (declaration : MetavarDecl) : MetaM Unit :=
  withLCtx declaration.lctx declaration.localInstances do
    let type ← instantiateMVars declaration.type
    unless frozen type do throwError "child projection: unresolved declaration type"
    Meta.check type
    unless (← whnf (← inferType type)).isSort do throwError "child projection: declaration is not a type"
    for entry in declaration.lctx do
      if entry.isAuxDecl then throwError "child projection: auxiliary local"
      if entry.isLet then throwError "child projection: let/have local"
      let type ← instantiateMVars entry.type
      unless frozen type do throwError "child projection: unresolved local type"
      Meta.check type

structure ChildInterface where
  id : MVarId
  declaration : MetavarDecl
  arguments : Array Expr
  closedType : Expr

structure View where
  wholeParameters : Array Expr
  childParameters : Array Expr
  childInterfaces : Array ChildInterface
  program : Expr
  partialClosure : Expr
  auditConstants : Array Expr

def View.parameters (view : View) : Array Expr := view.wholeParameters ++ view.childParameters

private def parameters (types : Array (Name × Expr))
    (consume : Array Expr → MetaM α) : MetaM α := do
  let nested := types.foldr (init := consume) fun (name, type) next values =>
    withLocalDeclD name type fun parameter => next (values.push parameter)
  nested #[]

private def originalClosure? (replayCheck : Expr → Expr → MetaM Unit)
    (item : Projection.HoleInterface) : MetaM (Option Expr) := do
  let body ← instantiateMVars (mkMVar item.owned.pending)
  if body.hasExprMVar then return none
  unless frozen body do throwError "child projection: completed body is not frozen"
  withLCtx item.owned.declaration.lctx item.owned.declaration.localInstances do
    Meta.check body
    unless ← isDefEq (← inferType body) item.owned.declaration.type do
      throwError "child projection: completed body changed original type"
    let value ← mkLambdaFVars item.arguments body (usedOnly := false) (usedLetOnly := false)
    let value ← instantiateMVars value
    replayCheck value item.closedType
    return some value

private def requireDepth (state : State) : MetaM Unit := do
  unless (← getMCtx).depth == state.base.prepared.depth do
    throwError "child projection: changed prepared depth"

/-- One selected owned hole. Callback values containing free parameters must
not escape; a closed abstracted expression may be returned for correspondence
tests. Every exit restores Core/Meta, including successful extraction. -/
private def withPartialViewWithReplay (replayCheck : Expr → Expr → MetaM Unit)
    (state : State) (selected : MVarId) (consume : View → MetaM α)
    (check : MetaM Unit := Core.checkInterrupted) (limits : Limits := {}) : MetaM α := isolated do
  requireDepth state
  check
  let some index := state.base.interfaces.findIdx? (·.owned.pending == selected)
    | throwError "child projection: selected root is not an owned hole"
  unless (← selected.isAssigned) || (← selected.isDelayedAssigned) do
    throwError "child projection: selected root has no chosen body"
  let ref ← IO.mkRef ({} : Inventory)
  visit ref limits check state.base.prepared.depth selected
  let selectedNodes := (← ref.get).nodes
  if selectedNodes.any (fun node => node.id != selected &&
      state.base.prepared.holes.any (·.pending == node.id)) then
    throwError "child projection: selected graph crosses another original owned hole"
  let leaves := selectedNodes.filter fun node => node.regular.isNone && node.delayed.isNone
  if leaves.isEmpty || leaves.size > limits.leaves then
    throwError "child projection: empty or excessive child frontier"
  for node in leaves do
    unless admissibleChildKind node.declaration.kind && !state.beforeSearch.decls.contains node.id do
      throwError "child projection: pre-search or non-owned child leaf"
    if state.base.prepared.holes.any (·.pending == node.id) then
      throwError "child projection: sibling owned hole in child frontier"
  -- Capture all actual owned arguments before any native instantiation. This
  -- includes completed children even if parent reduction later erases them.
  for item in state.base.interfaces do
    visit ref limits check state.base.prepared.depth item.owned.pending
  let inventory ← ref.get
  for node in inventory.nodes do
    check
    validateContext node.declaration
  let children ← leaves.mapM fun node => node.id.withContext do
    let type ← instantiateMVars node.declaration.type
    let unsupported ← forallTelescopeReducing type fun _ result => do
      return (← whnf result).isSort || (← isProp result) || (← isClass? result).isSome
    if unsupported then throwError "child projection: type/proof/class child"
    let arguments := node.declaration.lctx.getFVars
    let closedType ← mkForallFVars arguments node.declaration.type
      (usedOnly := false) (usedLetOnly := false)
    let closedType ← instantiateMVars closedType
    unless closed closedType do throwError "child projection: incomplete child telescope"
    return { id := node.id, declaration := node.declaration, arguments, closedType : ChildInterface }
  let constants ← inventory.constants.mapM fun constant => do
    check
    let constant ← instantiateMVars constant
    unless closed constant do throwError "child projection: raw dependency has open universes"
    withLCtx {} #[] do
      let type ← inferType constant
      unless closed type do throwError "child projection: dependency type is not frozen"
      Meta.check constant
    return constant
  -- Classify ordinary completed arguments before placeholder assignments make
  -- the selected fragment appear completed.
  let completed ← state.base.interfaces.mapM (originalClosure? replayCheck)
  unless completed[index]!.isNone do throwError "child projection: selected hole is already complete"
  withLCtx {} #[] <| parameters
      (state.base.interfaces.map fun item => (item.owned.spec.sourceName, item.closedType)) fun wholeParameters =>
    parameters (children.map fun item => (`child, item.closedType)) fun childParameters => do
      let parameterContext ← getLCtx
      for node in selectedNodes do
        let weakened := node.declaration.lctx.foldl
          (fun context entry => context.addDecl entry) parameterContext
        node.id.modifyDecl fun original => { original with lctx := weakened }
      for childIndex in [:children.size] do
        check
        let some item := children[childIndex]? | throwError "child projection: missing child interface"
        typedAssign item.id (mkAppN childParameters[childIndex]! item.arguments)
      -- Independently validate each actual assigned node after grounding.
      for node in selectedNodes do
        check
        -- Native delayed wrappers are intentionally not instantiated bare.
        -- Validate their actual full application in the pending goal context.
        let contextId := node.delayed.map (·.mvarIdPending) |>.getD node.id
        contextId.withContext do
          let source := match node.delayed with
            | some link => mkAppN (mkMVar node.id) link.fvars
            | none => mkMVar node.id
          let expected ← instantiateMVars (← inferType source)
          let value ← instantiateMVars source
          unless frozen value do throwError "child projection: native node remains incomplete"
          Meta.check value
          unless frozen expected && (← isDefEq (← inferType value) expected) do
            throwError "child projection: grounded node type changed"
          let args := (← getLCtx).getFVars
          let value ← mkLambdaFVars args value (usedOnly := false) (usedLetOnly := false)
          let type ← mkForallFVars args expected (usedOnly := false) (usedLetOnly := false)
          replayCheck (← instantiateMVars value) (← instantiateMVars type)
      let some item := state.base.interfaces[index]? | throwError "child projection: missing original interface"
      let body ← instantiateMVars (mkMVar selected)
      let partialClosure ← selected.withContext do
        let value ← mkLambdaFVars item.arguments body (usedOnly := false) (usedLetOnly := false)
        instantiateMVars value
      unless frozen partialClosure do throwError "child projection: partial closure remains unfinished"
      unless ← isDefEq (← inferType partialClosure) item.closedType do
        throwError "child projection: partial closure changed original owned interface"
      let arguments := Array.zipWith (fun value parameter => value.getD parameter) completed wholeParameters
      let arguments := arguments.set! index partialClosure
      let program := mkAppN state.base.skeleton arguments
      let allParameters := wholeParameters ++ childParameters
      Meta.check program
      unless frozen program && (← isDefEq (← inferType program) state.base.prepared.expected) do
        throwError "child projection: composed program has changed type or holes"
      let closedProgram ← mkLambdaFVars allParameters program (usedOnly := false)
      let closedType ← mkForallFVars allParameters state.base.prepared.expected (usedOnly := false)
      replayCheck closedProgram closedType
      check
      let result ← consume {
        wholeParameters, childParameters, childInterfaces := children,
        program, partialClosure, auditConstants := constants }
      check
      requireDepth state
      return result

/-- Eager API: every independent replay still precedes the external callback,
in the same construction order as before. No provisional View escapes here. -/
def withPartialView (state : State) (selected : MVarId) (consume : View → MetaM α)
    (check : MetaM Unit := Core.checkInterrupted) (limits : Limits := {}) : MetaM α :=
  withPartialViewWithReplay replay state selected consume check limits

def tryPartialView (state : State) (selected : MVarId) (consume : View → MetaM α)
    (check : MetaM Unit := Core.checkInterrupted) (limits : Limits := {}) : MetaM (Option α) :=
  tryCatchRuntimeEx (do return some (← withPartialView state selected consume check limits)) fun exception =>
    match exception with
    | .internal .. => throw exception
    | .error .. =>
      if exception.isInterrupt || exception.isRuntime || exception.isMaxHeartbeat || exception.isMaxRecDepth then
        throw exception
      else return none

/-- Add dependencies only to authorization syntax, never to evaluation. -/
def anchor (constants : Array Expr) (schema : Expr) (check : MetaM Unit) : MetaM Expr := do
  let mut result := schema
  for constant in constants do
    check
    let type ← inferType constant
    unless closed constant && closed type do throwError "child projection: open audit anchor"
    result := mkApp (mkLambda `unusedDependency .default type result) constant
  return result

private def observeViewWithReplay (replayCheck : Expr → Expr → MetaM Unit)
    (beforeRefuted : MetaM Unit)
    (view : View) (profile : Profile) (originalContract : Expr)
    (observations : Array Observation) (check : MetaM Unit := Core.checkInterrupted) : MetaM ObservationReport := do
  let authorize (predicate decider : Expr) : MetaM Bool := do
    check
    let originalApplication := mkApp originalContract view.program
    Meta.check originalApplication
    unless ← isDefEq (← inferType originalApplication) (mkSort .zero) do
      throwError "child projection: original contract is not a proposition"
    let schema (value : Expr) : MetaM (Expr × Expr) := do
      Meta.check value
      let type ← inferType value
      let value ← mkLambdaFVars view.parameters value (usedOnly := false)
      let type ← mkForallFVars view.parameters type (usedOnly := false)
      let anchored ← anchor view.auditConstants value check
      -- Profile refusal is checked before replay so unsafe raw dependencies
      -- refuse false rather than becoming a generic extraction error.
      return (anchored, type)
    let (original, originalType) ← schema originalApplication
    unless ← falseEvidenceAllowed profile original original do return false
    replayCheck original originalType
    let (proposition, propositionType) ← schema (mkApp predicate view.program)
    let (decision, decisionType) ← schema (mkApp decider view.program)
    unless ← falseEvidenceAllowed profile proposition decision do return false
    replayCheck proposition propositionType
    replayCheck decision decisionType
    beforeRefuted
    check
    return true
  let (report, _) ← evalObservations observations view.program #[] instantiateMVars check authorize
  return report

def observeView (view : View) (profile : Profile) (originalContract : Expr)
    (observations : Array Observation) (check : MetaM Unit := Core.checkInterrupted) : MetaM ObservationReport :=
  observeViewWithReplay replay (pure ()) view profile originalContract observations check

private structure ReplayObligation where
  value : Expr
  type : Expr

/-- Queue exact, already closed immutable inputs at the original replay site.
Construction's raw/type/scope/frozen checks remain eager. -/
private def queueReplay (obligations : IO.Ref (Array ReplayObligation))
    (value type : Expr) : MetaM Unit := do
  unless closed value && closed type do throwError "child projection: open replay input"
  obligations.modify (·.push { value, type })

/-- The injected replay action is private and used only by the eager/deferred
adapters and focused instrumentation tests. Production always supplies replay. -/
private def tryObservePartialWithReplay? (replayCheck : Expr → Expr → MetaM Unit)
    (state : State) (selected : MVarId) (profile : Profile) (originalContract : Expr)
    (observations : Array Observation) (check : MetaM Unit := Core.checkInterrupted)
    (limits : Limits := {}) : MetaM (Option ObservationReport) :=
  tryCatchRuntimeEx (do
    let obligations ← IO.mkRef (#[] : Array ReplayObligation)
    withPartialViewWithReplay (queueReplay obligations) state selected (fun view => do
      let discharge : MetaM Unit := do
        for obligation in ← obligations.get do
          check
          replayCheck obligation.value obligation.type
          check
      -- Queue evidence replays too: a decider-only policy refusal must not
      -- perform any independent replay or leak a provisional report.
      let report ← observeViewWithReplay (queueReplay obligations) discharge view profile originalContract observations check
      -- No provisional status report or expression is exposed on inconclusive
      -- paths. The observer returns some only after every check has succeeded.
      return if report.refuted then some report else none) check limits) fun exception =>
    match exception with
    | .internal .. => throw exception
    | .error .. =>
      if exception.isInterrupt || exception.isRuntime || exception.isMaxHeartbeat || exception.isMaxRecDepth then
        throw exception
      else return none

/-- Observer-only deferred validation. Unchanged native construction first
produces a typed frozen view inside full Core/Meta isolation. A raw false must
pass the full original contract, predicate and supplied-decider policy checks
and every original completed-closure, native-node, program and evidence replay,
before it can escape as a refutation. Other results expose no provisional View
or report. Ordinary unsupported errors return none; all internal/resource
exceptions propagate with their identity after restoration. No cache. -/
def tryObservePartial? (state : State) (selected : MVarId) (profile : Profile)
    (originalContract : Expr) (observations : Array Observation)
    (check : MetaM Unit := Core.checkInterrupted) (limits : Limits := {}) :
    MetaM (Option ObservationReport) :=
  tryObservePartialWithReplay? replay state selected profile originalContract observations check limits

structure Result where
  enhanced : Bool
  report : ObservationReport

/-- Ordinary unsupported extraction preserves whole-hole opacity. Internal and
resource exceptions propagate through both paths with their original identity. -/
def observe (state : State) (selected : MVarId) (profile : Profile) (originalContract : Expr)
    (observations : Array Observation) (check : MetaM Unit := Core.checkInterrupted)
    (limits : Limits := {}) : MetaM Result := do
  if let some report ← tryPartialView state selected
      (fun view => observeView view profile originalContract observations check) check limits then
    return { enhanced := true, report }
  let report ← Projection.observe state.base profile originalContract observations check
  return { enhanced := false, report }

/-- Cheap eligibility inspection for the optional descendant hook. This reads
raw assignment edges only; it never expands or assigns a metavariable. The
subsequent typed projection independently checks the complete selected graph.
Syntax work is capped across the at most four original roots, with a separate
node cap for each root. -/
private structure SelectionInventory where
  visited : Array MVarId := #[]
  syntaxNodes : Nat := 0
  productive : Bool := false

private partial def selectionEdges (ref : IO.Ref SelectionInventory) (limits : Limits)
    (check : MetaM Unit) (value : Expr) : MetaM (Array MVarId) := do
  check
  if (← ref.get).syntaxNodes ≥ limits.syntaxNodes then
    throwError "child projection: selection syntax quota"
  ref.modify fun current => { current with syntaxNodes := current.syntaxNodes + 1 }
  match value with
  | .mvar id => return #[id]
  | .app function argument =>
    -- Native introductions use metavariable-headed closure applications. A
    -- chosen local or constant application exposes actual body structure.
    if function.getAppFn.isFVar || function.getAppFn.isConst then
      ref.modify fun current => { current with productive := true }
    return (← selectionEdges ref limits check function) ++
      (← selectionEdges ref limits check argument)
  | .lam _ _ body _ => selectionEdges ref limits check body
  | .proj _ _ body =>
    ref.modify fun current => { current with productive := true }
    selectionEdges ref limits check body
  | .mdata _ body => selectionEdges ref limits check body
  -- These shapes are not part of the admitted computational body fragment.
  -- Their omission only disables optional pruning; ordinary search continues.
  | .forallE .. | .letE .. => return #[]
  | _ => return #[]

private partial def reachesChild (ref : IO.Ref SelectionInventory) (limits : Limits)
    (check : MetaM Unit) (depth : Nat) (child current : MVarId) : MetaM Bool := do
  check
  if current == child then return true
  if (← ref.get).visited.contains current then return false
  if (← ref.get).visited.size ≥ limits.nodes then
    throwError "child projection: selection graph quota"
  ref.modify fun state => { state with visited := state.visited.push current }
  unless (← current.getDecl).depth == depth do return false
  let regular ← getExprMVarAssignment? current
  let delayed ← getDelayedMVarAssignment? current
  if regular.isSome && delayed.isSome then return false
  if let some value := regular then
    for next in ← selectionEdges ref limits check value do
      if ← reachesChild ref limits check depth child next then return true
  else if let some link := delayed then
    return ← reachesChild ref limits check depth child link.mvarIdPending
  return false

/-- Select one original owned ancestor of a fresh pending search child. Pure
introductions are deliberately ineligible: their unknown body adds no useful
fixed application to the ordinary whole-hole view. Refusal here means only
that this optional pruning attempt is skipped. No selection survives a branch.
-/
def selectAncestor? (state : State) (child : MVarId)
    (check : MetaM Unit := Core.checkInterrupted) (limits : Limits := {}) :
    MetaM (Option MVarId) := isolated do
  requireDepth state
  check
  if state.beforeSearch.decls.contains child || (← child.isAssigned) ||
      (← child.isDelayedAssigned) then return none
  let declaration ← child.getDecl
  -- Native `apply` returns ordinary unification goals. They are eligible only
  -- through the same fresh-identity, depth and ancestry checks as opaque ones;
  -- the full extractor subsequently requires independent frozen data types.
  unless declaration.depth == state.base.prepared.depth &&
      admissibleChildKind declaration.kind do return none
  let ref ← IO.mkRef ({} : SelectionInventory)
  for owned in state.base.prepared.holes do
    -- Clear graph membership for each root so a shared child is still reached
    -- from a later ancestor. Keep the total syntax-work limit across roots.
    ref.modify fun current => { current with visited := #[], productive := false }
    let reached ← reachesChild ref limits check state.base.prepared.depth child owned.pending
    if reached && (← ref.get).productive then return some owned.pending
  return none

end Leant2.Frontend.Sketch.ChildProjection
