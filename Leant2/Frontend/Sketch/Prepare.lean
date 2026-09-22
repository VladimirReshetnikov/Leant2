import Lean

/-!
Preparation of explicit sketch holes in an isolated native metavariable context.
Named holes are owned by this invocation; native closure wrappers are inspected
without expanding them into assignable expressions. The consumer runs at the
same metavariable depth, and complete Core/Meta/Term state is restored afterward.
Search, acceptance, and result publication belong to the caller.
-/

namespace Leant2.Frontend.Sketch

open Lean Meta Elab
open Lean.Elab.Term hiding mkConst

structure HoleSpec where
  sourceName : Name
  internalName : Name
  source : Syntax

structure OwnedHole where
  spec : HoleSpec
  pending : MVarId
  declaration : MetavarDecl

structure Wrapper where
  outer : MVarId
  pending : MVarId
  arguments : Array Expr

/-- Valid only during `withPreparedSketch`'s consumer callback. The mctx and
its depth belong to that dynamic scope; callers must not retain this object. -/
structure Prepared where
  expected : Expr
  expression : Expr
  depth : Nat
  holes : Array OwnedHole
  wrappers : Array Wrapper

/-- Deliberately contains no Expr, MVarId, LocalContext, or saved state that
would become invalid when the preparation scope exits. -/
structure HoleReport where
  sourceName : Name
  depth : Nat
  locals : Nat
  deriving Repr

structure Report where
  depth : Nat
  holes : Array HoleReport
  delayedWrappers : Nat
  unresolvedBeforeConsumer : Nat
  deriving Repr

private def frozen (expression : Expr) : Bool :=
  !expression.hasExprMVar && !expression.hasLevelMVar &&
  !expression.hasLooseBVars && !expression.hasSorry

private def rawMVars (expression : Expr) : Array MVarId :=
  (expression.collectMVars {}).result

/-- Rewrite only explicit native named-hole syntax. The full native elaborator
still infers each hole's type and creates its local context. No global registry
or userName-based reuse of the caller's holes is permitted. -/
private partial def rewriteHoles (stx : Syntax) :
    StateRefT (Array HoleSpec) TermElabM Syntax := do
  if stx.isOfKind ``Lean.Parser.Term.syntheticHole then
    let identifier := stx[1]
    unless identifier.isIdent do
      throwErrorAt stx "leant2 sketch: preparation failed: only explicitly named program holes are supported"
    let sourceName := identifier.getId
    if (← get).any (·.sourceName == sourceName) then
      throwErrorAt stx "leant2 sketch: preparation failed: duplicate sketch-hole label {sourceName}"
    if (← get).size ≥ 4 then
      throwErrorAt stx "leant2 sketch: preparation failed: at most four program holes are supported"
    let mut internalName ← mkFreshUserName `sketchHole
    while ((← getMCtx).findUserName? internalName).isSome do
      internalName ← mkFreshUserName `sketchHole
    modify (·.push { sourceName, internalName, source := stx })
    return stx.setArg 1 (mkIdentFrom identifier internalName)
  if stx.isOfKind ``Lean.Parser.Term.hole then
    throwErrorAt stx "leant2 sketch: preparation failed: anonymous inference holes are not program holes"
  match stx with
  | .node info kind arguments =>
    return .node info kind (← arguments.mapM rewriteHoles)
  | other => return other

private def inspectOwned (before : MetavarContext) (depth : Nat)
    (specs : Array HoleSpec) : TermElabM (Array OwnedHole) := do
  let mut holes := #[]
  for spec in specs do
    let some pending := (← getMCtx).findUserName? spec.internalName
      | throwErrorAt spec.source "leant2 sketch: preparation failed: native elaboration did not register the owned hole"
    if before.decls.contains pending then
      throwErrorAt spec.source "leant2 sketch: preparation failed: caller metavariable captured by a sketch hole"
    let declaration ← pending.getDecl
    unless declaration.userName == spec.internalName && declaration.depth == depth do
      throwErrorAt spec.source "leant2 sketch: preparation failed: hole ownership or metavariable depth changed"
    unless declaration.kind.isSyntheticOpaque do
      throwErrorAt spec.source "leant2 sketch: preparation failed: program hole is not synthetic opaque"
    if (← pending.isAssigned) || (← pending.isDelayedAssigned) then
      throwErrorAt spec.source "leant2 sketch: preparation failed: expected an unassigned owned pending goal"
    pending.withContext do
      let type ← instantiateMVars declaration.type
      unless frozen type do
        throwErrorAt spec.source "leant2 sketch: preparation failed: hole type has unresolved dependencies"
      check type
      unless (← whnf (← inferType type)).isSort do
        throwErrorAt spec.source "leant2 sketch: preparation failed: owned goal declaration does not contain a type"
      let unsupported ← forallTelescopeReducing type fun _ result => do
        return (← whnf result).isSort || (← isClass? result).isSome
      if unsupported then
        throwErrorAt spec.source "leant2 sketch: preparation failed: type, motive, and dictionary holes are unsupported"
      for localDecl in declaration.lctx do
        let type ← instantiateMVars localDecl.type
        unless frozen type do
          throwErrorAt spec.source "leant2 sketch: preparation failed: hole-local type has unresolved dependencies"
        -- Inspect hidden have-values only for unfinished syntax. They stay
        -- opaque: native transformations may leave such values ill-typed, so
        -- do not type-check, unfold, or use them as definitional evidence.
        if let some value := localDecl.value? (allowNondep := true) then
          let value ← instantiateMVars value
          unless frozen value do
            throwErrorAt spec.source "leant2 sketch: preparation failed: hole-local value has unresolved dependencies"
    holes := holes.push { spec, pending, declaration }
  return holes

/-- Inspect native delayed links without expanding them into an assignable
term. Every unresolved leaf must be one registered pending goal. Only fresh
same-depth delayed wrappers may lead to those goals. The finite inspection cap
is a preparation bound, not a synthesis budget or completeness claim. -/
private def inspectGraph (before : MetavarContext) (depth : Nat)
    (expression : Expr) (holes : Array OwnedHole) : MetaM (Array Wrapper × Nat) := do
  let expression ← instantiateMVars expression
  let mut queue := rawMVars expression
  let mut seen : Array MVarId := #[]
  let mut wrappers : Array Wrapper := #[]
  let mut cursor := 0
  while cursor < queue.size do
    if seen.size ≥ 256 then throwError "leant2 sketch: preparation failed: closure-inspection limit reached"
    let current := queue[cursor]!
    cursor := cursor + 1
    if seen.contains current then continue
    seen := seen.push current
    if before.decls.contains current then
      throwError "leant2 sketch: preparation failed: unresolved caller metavariable occurs in the sketch graph"
    let declaration ← current.getDecl
    unless declaration.depth == depth do
      throwError "leant2 sketch: preparation failed: sketch graph crossed its owned metavariable depth"
    if let some delayed ← getDelayedMVarAssignment? current then
      let pendingDecl ← delayed.mvarIdPending.getDecl
      for argument in delayed.fvars do
        let .fvar id := argument
          | throwError "leant2 sketch: preparation failed: delayed closure argument is not a native free variable"
        unless (pendingDecl.lctx.find? id).isSome do
          throwError "leant2 sketch: preparation failed: delayed closure argument escaped its pending context"
      wrappers := wrappers.push {
        outer := current, pending := delayed.mvarIdPending, arguments := delayed.fvars }
      queue := queue.push delayed.mvarIdPending
    else if ← current.isAssigned then
      queue := queue ++ rawMVars (← instantiateMVars (mkMVar current))
    else unless holes.any (·.pending == current) do
      throwError "leant2 sketch: preparation failed: unregistered inference/program metavariable remains"
  for hole in holes do
    unless seen.contains hole.pending do
      throwErrorAt hole.spec.source "leant2 sketch: preparation failed: registered hole is not reachable from the sketch"
  -- Each delayed wrapper has one outgoing pending edge. An unfinished cycle
  -- is not justified just because another root component reaches an owned hole.
  for start in wrappers do
    let mut path : Array MVarId := #[]
    let mut current := start.outer
    while true do
      if path.contains current then throwError "leant2 sketch: preparation failed: cyclic delayed closure graph"
      path := path.push current
      let some next := wrappers.find? (·.outer == current) | break
      current := next.pending
  return (wrappers, seen.size)

private def errors : TermElabM Nat := do
  return ((← getThe Core.State).messages.toList.filter (·.severity == .error)).length

/-- Native elaboration can erase an unused subterm while retaining its error
obligation. Inspect the fresh invocation's registered expression obligations,
including their assigned/delayed dependencies, rather than every private
metavariable created by the elaborator. Only owned pending goals may remain. -/
private def inspectErrorObligations (holes : Array OwnedHole) : TermElabM Unit := do
  for info in (← getThe Term.State).mvarErrorInfos do
    for pending in (← getMVarsNoDelayed (mkMVar info.mvarId)) do
      unless holes.any (·.pending == pending) do
        throwErrorAt info.ref "leant2 sketch: preparation failed: unregistered native hole or inference obligation remains"

/-- Elaborate a closed sketch and expose its owned pending goals to an internal
controller at the same metavariable depth. Compatible macro occurrences may
share one registered goal. The complete state is restored even when the
consumer assigns holes, runs search, or raises an exception.

Unresolved native expression-error obligations are checked even when their
subterms were erased. This is not an inventory of private elaborator state.
Only the inert report escapes through this return value. The consumer must
export and validate any result before returning; retaining the live graph in
external mutable state is unsupported. This function performs no search or
acceptance check. -/
def withPreparedSketch (expected : Expr) (stx : TSyntax `term)
    (consume : Prepared → TermElabM Unit := fun _ => pure ()) : TermElabM Report := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  let termState ← getThe Term.State
  try
    Core.checkInterrupted
    -- withNewMCtxDepth clears postponed equations; inspect first.
    unless (← getPostponed).isEmpty do
      throwError "leant2 sketch: preparation failed: caller has pending universe equations"
    let expected ← instantiateMVars expected
    unless frozen expected && !expected.hasFVar do
      throwError "leant2 sketch: preparation failed: expected type must be closed and frozen"
    withNewMCtxDepth do
      let ownedDepth := (← getMCtx).depth
      let before ← getMCtx
      let errorCount ← errors
      withLCtx {} #[] do
        check expected
        unless (← whnf (← inferType expected)).isSort do
          throwError "leant2 sketch: preparation failed: expected expression must be a well-formed type"
      -- Do not drain the caller's synthetic task queue while elaborating this
      -- isolated expression. Native error records are likewise invocation-local
      -- so the later completeness check cannot consume/refuse caller holes.
      -- The outer finalizer restores all three original collections.
      modifyThe Term.State fun state => { state with
        pendingMVars := [], syntheticMVars := {}, mvarErrorInfos := [] }
      let (stx, specs) ← (rewriteHoles stx).run #[]
      let expression ← withLCtx {} #[] <| withoutErrToSorry do
        let expression ← elabTermEnsuringType stx expected
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars expression
      unless (← errors) == errorCount do
        throwError "leant2 sketch: preparation failed: sketch elaboration emitted an error"
      if expression.hasLevelMVar || expression.hasFVar || expression.hasSorry || expression.hasLooseBVars then
        throwError "leant2 sketch: preparation failed: incomplete sketch elaboration"
      unless (← getPostponed).isEmpty do
        throwError "leant2 sketch: preparation failed: sketch elaboration left a postponed equation"
      unless (← getThe Term.State).letRecsToLift.length == termState.letRecsToLift.length do
        throwError "leant2 sketch: preparation failed: recursive lifting is unsupported"
      for pending in (← getThe Term.State).pendingMVars do
        unless ← pending.isAssigned do
          throwError "leant2 sketch: preparation failed: unfinished synthetic elaborator task"
      unless (← getEnv).constants.map₂.toList.map Prod.fst ==
          coreState.env.constants.map₂.toList.map Prod.fst do
        throwError "leant2 sketch: preparation failed: new declarations during elaboration are unsupported"
      let holes ← inspectOwned before ownedDepth specs
      let (wrappers, unresolvedBeforeConsumer) ← inspectGraph before ownedDepth expression holes
      inspectErrorObligations holes
      let prepared : Prepared := { expected, expression, depth := ownedDepth, holes, wrappers }
      unless (← getMCtx).depth == prepared.depth do
        throwError "leant2 sketch: preparation failed: preparation left its original owned depth"
      consume prepared
      unless (← getMCtx).depth == prepared.depth do
        throwError "leant2 sketch: preparation failed: consumer changed the owned depth"
      Core.checkInterrupted
      return {
        depth := ownedDepth
        holes := holes.map fun hole => {
          sourceName := hole.spec.sourceName
          depth := hole.declaration.depth
          locals := hole.declaration.lctx.foldl (fun count _ => count + 1) 0 }
        delayedWrappers := wrappers.size
        unresolvedBeforeConsumer }
  finally
    modifyThe Term.State fun _ => termState
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

end Leant2.Frontend.Sketch
