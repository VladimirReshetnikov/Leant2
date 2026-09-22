import Lean
import Leant2.Core.Types
import Leant2.Native.Transaction
import Leant2.Native.Export
import Leant2.Search.Core
import Leant2.Accept.Gate
/-!
# The engine: a frozen query in, an outcome out

Runs the lanes under one adaptive budget, with no user settings
(Decision 1.1): a cheap constructive pass, a cheap refutation pass, deeper
constructive search, the classical lane (also at the `Prop` instantiation of
the query's universe parameters), and a deeper refutation pass.
-/
namespace Leant2

open Lean Meta Elab

/-- A closed target type and an optional contract `fun (f : T) => P f`.
The lower-level `runQuery` also supports the command frontend's unresolved
universe placeholders. The public `synthesize` API requires frozen input. -/
structure Query where
  target : Expr
  contract : Option Expr := none
  profile : Profile := .standard
  providers : Array Name := #[]
  /-- Cooperative search/lane budget in milliseconds, not a hard wall-clock
  timeout for the whole call, including preparation, proof checks, and ranking. -/
  budgetMs : Nat := 20000
  maxCandidates : Nat := 12
  /-- After the first accepted candidate, keep enumerating for this long. -/
  graceMs : Nat := 400

/-- The default type frontier for `Sort`-valued holes. -/
def defaultTypeFrontier : MetaM (Array Expr) := do
  return #[mkConst ``Unit, mkConst ``Empty, mkConst ``Bool, mkConst ``Nat,
           mkConst ``True, mkConst ``False]

private def runSearch (ctx : SearchCtx) (act : SearchM α) : MetaM α :=
  act.run ctx

/-- The real root and pending obligations for one enumeration pass. The root
may already contain a partial program, so its pending goals are explicit.
This is an internal live-state descriptor, not a portable query or result. -/
structure EnumerationSeed where
  root : MVarId
  goals : List Goal

/-- Enumerate initialized passes in the supplied depth order. Initialization
runs before the branch transaction: malformed input is not ordinary search
failure. The caller owns seed lifetime and any full state restoration; the
leaf receives the whole instantiated root before such restoration occurs.

The initializer and acceptance callback share the existing SearchCtx, so work
charges and accepted-result IO storage are not rolled back. A returned true
retains its existing stop semantics; no new quota check or exception boundary
is introduced here. -/
def enumerateInitialized (ctx : SearchCtx) (cfg : SearchConfig)
    (initializeSeed : Nat → SearchM EnumerationSeed)
    (accept : Expr → SearchM Bool) (productive : SearchM Bool) (depths : List Nat)
    (completed : IO.Ref Nat) : MetaM Unit := do
  runSearch ctx do
    for depth in depths do
      let seed ← initializeSeed depth
      let root := mkMVar seed.root
      let leaf : Leaf := do
        let e ← instantiateMVars root
        if e.hasExprMVar then return false
        if leant2.traceNodes.get (← getOptions) then
          IO.println s!"[leant2]     leaf {← ppExpr e}"
        accept e
      let cfg := { cfg with maxDepth := depth, root := some seed.root }
      let t0 ← IO.monoMsNow
      let _ ← alternative (search cfg leaf cfg.maxSplits seed.goals)
      -- a depth counts as completed only if the pass returned (not interrupted)
      completed.modify (· + 1)
      if leant2.trace.get (← getOptions) then
        IO.println s!"[leant2]   depth {depth} done in {(← IO.monoMsNow) - t0} ms"

      if ← productive then break

/-- Enumerate candidates for `goalTy` by iterative deepening, passing each
closed candidate to `accept`, which returns `true` to stop. Deepening stops
after the first depth that produced a candidate (`productive` reports it).
The ordinary initializer retains the original goal order and permissions. -/
def enumerate (ctx : SearchCtx) (cfg : SearchConfig) (goalTy : Expr)
    (accept : Expr → SearchM Bool) (productive : SearchM Bool) (depths : List Nat)
    (completed : IO.Ref Nat) : MetaM Unit :=
  enumerateInitialized ctx cfg (fun depth => do
    let root ← mkFreshExprMVar goalTy
    return {
      root := root.mvarId!
      goals := [{ mvar := root.mvarId!, depth, allowExtendedRecursion := true }] })
    accept productive depths completed

private def printLaneProfile (profile : Option Profiling.Collector)
    (before : Profiling.Snapshot) : MetaM Unit := do
  let some collector := profile | return
  let spans := (← collector.snapshot).delta before
  unless spans.valid do
    IO.println "[leant2]   span times unavailable: invalid clock or span nesting"
    return
  let rows := spans.entries.map fun e =>
    (e.label, e.inclusiveNs / 1000000, e.exclusiveNs / 1000000, e.returned, e.exceptional)
  IO.println s!"[leant2]   span times (inclusive/exclusive ms; returned/exception exits): {rows}"
  IO.println "[leant2]   lane.search is the search root; its exclusive time includes unlabelled search and profiling overhead, not query setup or ranking"

/-- Run `act` with a fresh lane deadline. Restore state on every exceptional
exit. Only explicit lane/resource limits are consumed; native user interrupts
and unrelated errors propagate after restoration. Span reports cover the action
and its children; the existing lane wall time also includes setup/restoration.
Ledger values in the header remain query-cumulative. -/
def withLane (ledger : IO.Ref Ledger) (refutedPrograms : IO.Ref (Std.HashSet Expr))
    (graceDeadline : IO.Ref (Option Nat))
    (timedOut : IO.Ref Bool) (ms : Nat)
    (act : SearchCtx → MetaM Unit) (name : String := "lane")
    (profile : Option Profiling.Collector := none) : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let trace := leant2.trace.get (← getOptions)
  -- runQuery supplies its collector. Direct traced lanes get their own fresh
  -- collector; ordinary lanes allocate and inspect no profiling state.
  let profile ← if trace then
      match profile with
      | some collector => pure (some collector)
      | none => some <$> Profiling.Collector.create
    else pure none
  let before ← match profile with
    | some collector => collector.snapshot
    | none => pure {}
  let observationCache ← IO.mkRef #[]
  let observationReport ← IO.mkRef {}
  let ctx : SearchCtx := {
    ledger, profile, deadline := some (t0 + ms), refutedPrograms
    observationCache, observationReport, graceDeadline }
  let saved : Meta.SavedState ← Meta.saveState
  -- This narrow boundary must see native interrupts to restore before
  -- rethrowing them; ordinary Core.tryCatch deliberately skips them.
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try
    Profiling.span profile "lane.search" (act ctx)
    if trace then
      let l ← ledger.get
      IO.println s!"[leant2] {name}: finished in {(← IO.monoMsNow) - t0} ms (share {ms} ms) rules {l.ruleApplications} unif {l.unifications} proofs {l.proofAttempts} cands {l.candidates}"
      printLaneProfile profile before
  catch e =>
    saved.restore
    if let some reason := searchStop? e then
      if reason != .grace then timedOut.set true
      if trace then
        let l ← ledger.get
        IO.println s!"[leant2] {name}: stopped ({repr reason}) after {(← IO.monoMsNow) - t0} ms (share {ms} ms) rules {l.ruleApplications} unif {l.unifications} proofs {l.proofAttempts} cands {l.candidates}"
        printLaneProfile profile before
    else throw e

/-- Propose the classical lane's `Prop` universe specialization. Existing
assignments are instantiated first; only remaining universe metavariables and
parameters become zero. Successors and other level structure are preserved,
so an assigned `Type` universe is never lowered to `Prop`. This does not assign
the original query's metavariables. Pending universe equations conservatively
disable this specialization until their constraints have been resolved.

The result is a specialized candidate type, not a proof of the original
universe-polymorphic query; acceptance records and checks this exact type. -/
def atProp? (e : Expr) : MetaM (Option Expr) := do
  unless (← getPostponed).isEmpty do return none
  let e ← instantiateMVars e
  let lps := (collectLevelParams {} e).params.toList
  return some <| replaceExprLevelMVars (fun _ => Level.zero)
    (e.instantiateLevelParams lps (lps.map fun _ => Level.zero))

/-- A cheap cost vector for ranking accepted candidates (Section 6.4):
inputs left unused by the outermost lambdas, eliminator uses, and size.
Lower is better. -/
def candidateCost (e : Expr) : Nat × Nat × Nat := Id.run do
  -- unused outermost binders
  let mut unused := 0
  let mut body := e
  let mut i := 0
  while body.isLambda do
    let b := body.bindingBody!
    -- instance binders are evidence, not inputs: leaving one unused is not a defect
    if !b.hasLooseBVar 0 && !body.bindingInfo!.isInstImplicit then unused := unused + 1
    body := b
    i := i + 1
  -- eliminators and size
  let mut elims := 0
  let mut size := 0
  let mut stack := [e]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | x :: rest =>
      stack := rest
      size := size + 1
      match x with
      | .const n _ =>
        let s := n.toString
        if s.endsWith ".casesOn" || s.endsWith ".rec" || s.endsWith ".elim" then elims := elims + 1
      | .app f a => stack := f :: a :: stack
      | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
      | .letE _ t v b _ => stack := t :: v :: b :: stack
      | .mdata _ b | .proj _ _ b => stack := b :: stack
      | _ => pure ()
  return (unused, elims, size)

/-- Sort candidates by cost and drop those that print identically. -/
def rankCandidates (cands : Array Accepted) : MetaM (Array Accepted) := do
  let mut keyed : Array (Nat × Nat × Nat × String × Accepted) := #[]
  for c in cands do
    let (u, el, sz) := candidateCost c.program
    let s := toString (← ppExpr c.program)
    keyed := keyed.push (u, el, sz, s, c)
  let sorted := keyed.qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2.1 < b.2.2.1)))
  let mut out : Array Accepted := #[]
  let mut seenStr : Array String := #[]
  for (_, _, _, s, c) in sorted do
    if seenStr.contains s then continue
    seenStr := seenStr.push s
    out := out.push c
  return out

private initialize refutationExportLimitExceptionId : InternalExceptionId ←
  registerInternalExceptionId `leant2RefutationExportLimit

/-- Refutation workers may create declarations and mutate native caches. A
complete snapshot also prevents such changes escaping successful extraction. -/
private def restoringRefutation (action : MetaM α) : MetaM α := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  try action finally
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

/-- Preserve axiom-free contradictions before simplification constructs
propositional equalities. Failed assumption probes cannot affect the portfolio. -/
private def proveContractNegation (goal : MVarId) : MetaM Bool := do
  let proof? ← restoringRefutation do
    forallTelescopeReducing (← goal.getType) fun xs target => do
      for x in xs.reverse do
        if ← isDefEq (← inferType x) target then
          return some (← mkLambdaFVars xs x)
      return none
  if let some proof := proof? then
    goal.assign proof
    return true
  tacticProve goal

/-- Try one bounded upfront refutation, returning a portable certificate under
the query's policy. Remaining universe placeholders are generalized once to
rigid parameters before proving the exact negative statement; expression holes
and unresolved universe equations are conservatively refused.

The proof callback is an internal testing seam. All speculative state is
restored, including on success, while the one proof-attempt charge survives.
Only new theorem bodies are exported, with a shared finite expansion bound;
the authoritative gate runs afterward in the original environment. -/
def tryRefuteContract? (q : Query) (ledger : IO.Ref Ledger)
    (prove : MVarId → MetaM Bool := proveContractNegation) : MetaM (Option Accepted) := do
  let some contract := q.contract | return none
  Core.checkInterrupted
  -- withNewMCtxDepth clears postponed equations, so inspect the caller's
  -- constraints before entering that scope rather than silently dropping them.
  unless (← getPostponed).isEmpty do return none
  restoringRefutation <| withNewMCtxDepth <| withCurrHeartbeats do
    withTheReader Core.Context (fun context => { context with maxHeartbeats := 20000 * 1000 }) do
    tryCatchRuntimeEx (do
      Core.checkInterrupted
      let negative ← withLocalDecl `f .default q.target fun f =>
        -- Preserve the original statement's syntax for its axiom audit:
        -- beta reduction could erase dependencies in the contract's domain.
        mkForallFVars #[f] (mkApp (mkConst ``Not) (mkApp contract f))
      let negative ← instantiateMVars negative
      if negative.hasExprMVar || negative.hasFVar || negative.hasLooseBVars || negative.hasSorry then
        return none
      let ([negative], levels) ← generalizeLevels [negative] | return none
      check negative
      unless ← isProp negative do return none
      let checkResources : MetaM Unit := do
        Core.checkInterrupted
        checkSystem "leant2.contractRefutation"
      checkResources
      ledger.modify fun work => { work with proofAttempts := work.proofAttempts + 1 }
      let original ← getEnv
      let proof? ← restoringRefutation do
        let goal ← mkFreshExprMVar negative .syntheticOpaque
        modifyThe Core.State fun state => { state with messages := {} }
        let success ← prove goal.mvarId!
        checkResources
        unless success && (← goal.mvarId!.isAssignedOrDelayedAssigned) do return none
        if (← getThe Core.State).messages.hasErrors then return none
        let proof ← instantiateMVars goal
        let remaining ← IO.mkRef 64
        let proof ← Native.inlineNewTheorems original (← getEnv) remaining checkResources
          (.internal refutationExportLimitExceptionId) proof
        if proof.hasExprMVar || proof.hasLevelMVar || proof.hasFVar ||
            proof.hasLooseBVars || proof.hasSorry then return none
        unless (collectLevelParams {} proof).params.toList.all levels.contains do return none
        return some proof
      let some proof := proof? | return none
      checkResources
      -- `negative` is the same frozen statement used by the worker. Rebuilding
      -- it from raw level placeholders here could change the certificate.
      let accepted ← gate q.profile proof negative none
      checkResources
      return match accepted with | .ok certificate => some certificate | .error _ => none)
      (fun ex => do
        Core.checkInterrupted
        if ex.isMaxHeartbeat || ex.isMaxRecDepth then return none
        if let .internal id _ := ex then
          if id == refutationExportLimitExceptionId then return none
        if isInterrupt ex then throw ex
        return none)

/-- Run the whole pipeline for one query. -/
def runQuery (q : Query) : MetaM Outcome :=
  -- heartbeats are replaced by the wall-clock deadline of each lane
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let ledger ← IO.mkRef ({} : Ledger)
  let refutedPrograms ← IO.mkRef ({} : Std.HashSet Expr)
  let spanProfile ← if leant2.trace.get (← getOptions) then
      some <$> Profiling.Collector.create
    else pure none
  let start ← IO.monoMsNow
  let frontier ← defaultTypeFrontier
  let providers ← mkProviders q.providers
  let residual ← match q.contract with
    | some c => mkResidual c q.target
    | none => pure #[]
  let observations ← match q.contract with
    | some c => mkObservations c q.target
    | none => pure #[]
  let skip := ((leant2.skipRules.get (← getOptions)).splitOn ",").map
    (fun part => part.trimAscii.toString) |>.filter (· != "")
  let pruningEvidenceCache ← IO.mkRef none
  let baseCfg : SearchConfig := { providers, profile := q.profile,
                                  pruningEvidenceCache := some pruningEvidenceCache,
                                  typeFrontier := frontier, recursionFirst := q.contract.isSome,
                                  contract := q.contract, residual, observations, skip }
  let found ← IO.mkRef (#[] : Array Accepted)
  let seen ← IO.mkRef (#[] : Array Expr)
  let firstFoundAt ← IO.mkRef (none : Option Nat)
  let graceRef ← IO.mkRef (none : Option Nat)
  let rejectedCount ← IO.mkRef 0
  -- the target actually searched (possibly universe-instantiated) and its subtype form
  let mkGoal (target : Expr) (c? : Option Expr) : MetaM Expr := match c? with
    | none => pure target
    | some c => mkAppM ``Subtype #[c]
  let accept (target : Expr) (contract : Option Expr) (classicalLane : Bool) :
      Expr → SearchM Bool := fun e => do
    let (prog, proof?) ← match contract with
      | none => pure (e, none)
      | some c => do
        let v ← whnfR (← mkAppM ``Subtype.val #[e])
        let p ← mkAppM ``Subtype.property #[e]
        let pty ← instantiateMVars (mkApp c v)
        pure (v, some (p, pty))
    let progN ← instantiateMVars prog
    if (← seen.get).any (· == progN) then return false
    charge fun l => { l with candidates := l.candidates + 1 }
    match ← gate q.profile progN target proof? with
    | .ok acc =>
      -- A rejected proof does not reject every proof of this program's
      -- contract. Deduplicate only accepted programs so ordinary proof
      -- alternatives remain available after an axiom-profile rejection.
      seen.modify (·.push progN)
      -- classical only by evidence: the axiom inventory, not the lane
      let _ := classicalLane
      found.modify (·.push acc)
      if (← firstFoundAt.get).isNone then
        let now ← IO.monoMsNow
        firstFoundAt.set (some now)
        graceRef.set (some (now + q.graceMs))
      return (← found.get).size ≥ q.maxCandidates
    | .error _ =>
      rejectedCount.modify (· + 1)
      charge fun l => { l with rejected := l.rejected + 1 }
      return false
  let productive : SearchM Bool := do
    -- stop deepening once something was found; also stop the current pass after the grace period
    return !(← found.get).isEmpty
  let graceDeadline : MetaM (Option Nat) := do
    return (← firstFoundAt.get).map (· + q.graceMs)
  -- a lane whose deadline is shortened once the first candidate appears
  let enumerateGrace (ctx : SearchCtx) (cfg : SearchConfig) (goalTy : Expr)
      (acc : Expr → SearchM Bool) (depths : List Nat) (completed : IO.Ref Nat) : MetaM Unit := do
    let acc' : Expr → SearchM Bool := fun e => do
      if ← acc e then return true
      match ← graceDeadline with
      | some gd => return (← IO.monoMsNow) > gd
      | none => return false
    -- the deadline check inside the search also honors the grace period
    let ctx' := ctx
    let checkGrace : SearchM Bool := do
      match ← graceDeadline with
      | some gd => return (← IO.monoMsNow) > gd
      | none => return false
    enumerate ctx' cfg goalTy acc' (do return (← productive) || (← checkGrace)) depths completed
  let goalTy ← mkGoal q.target q.contract
  let timedOut ← IO.mkRef false
  -- refutation lane
  let refuted ← IO.mkRef (none : Option Accepted)
  let refutationLane (ms : Nat) (depths : List Nat) : MetaM Unit := withLane ledger refutedPrograms graceRef timedOut ms (name := "refutation") (profile := spanProfile) fun ctx => do
    let negTy ← mkArrow q.target (mkConst ``False)
    let extra ← mkProviders #[``Empty.elim, ``False.elim] (always := true)
    let cfgR := { baseCfg with
      providers := extra ++ baseCfg.providers
      profile := .strictConstructive }
    let dummy ← IO.mkRef 0
    enumerate ctx cfgR negTy (fun e => do
        match ← gate .strictConstructive e negTy none with
        | .ok acc => refuted.set (some acc); return true
        | .error _ => return false) (do return (← refuted.get).isSome) depths dummy
  -- classical reasoning needs `Prop` targets: a universe-polymorphic query with
  -- explicit universe parameters or unresolved level placeholders is searched
  -- at its `Prop` instantiation, preserving already fixed universe structure.
  let classicalLane (ms : Nat) (depths : List Nat) : MetaM Unit := withLane ledger refutedPrograms graceRef timedOut ms (name := "classical") (profile := spanProfile) fun ctx => do
    let some tp ← atProp? q.target | return ()
    let cP ← match q.contract with
      | none => pure none
      | some c => atProp? c
    if q.contract.isSome && cP.isNone then return ()
    let dummy ← IO.mkRef 0
    if tp != q.target || cP != q.contract then
      let goalP ← mkGoal tp cP
      let residualP ← match cP with
        | some c => mkResidual c tp
        | none => pure #[]
      let observationsP ← match cP with
        | some c => mkObservations c tp
        | none => pure #[]
      enumerateGrace ctx { baseCfg with
        classical := true, contract := cP, residual := residualP, observations := observationsP }
        goalP (accept tp cP true) depths dummy
    else
      enumerateGrace ctx { baseCfg with classical := true } goalTy
        (accept q.target q.contract true) depths dummy
  let nothingYet : MetaM Bool := do return (← found.get).isEmpty && (← refuted.get).isNone
  -- classical reasoning can only matter when the query mentions propositions
  -- (a `Prop` binder or a universe-flexible sort); data queries skip those lanes
  let needsClassical := (q.target.find? fun e => match e with
    | .sort .zero => true
    | .sort (.mvar _) => true
    | _ => false).isSome
  let deadline := start + q.budgetMs
  let remaining : MetaM Nat := do return deadline - (min deadline (← IO.monoMsNow))
  -- 0. a contract no program can satisfy (`where False`, `... ∧ False`): its
  -- negation is proved once, for every program, before any search
  if let some certificate ← tryRefuteContract? q ledger then
    return .negative .contractImpossible (some certificate) (← ledger.get)
  -- constructive depths; a later lane resumes at the first depth the earlier one did not finish
  let constructiveDepths := [2, 3, 4, 5, 6, 7, 9, 12]
  let completed ← IO.mkRef 0
  -- 1. cheap constructive pass (a larger share when no classical lane will run).
  -- Under a contract without classical lanes nothing else would run between
  -- the cheap and the deeper pass, so a single pass takes the whole budget
  -- rather than cutting a depth and redoing it.
  let singlePass := !needsClassical && q.contract.isSome
  withLane ledger refutedPrograms graceRef timedOut
      (if singlePass then q.budgetMs else if needsClassical then q.budgetMs * 3 / 20 else q.budgetMs * 3 / 10)
      (name := "constructive") (profile := spanProfile) fun ctx =>
    enumerateGrace ctx baseCfg goalTy (accept q.target q.contract false)
      (if singlePass then constructiveDepths else constructiveDepths.take 4) completed
  -- 2. cheap refutation pass, only for type-only queries
  if (← nothingYet) && q.contract.isNone then refutationLane (q.budgetMs / 10) [4, 6]
  -- 3. cheap classical pass (shallow first: classical splits branch quickly)
  if (← nothingYet) && needsClassical then classicalLane (q.budgetMs * 3 / 10) [3, 4, 5, 6]
  -- 4. deeper constructive search: most of what remains when classical lanes are skipped
  if ← nothingYet then
    let rem ← remaining
    let share := if needsClassical then rem * 3 / 10 else rem * 4 / 5
    let done ← completed.get
    withLane ledger refutedPrograms graceRef timedOut share (name := "constructive-deeper") (profile := spanProfile) fun ctx =>
      enumerateGrace ctx baseCfg goalTy (accept q.target q.contract false)
        (constructiveDepths.drop done) completed
  -- 5. deeper classical search
  if (← nothingYet) && needsClassical then classicalLane ((← remaining) * 2 / 3) [8, 10]
  -- 6. deeper refutation
  if (← nothingYet) && q.contract.isNone then refutationLane (← remaining) [8]
  let cands ← found.get
  let l ← ledger.get
  if !cands.isEmpty then return .verified (← rankCandidates cands) l
  if let some cert ← refuted.get then return .negative .impossible (some cert) l
  -- programs of the right type existed but none passed the contract (gate
  -- rejections and contract refutations of closed programs)
  -- (both are charged to the ledger's `rejected` counter)
  if l.rejected > 0 && q.contract.isSome then
    return .refutedAll l.rejected l
  return .negative (if ← timedOut.get then .budgetExhausted else .grammarExhausted) none l

end Leant2
