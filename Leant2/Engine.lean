import Lean
import Leant2.Core.Types
import Leant2.Native.Transaction
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

/-- A frozen query: a closed target type and an optional contract
`fun (f : T) => P f`. -/
structure Query where
  target : Expr
  contract : Option Expr := none
  profile : Profile := .standard
  providers : Array Name := #[]
  /-- Wall-clock budget in milliseconds. -/
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

/-- Enumerate candidates for `goalTy` by iterative deepening, passing each
closed candidate to `accept`, which returns `true` to stop. Deepening stops
after the first depth that produced a candidate (`productive` reports it). -/
def enumerate (ctx : SearchCtx) (cfg : SearchConfig) (goalTy : Expr)
    (accept : Expr → SearchM Bool) (productive : SearchM Bool) (depths : List Nat)
    (completed : IO.Ref Nat) : MetaM Unit := do
  runSearch ctx do
    for depth in depths do
      let root ← mkFreshExprMVar goalTy
      let leaf : Leaf := do
        let e ← instantiateMVars root
        if e.hasExprMVar then return false
        if leant2.traceNodes.get (← getOptions) then
          IO.println s!"[leant2]     leaf {← ppExpr e}"
        accept e
      let cfg := { cfg with maxDepth := depth, root := some root.mvarId! }
      let t0 ← IO.monoMsNow
      let _ ← alternative (search cfg leaf cfg.maxSplits [{ mvar := root.mvarId!, depth }])
      -- a depth counts as completed only if the pass returned (not interrupted)
      completed.modify (· + 1)
      if leant2.trace.get (← getOptions) then
        IO.println s!"[leant2]   depth {depth} done in {(← IO.monoMsNow) - t0} ms"

      if ← productive then break

/-- Run `act` with a fresh deadline `ms` from now. A lane that hits its
deadline records the fact in `timedOut`; other interrupts propagate. -/
private def lane (ledger : IO.Ref Ledger) (refutedPrograms : IO.Ref (Std.HashSet Expr))
    (graceDeadline : IO.Ref (Option Nat))
    (timedOut : IO.Ref Bool) (ms : Nat)
    (act : SearchCtx → MetaM Unit) (name : String := "lane") : MetaM Unit := do
  let t0 ← IO.monoMsNow
  let trace := leant2.trace.get (← getOptions)
  let residualBlockers ← IO.mkRef #[]
  let ctx : SearchCtx := { ledger, deadline := some (t0 + ms), refutedPrograms, residualBlockers, graceDeadline }
  try
    act ctx
    if trace then
      let l ← ledger.get
      IO.println s!"[leant2] {name}: finished in {(← IO.monoMsNow) - t0} ms (share {ms} ms) rules {l.ruleApplications} unif {l.unifications} proofs {l.proofAttempts} cands {l.candidates}"
      let prof ← profTimers.get
      IO.println s!"[leant2]   self times (ms): {prof.map fun (k, v) => (k, v / 1000000)}"
      profTimers.set #[]
  catch e =>
    if isInterrupt e then
      -- a cut by the grace period is not a budget timeout
      if (← graceDeadline.get).isNone then timedOut.set true
      if trace then
        let l ← ledger.get
        IO.println s!"[leant2] {name}: timed out after {(← IO.monoMsNow) - t0} ms (share {ms} ms) rules {l.ruleApplications} unif {l.unifications} proofs {l.proofAttempts} cands {l.candidates}"
      let prof ← profTimers.get
      IO.println s!"[leant2]   self times (ms): {prof.map fun (k, v) => (k, v / 1000000)}"
      profTimers.set #[]
    else throw e

/-- Instantiate every universe parameter of `e` with `Prop`. -/
private def atProp (e : Expr) : Expr :=
  let lps := (collectLevelParams {} e).params.toList
  e.instantiateLevelParams lps (lps.map fun _ => Level.zero)

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

/-- Run the whole pipeline for one query. -/
def runQuery (q : Query) : MetaM Outcome :=
  -- heartbeats are replaced by the wall-clock deadline of each lane
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let ledger ← IO.mkRef ({} : Ledger)
  let refutedPrograms ← IO.mkRef ({} : Std.HashSet Expr)
  let start ← IO.monoMsNow
  let frontier ← defaultTypeFrontier
  let providers ← mkProviders q.providers
  let residual ← match q.contract with
    | some c => mkResidual c q.target
    | none => pure #[]
  let baseCfg : SearchConfig := { providers, typeFrontier := frontier, recursionFirst := q.contract.isSome,
                                  contract := q.contract, residual }
  let found ← IO.mkRef (#[] : Array Accepted)
  let seen ← IO.mkRef (#[] : Array Expr)
  let firstFoundAt ← IO.mkRef (none : Option Nat)
  let graceRef ← IO.mkRef (none : Option Nat)
  let rejectedCount ← IO.mkRef 0
  -- the target actually searched (possibly universe-instantiated) and its subtype form
  let mkGoal (target : Expr) (c? : Option Expr) : MetaM Expr := match c? with
    | none => pure target
    | some c => mkAppM ``Subtype #[c]
  let accept (target : Expr) (classicalLane : Bool) : Expr → SearchM Bool := fun e => do
    let contract := q.contract.map fun c => if target == q.target then c else atProp c
    let (prog, proof?) ← match contract with
      | none => pure (e, none)
      | some c => do
        let v ← whnfR (← mkAppM ``Subtype.val #[e])
        let p ← mkAppM ``Subtype.property #[e]
        let pty ← instantiateMVars (mkApp c v)
        pure (v, some (p, pty))
    let progN ← instantiateMVars prog
    if (← seen.get).any (· == progN) then return false
    seen.modify (·.push progN)
    charge fun l => { l with candidates := l.candidates + 1 }
    match ← gate q.profile progN target proof? with
    | .ok acc =>
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
  let refutationLane (ms : Nat) (depths : List Nat) : MetaM Unit := lane ledger refutedPrograms graceRef timedOut ms (name := "refutation") fun ctx => do
    let negTy ← mkArrow q.target (mkConst ``False)
    let extra ← mkProviders #[``Empty.elim, ``False.elim] (always := true)
    let cfgR := { baseCfg with providers := extra ++ baseCfg.providers }
    let dummy ← IO.mkRef 0
    enumerate ctx cfgR negTy (fun e => do
        match ← gate .strictConstructive e negTy none with
        | .ok acc => refuted.set (some acc); return true
        | .error _ => return false) (do return (← refuted.get).isSome) depths dummy
  -- classical reasoning needs `Prop` targets: a universe-polymorphic query with
  -- explicit universe parameters is searched at its `Prop` instantiation
  let classicalLane (ms : Nat) (depths : List Nat) : MetaM Unit := lane ledger refutedPrograms graceRef timedOut ms (name := "classical") fun ctx => do
    let tp := atProp q.target
    let dummy ← IO.mkRef 0
    if tp != q.target then
      let cP := q.contract.map atProp
      let goalP ← mkGoal tp cP
      let residualP ← match cP with
        | some c => mkResidual c tp
        | none => pure #[]
      enumerateGrace ctx { baseCfg with classical := true, contract := cP, residual := residualP }
        goalP (accept tp true) depths dummy
    else
      enumerateGrace ctx { baseCfg with classical := true } goalTy (accept q.target true) depths dummy
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
  if let some c := q.contract then
    let negTy ← withLocalDecl `f .default q.target fun f => do
      mkForallFVars #[f] (mkApp (mkConst ``Not) (c.beta #[f]))
    -- bounded by heartbeats: this is a quick check, not a lane
    let proved ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 }) do
      tryCatchRuntimeEx (do
        let mv ← mkFreshExprMVar negTy
        let ok ← tacticProve mv.mvarId!
        let pf ← instantiateMVars mv
        if !ok || pf.hasMVar then return false
        match ← gate .standard pf negTy none with
        | .ok _ => return true
        | .error _ => return false)
        (fun e => do if e.isInterrupt then throw e else return false)
    if proved then
      return .negative .contractImpossible none (← ledger.get)
  -- constructive depths; a later lane resumes at the first depth the earlier one did not finish
  let constructiveDepths := [2, 3, 4, 5, 6, 7, 9, 12]
  let completed ← IO.mkRef 0
  -- 1. cheap constructive pass (a larger share when no classical lane will run)
  lane ledger refutedPrograms graceRef timedOut (if needsClassical then q.budgetMs * 3 / 20 else q.budgetMs * 3 / 10) (name := "constructive") fun ctx =>
    enumerateGrace ctx baseCfg goalTy (accept q.target false) (constructiveDepths.take 4) completed
  -- 2. cheap refutation pass, only for type-only queries
  if (← nothingYet) && q.contract.isNone then refutationLane (q.budgetMs / 10) [4, 6]
  -- 3. cheap classical pass (shallow first: classical splits branch quickly)
  if (← nothingYet) && needsClassical then classicalLane (q.budgetMs * 3 / 10) [3, 4, 5, 6]
  -- 4. deeper constructive search: most of what remains when classical lanes are skipped
  if ← nothingYet then
    let rem ← remaining
    let share := if needsClassical then rem * 3 / 10 else rem * 4 / 5
    let done ← completed.get
    lane ledger refutedPrograms graceRef timedOut share (name := "constructive-deeper") fun ctx =>
      enumerateGrace ctx baseCfg goalTy (accept q.target false) (constructiveDepths.drop done) completed
  -- 5. deeper classical search
  if (← nothingYet) && needsClassical then classicalLane ((← remaining) * 2 / 3) [8, 10]
  -- 6. deeper refutation
  if (← nothingYet) && q.contract.isNone then refutationLane (← remaining) [8]
  let cands ← found.get
  let l ← ledger.get
  if !cands.isEmpty then return .verified (← rankCandidates cands) l
  if let some cert ← refuted.get then return .negative .impossible (some cert) l
  if (← rejectedCount.get) > 0 && q.contract.isSome then
    return .refutedAll (← rejectedCount.get) l
  return .negative (if ← timedOut.get then .budgetExhausted else .grammarExhausted) none l

end Leant2
