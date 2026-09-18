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
    (accept : Expr → SearchM Bool) (productive : SearchM Bool) (depths : List Nat) :
    MetaM Unit := do
  runSearch ctx do
    for depth in depths do
      let root ← mkFreshExprMVar goalTy
      let leaf : Leaf := do
        let e ← instantiateMVars root
        if e.hasExprMVar then return false
        accept e
      let cfg := { cfg with maxDepth := depth }
      let _ ← alternative (search cfg leaf cfg.maxSplits [{ mvar := root.mvarId!, depth }])
      if ← productive then break

/-- Run `act` with a fresh deadline `ms` from now. A lane that hits its
deadline records the fact in `timedOut`; other interrupts propagate. -/
private def lane (ledger : IO.Ref Ledger) (timedOut : IO.Ref Bool) (ms : Nat)
    (act : SearchCtx → MetaM Unit) : MetaM Unit := do
  let ctx : SearchCtx := { ledger, deadline := some ((← IO.monoMsNow) + ms) }
  try act ctx
  catch e =>
    if isInterrupt e then timedOut.set true else throw e

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
    if !b.hasLooseBVar 0 then unused := unused + 1
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
  let start ← IO.monoMsNow
  let frontier ← defaultTypeFrontier
  let providers ← mkProviders q.providers
  let baseCfg : SearchConfig := { providers, typeFrontier := frontier, recursionFirst := q.contract.isSome }
  let found ← IO.mkRef (#[] : Array Accepted)
  let seen ← IO.mkRef (#[] : Array Expr)
  let firstFoundAt ← IO.mkRef (none : Option Nat)
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
      if (← firstFoundAt.get).isNone then firstFoundAt.set (some (← IO.monoMsNow))
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
      (acc : Expr → SearchM Bool) (depths : List Nat) : MetaM Unit := do
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
    enumerate ctx' cfg goalTy acc' (do return (← productive) || (← checkGrace)) depths
  let goalTy ← mkGoal q.target q.contract
  let timedOut ← IO.mkRef false
  -- refutation lane
  let refuted ← IO.mkRef (none : Option Accepted)
  let refutationLane (ms : Nat) (depths : List Nat) : MetaM Unit := lane ledger timedOut ms fun ctx => do
    let negTy ← mkArrow q.target (mkConst ``False)
    let extra ← mkProviders #[``Empty.elim, ``False.elim] (always := true)
    let cfgR := { baseCfg with providers := extra ++ baseCfg.providers }
    enumerate ctx cfgR negTy (fun e => do
        match ← gate .strictConstructive e negTy none with
        | .ok acc => refuted.set (some acc); return true
        | .error _ => return false) (do return (← refuted.get).isSome) depths
  -- classical reasoning needs `Prop` targets: a universe-polymorphic query with
  -- explicit universe parameters is searched at its `Prop` instantiation
  let classicalLane (ms : Nat) (depths : List Nat) : MetaM Unit := lane ledger timedOut ms fun ctx => do
    let tp := atProp q.target
    if tp != q.target then
      let goalP ← mkGoal tp (q.contract.map atProp)
      enumerateGrace ctx { baseCfg with classical := true } goalP (accept tp true) depths
    else
      enumerateGrace ctx { baseCfg with classical := true } goalTy (accept q.target true) depths
  let nothingYet : MetaM Bool := do return (← found.get).isEmpty && (← refuted.get).isNone
  -- 1. cheap constructive pass
  lane ledger timedOut (q.budgetMs * 3 / 20) fun ctx =>
    enumerateGrace ctx baseCfg goalTy (accept q.target false) [2, 3, 5]
  -- 2. cheap refutation pass, only for type-only queries
  if (← nothingYet) && q.contract.isNone then refutationLane (q.budgetMs / 10) [4, 6]
  -- 3. cheap classical pass (shallow first: classical splits branch quickly)
  if ← nothingYet then classicalLane (q.budgetMs * 3 / 10) [3, 4, 5, 6]
  -- 4. deeper constructive search
  if ← nothingYet then
    lane ledger timedOut (q.budgetMs * 3 / 20) fun ctx =>
      enumerateGrace ctx baseCfg goalTy (accept q.target false) [7, 9, 12]
  -- 5. deeper classical search
  if ← nothingYet then classicalLane (q.budgetMs / 5) [8, 10]
  -- 6. deeper refutation
  if (← nothingYet) && q.contract.isNone then refutationLane (q.budgetMs / 10) [8]
  let cands ← found.get
  let l ← ledger.get
  if !cands.isEmpty then return .verified (← rankCandidates cands) l
  if let some cert ← refuted.get then return .negative .impossible (some cert) l
  if (← rejectedCount.get) > 0 && q.contract.isSome then
    return .refutedAll (← rejectedCount.get) l
  return .negative (if ← timedOut.get then .budgetExhausted else .grammarExhausted) none l

end Leant2
