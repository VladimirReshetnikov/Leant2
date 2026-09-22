import Lean
/-!
# Kernel observations of behavioral contracts

Finite `List.all`, Boolean conjunctions and `decide P = true` are split at
query preparation time. These observations are necessary conditions of the
original contract. They only prune search: the original contract is still
proved and kernel-checked before a candidate is accepted.
-/
namespace Leant2

open Lean Meta

/-- An observation and its optional decider, both abstracted over the program. -/
structure Observation where
  predicate : Expr
  decider : Option Expr
  deriving Inhabited

/-- The three answers the kernel can give on a partial program. -/
inductive ObservationStatus where
  | satisfied
  | refuted
  | stuck
  deriving BEq, Repr, Inhabited

/-- A previous reduction. `program` is the exact partial input used for it;
`predicate` and `decider` are instantiated observation keys, so changes to an
observation or its assignments invalidate reuse. `reduced` is the residual
Boolean expression returned by the kernel. Entries are local to one environment
and must not be reused after changing its declarations. -/
structure ObservationCacheEntry where
  program : Expr
  predicate : Expr
  decider : Expr
  reduced : Expr
  deriving Inhabited

/-- `none` means not evaluated because an earlier observation already refuted
the branch. Blocker sets conservatively include every hole in each residual
(including its proof/type arguments); they need not be minimal. Counts
distinguish reductions from reused results. -/
structure ObservationReport where
  statuses : Array (Option ObservationStatus) := #[]
  blockers : Array (Array MVarId) := #[]
  reductions : Nat := 0
  reused : Nat := 0
  deriving Inhabited

def ObservationReport.refuted (r : ObservationReport) : Bool :=
  r.statuses.contains (some .refuted)

private def boolTrue (e : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ .zero]) (mkConst ``Bool) e (mkConst ``Bool.true)

private def boolEqTrue? (e : Expr) : Option Expr := do
  guard (e.isAppOfArity ``Eq 3)
  guard ((e.getArg! 0).isConstOf ``Bool)
  guard ((e.getArg! 2).isConstOf ``Bool.true)
  return e.getArg! 1

/-- Only expand a finite list spine, with a fixed preparation bound. A list
with an unknown spine stays one observation. -/
private def finiteList? (xs : Expr) : MetaM (Option (Array Expr)) := do
  let mut xs := xs
  let mut out := #[]
  for _ in [:256] do
    xs ← whnf xs
    if xs.isAppOfArity ``List.nil 1 then return some out
    if !xs.isAppOfArity ``List.cons 3 then return none
    out := out.push (xs.getArg! 1)
    xs := xs.getArg! 2
  return none

mutual
  /-- Bounded decomposition; unrecognized terms remain intact. -/
  private partial def splitObservation (e : Expr) (fuel : Nat) : MetaM (Array (Expr × Option Expr)) := do
    if fuel == 0 then return #[(e, none)]
    let e := e.headBeta
    if e.isAppOfArity ``And 2 then
      let a ← splitObservation (e.getArg! 0) (fuel - 1)
      let b ← splitObservation (e.getArg! 1) (fuel - 1)
      return if a.size + b.size ≤ 256 then a ++ b else #[(e, none)]
    if let some b := boolEqTrue? e then return ← splitBoolean b (fuel - 1)
    return #[(e, none)]

  private partial def splitBoolean (b : Expr) (fuel : Nat) : MetaM (Array (Expr × Option Expr)) := do
    let b := b.headBeta
    if fuel == 0 then return #[(boolTrue b, none)]
    if b.isAppOfArity ``Bool.and 2 then
      let a ← splitBoolean (b.getArg! 0) (fuel - 1)
      let c ← splitBoolean (b.getArg! 1) (fuel - 1)
      return if a.size + c.size ≤ 256 then a ++ c else #[(boolTrue b, none)]
    if b.isAppOfArity ``List.all 3 then
      if let some xs ← finiteList? (b.getArg! 1) then
        let mut out := #[]
        for x in xs do
          out := out ++ (← splitBoolean ((b.getArg! 2).beta #[x]) (fuel - 1))
          if out.size > 256 then return #[(boolTrue b, none)]
        -- Keep the empty case explicit so that the report is nonempty.
        return if out.isEmpty then #[(boolTrue b, none)] else out
    if b.isAppOfArity ``Decidable.decide 2 then
      return #[(b.getArg! 0, some (b.getArg! 1))]
    -- Open a named checker one definition at a time, before WHNF erases the
    -- recognizable `Bool.and`/`List.all` structure. No arbitrary normalization.
    if let some unfolded ← unfoldDefinition? b then
      if unfolded != b then return ← splitBoolean unfolded (fuel - 1)
    return #[(boolTrue b, none)]
end

/-- Prepare observations once. Lack of a decider is inconclusive, never a
refutation; quantified contracts remain obligations for the proof service. -/
def mkObservations (contract ty : Expr) : MetaM (Array Observation) :=
  withLocalDeclD `f ty fun f => do
    let parts ← splitObservation (contract.beta #[f]) 32
    parts.mapM fun (p, givenDecider) => do
      let inst? ← try match givenDecider with
        | some inst => pure (some inst)
        | none => synthInstance? (mkApp (mkConst ``Decidable) p)
        catch e => if e.isInterrupt || e.isRuntime then throw e else pure none
      return { predicate := ← mkLambdaFVars #[f] p,
               decider := ← inst?.mapM fun i => do mkLambdaFVars #[f] (← instantiateMVars i) }

/-- Evaluate every observation unless an earlier one refutes the branch.
The caller supplies delayed-assignment-aware instantiation. Reusing a cached
residual requires that its original program, instantiated in the *current*
branch, exactly matches the current program. Testing only that the old holes
are still open would be unsound when a sibling branch changes the surrounding
program. The instantiated predicate and decider must also match their original
keys. Inputs or observations containing free locals are deliberately not cached
across contexts. The caller must keep the environment fixed for the cache's
lifetime (the engine allocates a fresh cache for each lane).

The default `authorizeFalse` preserves raw kernel-reduction reporting; it does
not enforce an axiom profile. Profile-sensitive search supplies a callback over
the current unreduced predicate/decider schemas, including on cached false
results. Refusal reports `stuck` and continues to later observations. -/
def evalObservations (observations : Array Observation) (program : Expr)
    (cache : Array (Option ObservationCacheEntry)) (instantiate : Expr → MetaM Expr)
    (check : MetaM Unit := pure ())
    (authorizeFalse : Expr → Expr → MetaM Bool := fun _ _ => pure true) :
    MetaM (ObservationReport × Array (Option ObservationCacheEntry)) := do
  let mut report : ObservationReport := {
    statuses := Array.replicate observations.size none
    blockers := Array.replicate observations.size #[] }
  let mut next := Array.replicate observations.size none
  -- All entries emitted by this evaluator share an input. Instantiate that
  -- input only once, not once for every example in a large checker.
  let cachedProgram := (cache.findSome? id).map (·.program)
  let sameProgram ← match cachedProgram with
    | some previous => do pure (!program.hasFVar && (← instantiate previous) == program)
    | none => pure false
  for idx in [:observations.size] do
    check
    let obs := observations[idx]!
    let some inst := obs.decider |
      report := { report with statuses := report.statuses.set! idx (some .stuck) }
      continue
    let predicate ← instantiate obs.predicate
    let decider ← instantiate inst
    let cacheable := !program.hasFVar && !predicate.hasFVar && !decider.hasFVar
    let mut input := mkApp2 (mkConst ``Decidable.decide)
      (predicate.beta #[program]) (decider.beta #[program])
    let mut reused := false
    let mut unchanged := false
    if sameProgram && cacheable then
      if let some (some prev) := cache[idx]? then
        if some prev.program == cachedProgram &&
            prev.predicate == predicate && prev.decider == decider then
          input ← instantiate prev.reduced
          reused := true
          unchanged := input == prev.reduced
    let reduced? ← if unchanged || input.isConstOf ``Bool.true || input.isConstOf ``Bool.false then
        pure (some input)
      else
        report := { report with reductions := report.reductions + 1 }
        pure ((Kernel.whnf (← getEnv) (← getLCtx) input).toOption)
    if reused then report := { report with reused := report.reused + 1 }
    let some reduced := reduced? |
      report := { report with statuses := report.statuses.set! idx (some .stuck) }
      continue
    let status ← if reduced.isConstOf ``Bool.true then pure ObservationStatus.satisfied
      else if reduced.isConstOf ``Bool.false then
        -- Reauthorize even an unchanged raw cache hit, using current evidence.
        -- A refused false result is inconclusive; later observations may still
        -- supply an authorized refutation.
        pure (if ← authorizeFalse predicate decider then .refuted else .stuck)
      else pure .stuck
    report := { report with
      statuses := report.statuses.set! idx (some status)
      blockers := report.blockers.set! idx (reduced.collectMVars {}).result }
    if cacheable then next := next.set! idx (some { program, predicate, decider, reduced })
    if status == .refuted then break
  return (report, next)

end Leant2
