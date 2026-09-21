import Leant2

open Lean Meta Elab Term Leant2

private def observationContract (f : Bool → Bool) : Bool :=
  [false, true].all fun b => (f b == b) && decide (f b = b)

/-! Splitting checker definitions, finite lists, Boolean conjunctions and
decide must agree with kernel evaluation of the original closed contract. -/
run_elab do
  let ty ← elabType (← `(Bool → Bool))
  let contract ← elabTerm (← `(fun f : Bool → Bool => observationContract f = true)) none
  let observations ← mkObservations contract ty
  unless observations.size == 4 do
    throwError "expected four observations, got {observations.size}"
  for termStx in [← `(fun b : Bool => b), ← `(fun b : Bool => !b),
      ← `(fun _ : Bool => true), ← `(fun _ : Bool => false)] do
    let program ← elabTerm termStx (some ty)
    let (report, _) ← evalObservations observations program #[] instantiatePartial
    let proposition := contract.beta #[program]
    let inst ← synthInstance (mkApp (Lean.mkConst ``Decidable) proposition)
    let (decided, _) ← kernelDecide proposition inst
    unless decided.isSome && report.refuted == (decided == some false) do
      throwError "observation/kernel disagreement"

/-! A report exposes conservative blockers per observation. Unchanged reports
reuse reductions. Sibling branches must not
reuse a result merely because a shared hole is still open. -/
run_elab do
  let ty ← elabType (← `(Bool × Bool))
  let contract ← elabTerm (← `(fun p : Bool × Bool => p.1 = true ∧ p.2 = true)) none
  let observations ← mkObservations contract ty
  let a ← mkFreshExprMVar (Lean.mkConst ``Bool)
  let b ← mkFreshExprMVar (Lean.mkConst ``Bool)
  let pair ← mkAppM ``Prod.mk #[a, b]
  let (first, cache) ← evalObservations observations pair #[] instantiatePartial
  unless first.statuses == #[some .stuck, some .stuck] &&
      first.blockers[0]!.contains a.mvarId! && first.blockers[1]!.contains b.mvarId! do
    throwError "incorrect initial blockers"
  let saved ← saveState
  a.mvarId!.assign (Lean.mkConst ``Bool.true)
  let partialProgram ← instantiatePartial pair
  let (second, next) ← evalObservations observations partialProgram cache instantiatePartial
  unless second.statuses == #[some .satisfied, some .stuck] &&
      second.reused == 2 && second.reductions > 0 && second.reductions ≤ 2 do
    throwError "incorrect incremental report: {repr second.statuses}, reductions {second.reductions}"
  let (same, _) ← evalObservations observations partialProgram next instantiatePartial
  unless same.reductions == 0 && same.reused == 2 do throwError "unchanged observations recomputed"
  saved.restore
  a.mvarId!.assign (Lean.mkConst ``Bool.false)
  let (sibling, _) ← evalObservations observations (← instantiatePartial pair) next instantiatePartial
  unless sibling.refuted do throwError "stale satisfied result survived rollback"
  saved.restore
  let bad ← mkAppM ``Prod.mk #[a, Lean.mkConst ``Bool.false]
  let good ← mkAppM ``Prod.mk #[a, Lean.mkConst ``Bool.true]
  let (badReport, badCache) ← evalObservations observations bad #[] instantiatePartial
  let (goodReport, _) ← evalObservations observations good badCache instantiatePartial
  unless badReport.refuted && goodReport.statuses == #[some .stuck, some .satisfied] do
    throwError "cache ignored changed structure around an open hole"

/-! Quantified propositions with no decider remain inconclusive. -/
run_elab do
  let ty ← elabType (← `(Nat → Nat))
  let contract ← elabTerm (← `(fun f : Nat → Nat => ∀ n, f n = n)) none
  let observations ← mkObservations contract ty
  let program ← elabTerm (← `(fun n : Nat => n)) (some ty)
  let (report, _) ← evalObservations observations program #[] instantiatePartial
  unless report.statuses == #[some .stuck] do throwError "quantified contract was decided"

/-! Project-relative premises can supply a noncanonical Decidable. Keep the
actual instance of `decide P` instead of synthesizing a different instance. -/
axiom observationPremise : False

run_elab do
  let ty := Lean.mkConst ``Bool
  let contract ← elabTerm (← `(fun _ : Bool =>
    @decide False (Decidable.isTrue observationPremise) = true)) none
  let observations ← mkObservations contract ty
  let (report, _) ← evalObservations observations (Lean.mkConst ``Bool.true) #[] instantiatePartial
  unless report.statuses == #[some .satisfied] do
    throwError "the original decidability instance was replaced"

/-! Public callers can reuse a cache with different observation arrays. Keys
must include the observation, even when the partial program is unchanged. -/
run_elab do
  let ty := Lean.mkConst ``Bool
  let yes ← mkObservations (← elabTerm (← `(fun _ : Bool => True)) none) ty
  let no ← mkObservations (← elabTerm (← `(fun _ : Bool => False)) none) ty
  let program := Lean.mkConst ``Bool.true
  let (first, cache) ← evalObservations yes program #[] instantiatePartial
  let (second, _) ← evalObservations no program cache instantiatePartial
  unless first.statuses == #[some .satisfied] && second.refuted && second.reused == 0 do
    throwError "cache ignored changed observations"

/-! Assignments in the predicate are independent of assignments in the program.
Restoring a branch and assigning the predicate's hole differently invalidates
the old reduction, including a result that already reduced to a constant. -/
run_meta do
  let ty := Lean.mkConst ``Bool
  let b ← mkFreshExprMVar ty
  -- Synthesize the generic decider before replacing its parameter by a hole:
  -- typeclass search is allowed to postpone an input containing metavariables.
  let observations ← withLocalDeclD `b ty fun localB => do
    let contract ← withLocalDeclD `f ty fun f => do
      mkLambdaFVars #[f] (← mkEq localB (Lean.mkConst ``Bool.true))
    return (← mkObservations contract ty).map fun obs => {
      predicate := obs.predicate.replaceFVar localB b
      decider := obs.decider.map (·.replaceFVar localB b) }
  let saved ← saveState
  b.mvarId!.assign (Lean.mkConst ``Bool.true)
  let (first, cache) ← evalObservations observations (Lean.mkConst ``Bool.true) #[] instantiatePartial
  saved.restore
  b.mvarId!.assign (Lean.mkConst ``Bool.false)
  let (second, _) ← evalObservations observations (Lean.mkConst ``Bool.true) cache instantiatePartial
  unless first.statuses == #[some .satisfied] && second.refuted && second.reused == 0 do
    throwError "cache ignored changed predicate assignments: {repr first.statuses}, {repr second.statuses}, reused {second.reused}"

/-! Preserve and track the actual decider, including project-relative instances
whose constructor can change while the predicate and program stay fixed. -/
run_elab do
  let ty := Lean.mkConst ``Bool
  let deciderTy := mkApp (Lean.mkConst ``Decidable) (Lean.mkConst ``False)
  let hole ← mkFreshExprMVar deciderTy
  let predicate ← elabTerm (← `(fun _ : Bool => False)) none
  let decider ← withLocalDeclD `f ty fun f => mkLambdaFVars #[f] hole
  let observations : Array Observation := #[{ predicate, decider := some decider }]
  let positive ← elabTerm (← `(@Decidable.isTrue False observationPremise)) (some deciderTy)
  let negative ← elabTerm (← `(@Decidable.isFalse False (fun h => h))) (some deciderTy)
  let saved ← saveState
  hole.mvarId!.assign positive
  let (first, cache) ← evalObservations observations (Lean.mkConst ``Bool.true) #[] instantiatePartial
  saved.restore
  hole.mvarId!.assign negative
  let (second, _) ← evalObservations observations (Lean.mkConst ``Bool.true) cache instantiatePartial
  unless first.statuses == #[some .satisfied] && second.refuted && second.reused == 0 do
    throwError "cache ignored changed decider assignments"

/-! A closed program does not make an observation's free locals context-free. -/
run_meta do
  let ty := Lean.mkConst ``Bool
  withLetDecl `b ty (Lean.mkConst ``Bool.true) fun b => do
    let contract ← withLocalDeclD `f ty fun f => do
      mkLambdaFVars #[f] (← mkEq b (Lean.mkConst ``Bool.true))
    let observations ← mkObservations contract ty
    let (report, cache) ← evalObservations observations (Lean.mkConst ``Bool.true) #[] instantiatePartial
    unless report.statuses == #[some .satisfied] && cache.all Option.isNone do
      throwError "an observation with free locals was cached"

/-! End-to-end synthesis still proves the original Boolean checker. -/
#leant2_check f : (Bool → Bool) where observationContract f = true
