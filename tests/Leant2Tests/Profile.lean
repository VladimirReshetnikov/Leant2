import Leant2.Engine

/-! Clock-injected profiling tests. No sleeps, elapsed-time thresholds, or
search budgets establish the accounting assertions. Native cancellation and
rollback retain their existing semantics while diagnostic spans finalize. -/

namespace Leant2Tests.Profiling

open Lean Meta Elab Leant2

private def observeAll (act : MetaM α) : MetaM (Except Exception α) := do
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try return .ok (← act)
  catch ex => return .error ex

private def clocked (times : List Nat) : MetaM
    (Leant2.Profiling.Collector × IO.Ref (List Nat) × IO.Ref Nat) := do
  let pending ← IO.mkRef times
  let calls ← IO.mkRef 0
  let clock : BaseIO Nat := do
    calls.modify (· + 1)
    match ← pending.get with
    | [] => return 0
    | value :: rest => pending.set rest; return value
  return (← Leant2.Profiling.Collector.create clock, pending, calls)

private def checkEntries (collector : Leant2.Profiling.Collector)
    (expected : Array Leant2.Profiling.Entry) : MetaM Unit := do
  let report ← collector.snapshot
  unless report.valid && report.activeDepth == 0 && report.entries == expected do
    throwError "unexpected span accounting: {repr report}; expected {repr expected}"

private def context (profile : Option Leant2.Profiling.Collector := none) : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}, profile
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

-- A returned false/none is still a normally returned invocation.
run_meta do
  let (collector, pending, calls) ← clocked [10, 25, 30, 34]
  unless !(← Leant2.Profiling.span (some collector) "flat" (pure false)) do
    throwError "span changed false result"
  let result ← Leant2.Profiling.span (some collector) "option" (pure (none : Option Nat))
  unless result.isNone do throwError "span changed optional result"
  checkEntries collector #[
    { label := "flat", inclusiveNs := 15, exclusiveNs := 15, returned := 1 },
    { label := "option", inclusiveNs := 4, exclusiveNs := 4, returned := 1 }]
  unless (← pending.get).isEmpty && (← calls.get) == 4 do
    throwError "span used unexpected clocks"

run_meta do
  let (collector, _, _) ← clocked [0, 3, 11, 20]
  Leant2.Profiling.span (some collector) "parent" do
    Leant2.Profiling.span (some collector) "child" (pure ())
  checkEntries collector #[
    { label := "child", inclusiveNs := 8, exclusiveNs := 8, returned := 1 },
    { label := "parent", inclusiveNs := 20, exclusiveNs := 12, returned := 1 }]

-- Invocation identity is separate from the aggregate label, including recursion.
run_meta do
  let (collector, _, _) ← clocked [0, 2, 5, 10, 20, 24]
  Leant2.Profiling.span (some collector) "same" do
    Leant2.Profiling.span (some collector) "same" (pure ())
  Leant2.Profiling.span (some collector) "same" (pure ())
  checkEntries collector #[
    { label := "same", inclusiveNs := 17, exclusiveNs := 14, returned := 3 }]

private def ordinary : Exception := .error .missing m!"profile ordinary failure"

private def sameException (actual expected : Exception) : MetaM Bool := do
  match actual, expected with
  | .internal a x, .internal b y =>
    return a == b && x.getNat `profile.identity == y.getNat `profile.identity
  | .error _ a, .error _ b =>
    return a.stripNestedTags.kind == b.stripNestedTags.kind && (← a.toString) == (← b.toString)
  | _, _ => return false

-- Caught child failure does not mark the returning parent exceptional.
run_meta do
  let (collector, _, _) ← clocked [0, 3, 11, 20]
  Leant2.Profiling.span (some collector) "parent" do
    let result ← observeAll <| Leant2.Profiling.span (some collector) "child"
      (throw ordinary : MetaM Unit)
    unless result matches .error _ do throwError "span consumed child failure"
  checkEntries collector #[
    { label := "child", inclusiveNs := 8, exclusiveNs := 8, exceptional := 1 },
    { label := "parent", inclusiveNs := 20, exclusiveNs := 12, returned := 1 }]

-- Every class of native exceptional exit retains identity and partial time.
run_meta do
  let payload := ({} : KVMap).setNat `profile.identity 37
  for ex in [ordinary,
      Exception.internal unsupportedSyntaxExceptionId payload,
      .internal interruptExceptionId payload,
      .internal deadlineExceptionId payload,
      .internal graceExceptionId payload,
      .error .missing (.tagged `runtime.maxHeartbeats m!"injected heartbeat"),
      .error .missing (.tagged `runtime.maxRecDepth m!"injected recursion depth")] do
    let (collector, _, _) ← clocked [0, 2, 7, 11]
    let result ← observeAll <| Leant2.Profiling.span (some collector) "outer" do
      Leant2.Profiling.span (some collector) "inner" (throw ex : MetaM Unit)
    match result with
    | .ok _ => throwError "span swallowed an exception"
    | .error actual => unless ← sameException actual ex do throwError "span changed exception identity"
    checkEntries collector #[
      { label := "inner", inclusiveNs := 5, exclusiveNs := 5, exceptional := 1 },
      { label := "outer", inclusiveNs := 11, exclusiveNs := 6, exceptional := 1 }]

run_meta do
  let (collector, _, _) ← clocked [0, 2, 7, 11]
  let token ← IO.CancelToken.new
  token.set
  let result ← observeAll <| withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
    Leant2.Profiling.span (some collector) "outer" do
      Leant2.Profiling.span (some collector) "inner" Core.checkInterrupted
  match result with
  | .error (.internal id _) => unless id == interruptExceptionId do throwError "changed cancellation"
  | _ => throwError "span swallowed native cancellation"
  checkEntries collector #[
    { label := "inner", inclusiveNs := 5, exclusiveNs := 5, exceptional := 1 },
    { label := "outer", inclusiveNs := 11, exclusiveNs := 6, exceptional := 1 }]

-- Two collectors stay isolated; successive closed intervals produce exact deltas.
run_meta do
  let (first, _, _) ← clocked [1, 4, 10, 15]
  let (second, _, _) ← clocked [20, 29]
  Leant2.Profiling.span (some first) "step" (pure ())
  let before ← first.snapshot
  discard <| observeAll <| Leant2.Profiling.span (some first) "step" (throw ordinary : MetaM Unit)
  Leant2.Profiling.span (some second) "step" (pure ())
  let delta := (← first.snapshot).delta before
  unless delta.valid && delta.activeDepth == 0 && delta.entries == #[
      { label := "step", inclusiveNs := 5, exclusiveNs := 5, exceptional := 1 }] do
    throwError "lane delta included previous work: {repr delta}"
  checkEntries second #[{ label := "step", inclusiveNs := 9, exclusiveNs := 9, returned := 1 }]

-- Disabled spans do not touch a collector or its clock, including on failure.
run_meta do
  let (collector, pending, calls) ← clocked [1, 2]
  let before ← collector.snapshot
  let effects ← IO.mkRef 0
  let result ← Leant2.Profiling.span none "disabled" do
    effects.modify (· + 1)
    return 17
  let failed ← observeAll <| Leant2.Profiling.span none "disabled" (throw ordinary : MetaM Unit)
  unless result == 17 && (← effects.get) == 1 && (← calls.get) == 0 &&
      (← pending.get) == [1, 2] && (← collector.snapshot) == before do
    throwError "disabled profiling performed diagnostic work or changed the action"
  unless failed matches .error _ do throwError "disabled span consumed exception"

-- Malformed clocks invalidate reports without replacing a search exception.
run_meta do
  let (collector, _, _) ← clocked [10, 5]
  let result ← observeAll <| Leant2.Profiling.span (some collector) "bad clock" (throw ordinary : MetaM Unit)
  match result with
  | .error actual => unless ← sameException actual ordinary do throwError "clock masked search error"
  | _ => throwError "clock swallowed search error"
  let snapshot ← collector.snapshot
  unless !snapshot.valid && snapshot.activeDepth == 0 do throwError "invalid clock produced valid report"

-- The lane wrapper reports closed deltas, including a consumed deadline exit,
-- while headers retain the ordinary cumulative ledger. Clock values are exact.
run_meta do
  let (collector, pending, _) ← clocked [0, 2, 5, 10, 20, 21, 25, 30]
  let ctx ← context
  let timedOut ← IO.mkRef false
  withOptions (fun opts => leant2.trace.set opts true) do
    withLane ctx.ledger ctx.refutedPrograms ctx.graceDeadline timedOut 1000000
      (fun lane => (timed "work" (pure ())).run lane)
      (name := "profile-test-first") (profile := some collector)
    withLane ctx.ledger ctx.refutedPrograms ctx.graceDeadline timedOut 1000000
      (fun lane => (timed "work" (throw (.internal deadlineExceptionId) : SearchM Unit)).run lane)
      (name := "profile-test-stop") (profile := some collector)
  unless (← timedOut.get) && (← pending.get).isEmpty do throwError "lane changed stop/clock behavior"
  checkEntries collector #[
    { label := "work", inclusiveNs := 7, exclusiveNs := 7, returned := 1, exceptional := 1 },
    { label := "lane.search", inclusiveNs := 20, exclusiveNs := 13, returned := 1, exceptional := 1 }]

-- An explicitly supplied collector does not turn a trace-disabled lane on.
run_meta do
  let (collector, pending, calls) ← clocked [1, 2]
  let ctx ← context
  let timedOut ← IO.mkRef false
  withOptions (fun opts => leant2.trace.set opts false) do
    withLane ctx.ledger ctx.refutedPrograms ctx.graceDeadline timedOut 1000000
      (fun lane => do
        if lane.profile.isSome then throwError "disabled lane retained a collector"
        (timed "work" (pure ())).run lane)
      (profile := some collector)
  unless (← pending.get) == [1, 2] && (← calls.get) == 0 do
    throwError "disabled lane accessed profiling clock"
  checkEntries collector #[]

-- Profiling remains outside rollback, including save/restore and joint assignments.
run_meta do
  for answer in [false, true] do
    withoutModifyingState do
      let times := if answer then [0, 1, 4, 7] else [0, 1, 4, 5, 8, 10]
      let (collector, pending, _) ← clocked times
      let ctx ← context (some collector)
      let g ← mkFreshExprMVar (mkConst ``Nat)
      let sibling ← mkFreshExprMVar (mkConst ``Nat)
      let u ← mkFreshLevelMVar
      let beforeMessages := (← getThe Core.State).messages.toList.length
      let result ← (timed "branch" <| alternative do
        g.mvarId!.assign (mkNatLit 3)
        sibling.mvarId!.assign (mkNatLit 5)
        unless ← isDefEq (mkSort u) (mkSort (.succ .zero)) do throwError "universe fixture"
        logInfo "profile rollback marker"
        charge fun ledger => { ledger with ruleApplications := ledger.ruleApplications + 1 }
        return answer).run ctx
      unless result == answer && (← g.mvarId!.isAssigned) == answer &&
          (← sibling.mvarId!.isAssigned) == answer do throwError "profiling changed transaction result"
      if !answer then
        unless (← instantiateLevelMVars u) == u &&
            (← getThe Core.State).messages.toList.length == beforeMessages do
          throwError "profiling changed rollback"
      unless (← ctx.ledger.get).ruleApplications == 1 && (← pending.get).isEmpty do
        throwError "profiling changed ledger or clock work"
      let expected := if answer then #[
          { label := "alt.save", inclusiveNs := 3, exclusiveNs := 3, returned := 1 },
          { label := "branch", inclusiveNs := 7, exclusiveNs := 4, returned := 1 }]
        else #[
          { label := "alt.save", inclusiveNs := 3, exclusiveNs := 3, returned := 1 },
          { label := "alt.restore", inclusiveNs := 3, exclusiveNs := 3, returned := 1 },
          { label := "branch", inclusiveNs := 10, exclusiveNs := 4, returned := 1 }]
      checkEntries collector expected

end Leant2Tests.Profiling
