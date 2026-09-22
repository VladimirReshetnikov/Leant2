import Leant2.Frontend.Sketch
import Leant2Tests.Support.SketchEffects

/-! Direct command-entry integration. Fixed zero-hole inputs keep these tests
independent of synthesis ranking. Expected diagnostics and temporary aliases
are restored inside each fixture; frontend failures must not be mistaken for
successful `elabCommand` recovery. -/
namespace Leant2Tests.SketchCommand
open Lean Meta Elab Command Term Leant2 Frontend.Sketch

elab "sketchTypeWithError%" : term => do
  logError "sketch command test: type elaborator returned a valid type with an error"
  return mkConst ``Nat

elab "sketchContractWithError%" : term => do
  logError "sketch command test: contract elaborator returned a valid Prop with an error"
  return mkConst ``True

private def observeAll (action : CommandElabM α) : CommandElabM (Except Exception α) := do
  let _ : MonadExceptOf Exception CommandElabM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch ex => return .error ex

private unsafe def assertRestored (before : Command.State) : CommandElabM Unit := do
  unless ptrEq before (← get) do
    throwError "failed sketch command changed the exact caller Command.State"

private def requireValue (name : Name) (expected : Nat) : CommandElabM Unit :=
  liftTermElabM do
    unless ← isDefEq (mkConst name) (mkNatLit expected) do
      throwError "published result does not retain its checked value"

private def numbered : CommandElabM Name := do
  let some name := resultBinding? (← getEnv) `it1
    | throwError "successful sketch command did not publish it1"
  return name

private unsafe def rejectsPreparation (input : Syntax) : CommandElabM Unit := do
  let before ← get
  let .error ex ← observeAll (elabSketchCommand input)
    | throwError "malformed sketch command did not throw"
  unless (← ex.toMessageData.toString).startsWith "leant2 sketch: preparation failed:" do
    throwError "malformed sketch command used the wrong failure classification"
  assertRestored before

run_cmd do
  let saved ← get
  try
    -- Exercise the optional absent `where` clause through the real public
    -- command elaborator, not a manually constructed controller Query.
    elabSketchCommand (← `(command| #leant2_sketch f : Nat := 7))
    let original ← numbered
    requireValue original 7
    let originalInfo ← liftCoreM <| getConstInfo original
    let originalValue := originalInfo.value? (allowOpaque := true)
    unless resultBinding? (← getEnv) `it == some original do
      throwError "successful sketch command did not publish bare it"

    rejectsPreparation (← `(command|
      #leant2_sketch f : Nat × Nat := (?same, ?same)))
    rejectsPreparation (← `(command|
      #leant2_sketch f : sketchTypeWithError% := 0))
    rejectsPreparation (← `(command|
      #leant2_sketch f : Nat := 0 where sketchContractWithError%))
    unless (← numbered) == original do
      throwError "preparation failure changed the previous alias"
    unless (← liftCoreM <| getConstInfo original).value? (allowOpaque := true) == originalValue do
      throwError "preparation failure changed the immutable prior definition"

    -- Earlier errors stay visible but are not new query errors. This log is
    -- discarded only by the outer test finalizer, after its preservation check.
    logError "sketch command test: unrelated earlier diagnostic"
    let errorsBefore := ((← get).messages.toList.filter (·.severity == .error)).length
    elabSketchCommand (← `(command| #leant2_sketch f : Nat := 11))
    let current ← numbered
    unless current != original do throwError "new sketch reused an immutable result name"
    requireValue current 11
    requireValue original 7
    unless ((← get).messages.toList.filter (·.severity == .error)).length == errorsBefore do
      throwError "valid sketch query changed unrelated prior error diagnostics"

    -- Well-formed mathematical rejection has different alias semantics from
    -- preflight failure: numbered results clear, bare it remains the last value.
    elabSketchCommand (← `(command| #leant2_sketch f : Nat := 0 where False))
    if (resultBinding? (← getEnv) `it1).isSome ||
        !(getAliases (← getEnv) `it1 false).isEmpty then
      throwError "negative sketch retained a numbered result"
    unless resultBinding? (← getEnv) `it == some current do
      throwError "negative sketch replaced bare it"
    requireValue current 11
    requireValue original 7
  finally
    set saved

run_cmd do
  let saved ← get
  let oldToken ← SketchEffects.token.get
  let oldPrevious ← SketchEffects.previousBinding.get
  let oldObserved ← SketchEffects.observedBinding.get
  try
    elabSketchCommand (← `(command| #leant2_sketch f : Nat := 19))
    let previous ← numbered
    let input ← `(command| #leant2_sketch f : Nat := SketchEffects.displayValue)
    let cancellation ← IO.CancelToken.new
    SketchEffects.previousBinding.set (some previous)
    SketchEffects.observedBinding.set none
    SketchEffects.token.set (some cancellation)
    let before ← get
    let .error ex ← observeAll <| withReader
        (fun context => { context with cancelTk? := some cancellation })
        (elabSketchCommand input)
      | throwError "formatting-triggered cancellation did not escape the command"
    unless ex.isInterrupt do throwError "command changed native cancellation identity"
    -- The IO evidence survives rollback. It must prove this interruption came
    -- after publication; a pre-cancelled search would not satisfy the fixture.
    let some published ← SketchEffects.observedBinding.get
      | throwError "cancellation fixture never observed the new published alias"
    unless published != previous && (← cancellation.isSet) do
      throwError "cancellation did not occur after a changed result binding"
    assertRestored before
    unless (← numbered) == previous && resultBinding? (← getEnv) `it == some previous do
      throwError "cancelled command retained provisional result aliases"
    if (← getEnv).contains published then
      throwError "cancelled command leaked its provisional immutable declaration"
    requireValue previous 19
  finally
    SketchEffects.token.set oldToken
    SketchEffects.previousBinding.set oldPrevious
    SketchEffects.observedBinding.set oldObserved
    set saved

end Leant2Tests.SketchCommand
