import Lean
import Leant2.Core.Types
import Leant2.Behavior.Observations
/-!
# Transactional search state

The atomic attempt (Section 5.1): snapshot, run, restore on failure, and never
swallow interrupts. Work charges live in an `IO.Ref` outside the snapshot so
that rollback cannot refund them (Decision 2.8).
-/
namespace Leant2

open Lean Meta

/-- Search context: a ledger reference and a wall-clock deadline. -/
structure SearchCtx where
  ledger : IO.Ref Ledger
  deadline : Option Nat := none  -- monotonic milliseconds
  /-- Closed programs whose contract already reduced to `false` (per query):
  the same program is reached along several paths and across deepening passes. -/
  refutedPrograms : IO.Ref (Std.HashSet Expr)
  /-- Lane-local per-observation reductions, guarded by their partial input. -/
  observationCache : IO.Ref (Array (Option ObservationCacheEntry))
  /-- Most recent observation report, for diagnostics and search guidance. -/
  observationReport : IO.Ref ObservationReport
  /-- A deadline set once the first candidate is accepted (the grace period),
  checked together with the lane deadline. -/
  graceDeadline : IO.Ref (Option Nat)

abbrev SearchM := ReaderT SearchCtx MetaM

def charge (f : Ledger → Ledger) : SearchM Unit := do
  (← read).ledger.modify f

/-- Internal exception raised when the search deadline passes. -/
initialize deadlineExceptionId : InternalExceptionId ← registerInternalExceptionId `leant2Deadline

def checkDeadline : SearchM Unit := do
  let now ← IO.monoMsNow
  match (← read).deadline with
  | none => pure ()
  | some d => if now > d then throw (.internal deadlineExceptionId)
  match ← (← read).graceDeadline.get with
  | none => pure ()
  | some d => if now > d then throw (.internal deadlineExceptionId)

/-- `True` when an exception must propagate rather than count as rule failure. -/
def isInterrupt (e : Exception) : Bool :=
  e.isInterrupt || e.isRuntime ||
    (match e with
     | .internal id _ => id == deadlineExceptionId
     | _ => false)

/-- Run `act` from a saved state. On failure restore the state and return
`none`. Interrupts, heartbeat exhaustion, and the search deadline propagate. -/
def attempt (act : SearchM α) : SearchM (Option α) := do
  let saved : Meta.SavedState ← Meta.saveState
  try
    checkDeadline
    let r ← act
    return some r
  catch e =>
    if isInterrupt e then throw e
    saved.restore
    return none

end Leant2
