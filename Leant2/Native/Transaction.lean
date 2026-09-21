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

/-- Internal exception raised when the search lane deadline passes. -/
initialize deadlineExceptionId : InternalExceptionId ← registerInternalExceptionId `leant2Deadline

/-- Grace-period completion is successful enumeration termination, not a timeout. -/
initialize graceExceptionId : InternalExceptionId ← registerInternalExceptionId `leant2Grace

/-- Resource limits consumed by a lane. User cancellation is deliberately absent. -/
inductive SearchStop where
  | deadline
  | grace
  | heartbeats
  | recursionDepth
  deriving BEq, Repr

/-- Identify the first expired bound. Merely having a grace deadline does not
turn an earlier lane deadline into successful grace-period completion. -/
def expiredDeadline? (now : Nat) (deadline grace : Option Nat) : Option SearchStop :=
  match deadline, grace with
  | some d, some g =>
    if g ≤ d then (if now > g then some .grace else none)
    else (if now > d then some .deadline else none)
  | some d, none => if now > d then some .deadline else none
  | none, some g => if now > g then some .grace else none
  | none, none => none

def checkDeadline : SearchM Unit := do
  Core.checkInterrupted
  let ctx ← read
  match expiredDeadline? (← IO.monoMsNow) ctx.deadline (← ctx.graceDeadline.get) with
  | some .deadline => throw (.internal deadlineExceptionId)
  | some .grace => throw (.internal graceExceptionId)
  | _ => pure ()

/-- Only explicitly recognized search/resource limits are consumed by a lane.
Other errors, including native user cancellation, retain their identity. -/
def searchStop? (e : Exception) : Option SearchStop :=
  if e.isMaxHeartbeat then some .heartbeats
  else if e.isMaxRecDepth then some .recursionDepth
  else match e with
    | .internal id _ =>
      if id == deadlineExceptionId then some .deadline
      else if id == graceExceptionId then some .grace
      else none
    | _ => none

/-- Only ordinary, non-resource error messages count as rule failure. Internal
exceptions must be handled by their owning API or propagate with their identity. -/
def isInterrupt (e : Exception) : Bool :=
  match e with
  | .internal .. => true
  | .error .. => e.isRuntime

/-- Run `act` from a saved state. On ordinary failure return `none`; cancellation
and resource limits propagate. Every uncommitted exit restores state, including
native interrupts and runtime exceptions, which skip Lean's ordinary `catch`. -/
def attempt (act : SearchM α) : SearchM (Option α) := do
  let saved : Meta.SavedState ← Meta.saveState
  let (result, _) ← tryFinally' (do
    try
      checkDeadline
      return some (← act)
    catch e =>
      if isInterrupt e then throw e
      return none) fun result? =>
        match result? with
        | some (some _) => pure ()
        | _ => saved.restore
  return result

end Leant2
