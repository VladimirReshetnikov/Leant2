import Lean

/-! Query-owned, exception-safe elapsed spans. Inclusive time includes children;
exclusive time subtracts immediate child spans. Neither is CPU time. Collectors
belong to one serial search and live outside backtrackable Meta/Core state. -/

namespace Leant2.Profiling

open Lean Meta

structure Entry where
  label : String
  inclusiveNs : Nat := 0
  exclusiveNs : Nat := 0
  returned : Nat := 0
  exceptional : Nat := 0
  deriving BEq, Repr, Inhabited

private structure Frame where
  token : Nat
  label : String
  start : Nat
  childrenNs : Nat := 0

private structure State where
  nextToken : Nat := 0
  frames : List Frame := []
  entries : Array Entry := #[]
  valid : Bool := true

/-- A collector has no process-global state. Its clock is injectable for exact
tests. The BaseIO clock cannot replace a search exception with an IO error. -/
structure Collector where
  private clock : BaseIO Nat
  private state : IO.Ref State

def Collector.create (clock : BaseIO Nat := IO.monoNanosNow) : BaseIO Collector := do
  return ⟨clock, ← IO.mkRef {}⟩

structure Snapshot where
  entries : Array Entry := #[]
  activeDepth : Nat := 0
  valid : Bool := true
  deriving BEq, Repr, Inhabited

def Collector.snapshot (c : Collector) : BaseIO Snapshot := do
  let s ← c.state.get
  return { entries := s.entries, activeDepth := s.frames.length, valid := s.valid }

private def beginSpan (c : Collector) (label : String) : BaseIO Nat := do
  let start ← c.clock
  let s ← c.state.get
  let token := s.nextToken
  c.state.set { s with
    nextToken := token + 1
    frames := { token, label, start } :: s.frames }
  return token

private def endSpan (c : Collector) (token : Nat) (returned : Bool) : BaseIO Unit := do
  let stop ← c.clock
  c.state.modify fun s =>
    match s.frames with
    | [] => { s with valid := false }
    | frame :: rest =>
      if frame.token != token then
        -- Broken diagnostic nesting must not mask an escaping search exception.
        { s with frames := [], valid := false }
      else
        let inclusive := stop - frame.start
        let valid := s.valid && stop ≥ frame.start && frame.childrenNs ≤ inclusive
        let entries := if valid then
          let bump (entry : Entry) : Entry := { entry with
            inclusiveNs := entry.inclusiveNs + inclusive
            exclusiveNs := entry.exclusiveNs + (inclusive - frame.childrenNs)
            returned := entry.returned + if returned then 1 else 0
            exceptional := entry.exceptional + if returned then 0 else 1 }
          match s.entries.findIdx? (·.label == frame.label) with
          | some i => s.entries.modify i bump
          | none => s.entries.push (bump { label := frame.label })
        else s.entries
        let frames := match rest with
          | [] => []
          | parent :: tail => { parent with childrenNs := parent.childrenNs + inclusive } :: tail
        { s with entries, frames, valid }

/-- No collector means no clock, reference access, stack, or report work.
Native finalization records partial elapsed time on every exceptional exit,
including interrupts which Lean's ordinary exception handler skips. -/
def span (collector : Option Collector) (label : String) (act : MetaM α) : MetaM α := do
  let some c := collector | return ← act
  let token ← beginSpan c label
  let (result, _) ← tryFinally' act fun result? => do
    endSpan c token result?.isSome
  return result

/-- Closed-span differences, normally between lane entry and lane exit.
Invalid clock/nesting or non-monotone totals suppress numeric reporting. -/
def Snapshot.delta (after before : Snapshot) : Snapshot := Id.run do
  let mut valid := before.valid && after.valid && before.activeDepth == after.activeDepth
  let mut entries := #[]
  for entry in after.entries do
    let old := (before.entries.find? (·.label == entry.label)).getD { label := entry.label }
    valid := valid && entry.inclusiveNs ≥ old.inclusiveNs &&
      entry.exclusiveNs ≥ old.exclusiveNs && entry.returned ≥ old.returned &&
      entry.exceptional ≥ old.exceptional
    let diff : Entry := {
      label := entry.label
      inclusiveNs := entry.inclusiveNs - old.inclusiveNs
      exclusiveNs := entry.exclusiveNs - old.exclusiveNs
      returned := entry.returned - old.returned
      exceptional := entry.exceptional - old.exceptional }
    if diff.returned + diff.exceptional > 0 then entries := entries.push diff
  for old in before.entries do
    if !(after.entries.any (·.label == old.label)) then valid := false
  return { entries, activeDepth := after.activeDepth, valid }

end Leant2.Profiling
