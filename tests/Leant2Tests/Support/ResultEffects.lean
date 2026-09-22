import Lean

/-! An imported test-only IO sentinel for result publication's preflight checks.
It is independent of production diagnostics and is restored by each test. -/
namespace Leant2Tests.ResultEffects

initialize reference : IO.Ref Nat ← IO.mkRef 0

end Leant2Tests.ResultEffects
