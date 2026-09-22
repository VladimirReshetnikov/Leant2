import Lean

/-! Bounded extraction of native auxiliary theorem bodies. The caller owns
the original environment, shared expansion allowance, resource check, and
exhaustion exception. Final kernel replay remains the caller's responsibility. -/

namespace Leant2.Native
open Lean

/-- Preserve original constants and inline only newly introduced theorems,
instantiating their universe parameters at each use. Fresh axioms, definitions,
and opaque constants remain unchanged so original-environment replay can reject
them. The shared counter is monotone even if the caller restores native state. -/
def inlineNewTheorems {m} [Monad m] [MonadLiftT CoreM m] [MonadControlT CoreM m]
    [MonadExceptOf Exception m] (original speculative : Environment)
    (remaining : IO.Ref Nat) (check : m Unit) (exhausted : Exception) (e : Expr) : m Expr :=
  Core.transform e (pre := fun e => do
    let .const name levels := e | return .continue
    if original.contains name then return .done e
    let some (.thmInfo info) := speculative.find? name | return .done e
    check
    let fuel ← liftM (m := CoreM) remaining.get
    if fuel == 0 then throw exhausted
    liftM (m := CoreM) (remaining.set (fuel - 1))
    return .visit (info.value.instantiateLevelParams info.levelParams levels))

end Leant2.Native
