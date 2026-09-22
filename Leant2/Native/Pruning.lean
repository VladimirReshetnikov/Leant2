import Lean
import Leant2.Core.Types

/-! Dependency authorization for negative kernel observations. A raw false
decision may use axioms forbidden by the query, even when its proposition has
an independent admissible proof. Audit the native, unreduced evidence schema
before allowing it to discard a branch. This is not an acceptance gate. -/

namespace Leant2
open Lean Meta

/-- One environment/profile-local cache of closed evidence schemas. The raw
observation cache is separate: a cached Boolean never carries authorization. -/
structure PruningEvidenceCache where
  environment : Environment
  allowed : List Name
  entries : Array (Expr × Expr × Bool) := #[]

abbrev PruningEvidenceCacheRef := IO.Ref (Option PruningEvidenceCache)

private unsafe def sameEnvironmentImpl (a b : Environment) : BaseIO Bool :=
  pure (ptrEq a b)

/-- The logical fallback never reuses a cached judgment. Runtime pointer
identity only enables reuse for the very same immutable environment object;
keeping that object in the cache also prevents address-reuse confusion. -/
@[implemented_by sameEnvironmentImpl]
private opaque sameEnvironment (_a _b : Environment) : BaseIO Bool := pure false

/-- Check the transitive axiom dependencies of a native predicate and decider.
For partial programs these are their closed lambda-over-program schemas, not
the reduced Boolean or an expression produced by partial closure expansion.
Their bound program argument is parametric; unresolved schema expression
holes, free locals, missing checked declarations, and unsafe declarations
conservatively refuse.

The caller supplies well-typed native evidence. This helper only authorizes
pruning, never certifies an accepted value. Universe parameters/holes do not
change the axiom inventory. Cached judgments require the same environment
object, allowed-axiom list, and fully instantiated schemas. -/
def falseEvidenceAllowed (profile : Profile) (predicate decider : Expr)
    (cache? : Option PruningEvidenceCacheRef := none) : MetaM Bool := do
  let predicate ← instantiateMVars predicate
  let decider ← instantiateMVars decider
  let closed := fun e : Expr =>
    !e.hasExprMVar && !e.hasFVar && !e.hasLooseBVars && !e.hasSorry
  unless closed predicate && closed decider do return false
  let environment ← getEnv
  let allowed := profile.allowedAxioms
  let mut entries := #[]
  if let some cache := cache? then
    if let some previous ← cache.get then
      if (← sameEnvironment previous.environment environment) && previous.allowed == allowed then
        entries := previous.entries
        if let some (_, _, result) := entries.find? fun (p, d, _) =>
            p == predicate && d == decider then
          return result
  let mut permitted := true
  for name in (predicate.getUsedConstants ++ decider.getUsedConstants).toList.eraseDups do
    -- collectAxioms treats an unknown name as having no axioms, and unsafe
    -- declarations need not be kernel-checked even in the checked environment.
    -- Neither can justify pruning for the safe acceptance gate.
    let some info := environment.checked.get.find? name |
      permitted := false
      break
    if info.isUnsafe then
      permitted := false
      break
    if (← collectAxioms name).any (!allowed.contains ·) then
      permitted := false
      break
  if let some cache := cache? then
    cache.set (some {
      environment, allowed
      entries := entries.push (predicate, decider, permitted) })
  return permitted

end Leant2
