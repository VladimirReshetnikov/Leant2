import Leant2.Search.Core

/-! Optional rule profiling must preserve bounded enumeration, including its
order and work ledger. Each fixture exhausts a fixed depth with tracing disabled,
then enabled; every proposed expression is independently type-checked. -/

namespace Leant2Tests.Substrate

open Lean Meta Elab Term Leant2

private def proposals (target : Expr) (depth : Nat) (profiled : Bool)
    : MetaM (Array Expr × Ledger × Array (String × Nat)) := do
  let saved ← saveState
  let root ← mkFreshExprMVar target
  let out ← IO.mkRef #[]
  let errors ← IO.mkRef #[]
  let ledger ← IO.mkRef {}
  let ctx : SearchCtx := {
    ledger
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }
  let cfg : SearchConfig := { maxSplits := 0, proofPortfolio := false }
  let leaf : Leaf := do
    let e ← instantiateMVars root
    try
      check e
      unless ← isDefEq (← inferType e) (← instantiateMVars target) do
        throwError "proposal has the wrong type"
    catch ex =>
      if isInterrupt ex then throw ex
      errors.modify (·.push ex.toMessageData)
    out.modify (·.push e)
    return false
  let previousTimers ← profTimers.get
  profTimers.set #[]
  let _ ← withOptions (fun opts => leant2.trace.set opts profiled) do
    (search cfg leaf 0 [{ mvar := root.mvarId!, depth }]).run ctx
  let result := (← out.get, ← ledger.get, ← profTimers.get)
  profTimers.set previousTimers
  saved.restore
  unless (← errors.get).isEmpty do
    throwError "ill-typed proposals: {← errors.get}"
  return result

private def checkParity (target : Expr) (depth : Nat := 2) : MetaM Unit := do
  let (plain, plainWork, plainTimers) ← proposals target depth false
  let (profiled, profiledWork, activeTimers) ← proposals target depth true
  if plain.isEmpty then throwError "fixture did not exercise a candidate"
  unless plain == profiled do throwError "profiling changed candidate order or content"
  unless reprStr plainWork == reprStr profiledWork do
    throwError "profiling changed the work ledger"
  unless plainTimers.isEmpty do throwError "disabled profiling recorded rule timers"
  for key in ["entry", "alt.save", "alt.restore"] do
    unless activeTimers.any (·.1 == key) do throwError "enabled profiling omitted {key}"

run_elab do
  for stx in #[
      ← `(∀ A B : Type, (A → B) → A → B),
      ← `((Nat × Bool) → Bool × Nat),
      ← `(∀ p q : Prop, (p ↔ q) → ¬p → ¬q),
      ← `((∀ R : Type, R → R → R) → Bool)] do
    checkParity (← elabType stx)

/-! Profiling also preserves rollback when a local type is fixed differently by
different alternatives. -/
run_meta do
  let α ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `x α fun _ => do
    checkParity (mkConst ``Bool) 1

/-! Include a hole hidden in an implementation-detail let value, whose changes
affect a later local type. -/
run_meta do
  let α ← mkFreshExprMVar (mkSort (.succ .zero))
  withLetDecl `T (mkSort (.succ .zero)) α (kind := .implDetail) fun t => do
    withLocalDeclD `x t fun _ => do
      checkParity (mkConst ``Bool) 1

end Leant2Tests.Substrate
