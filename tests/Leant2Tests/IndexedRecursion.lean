import Leant2

/-! The new outer-recursion tier is tested with an explicit provider inventory.
References are never registered as providers. Kernel acceptance, exact target
preservation, and held-out constructor equations are separate assertions. -/

namespace IndexedRecursion

open Lean Meta Elab Term Leant2

inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)

private def synthesize (target : Expr) (contract : Option Expr) (providers : Array Name)
    (recursor : Name) : MetaM Accepted := do
  let result ← runQuery {
    target, contract, providers, budgetMs := 10000, maxCandidates := 1, graceMs := 0 }
  let .verified candidates _ := result | throwError "outer-recursion query did not succeed"
  let candidate := candidates[0]!
  unless ← isDefEq candidate.programType target do
    throwError "synthesis changed the requested dependent type"
  unless (candidate.program.find? fun e => e.isConstOf recursor).isSome do
    throwError "fixture did not exercise the expected recursor {recursor}"
  return candidate

run_elab do
  let target ← elabType (← `(Nat → Nat))
  let contract ← elabTerm (← `(fun f : Nat → Nat =>
    f 0 = 0 ∧ f 1 = 0 ∧ f 4 = 3)) none
  let candidate ← synthesize target (some contract) #[] ``Nat.rec
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    unless ← isDefEq (mkApp candidate.program (mkApp (mkConst ``Nat.succ) n)) n do
      throwError "Nat predecessor failed its arbitrary-successor equation"

run_elab do
  let target ← elabType (← `(Nat → Nat))
  let contract ← elabTerm (← `(fun f : Nat → Nat =>
    f 0 = 1 ∧ f 3 = 8 ∧ f 5 = 32)) none
  let candidate ← synthesize target (some contract) #[``Nat.add] ``Nat.rec
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let value := mkApp candidate.program n
    let next := mkApp candidate.program (mkApp (mkConst ``Nat.succ) n)
    unless ← isDefEq next (mkApp2 (mkConst ``Nat.add) value value) do
      throwError "power of two failed its arbitrary-successor equation"

/-! This target needs the motive `fun n _ => Vec B n`. Fixed output types
cannot fill its cons branch. No Vec-valued library provider is available. -/
run_elab do
  let target ← elabType (← `(∀ (A B : Type), (A → B) → ∀ n, Vec A n → Vec B n))
  let candidate ← synthesize target none #[] ``Vec.rec
  let expected ← elabTerm (← `(fun (A B : Type) (f : A → B) =>
    fun n (xs : Vec A n) =>
      @Vec.rec A (fun n _ => Vec B n) Vec.nil
        (fun {n} (a : A) (_rest : Vec A n) (ih : Vec B n) => Vec.cons (f a) ih) n xs)) (some target)
  unless ← isDefEq candidate.program expected do
    throwError "indexed map failed the generic native-recursion equations"

/-! An unsupported compound index fails before native motive preparation,
without assigning the original goal or leaking metavariables. -/
run_meta do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let vecType := mkApp2 (mkConst ``Vec) (mkConst ``Bool)
      (mkApp (mkConst ``Nat.succ) n)
    withLocalDeclD `xs vecType fun xs => do
      let goal ← mkFreshExprMVar (mkConst ``Bool)
      let before ← getMCtx
      let ctx : SearchCtx := {
        ledger := ← IO.mkRef {}
        refutedPrograms := ← IO.mkRef {}
        observationCache := ← IO.mkRef #[]
        observationReport := ← IO.mkRef {}
        graceDeadline := ← IO.mkRef none }
      let stopped ← (extendedStructuralRecursion {} (pure true) 2 2
        goal.mvarId! #[(← xs.fvarId!.getDecl)] [] []).run ctx
      if stopped || (← goal.mvarId!.isAssigned) || (← getMCtx).mvarCounter != before.mvarCounter then
        throwError "failed indexed induction did not roll back"

/-! Also reject after native induction has assigned the original goal and its
branch obligations have been completed. The rejected continuation must restore
those assignments and all branch-local metavariables. -/
run_meta do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let vecType := mkApp2 (mkConst ``Vec) (mkConst ``Bool) n
    withLocalDeclD `xs vecType fun xs => do
      let goal ← mkFreshExprMVar (mkConst ``Bool)
      let sibling ← mkFreshExprMVar (mkConst ``Bool)
      let before ← getMCtx
      let reachedAssignedGoal ← IO.mkRef false
      let ctx : SearchCtx := {
        ledger := ← IO.mkRef {}
        refutedPrograms := ← IO.mkRef {}
        observationCache := ← IO.mkRef #[]
        observationReport := ← IO.mkRef {}
        graceDeadline := ← IO.mkRef none }
      let leaf : Leaf := do
        let term ← instantiateMVars goal
        if (← goal.mvarId!.isAssigned) && !term.hasExprMVar &&
            (term.find? fun e => e.isConstOf ``Vec.rec).isSome then
          reachedAssignedGoal.set true
        sibling.mvarId!.assign (mkConst ``Bool.true)
        return false
      let stopped ← (extendedStructuralRecursion {} leaf 2 0
        goal.mvarId! #[(← xs.fvarId!.getDecl)] [] []).run ctx
      unless ← reachedAssignedGoal.get do
        throwError "rollback fixture never completed native induction"
      if stopped || (← goal.mvarId!.isAssigned) || (← sibling.mvarId!.isAssigned) ||
          (← getMCtx).mvarCounter != before.mvarCounter then
        throwError "rejected native induction did not restore its original state"

private def wrapNat (f : Nat → Nat) : { g : Nat → Nat // True } := ⟨f, trivial⟩

/-! Only the actual root Subtype constructor forwards outer-recursion
permission. A provider with the same result type must clear that permission
on its ordinary function argument. Both paths are enumerated at one depth. -/
run_elab do
  let target ← elabType (← `({ g : Nat → Nat // True }))
  let contract ← elabTerm (← `(fun _ : Nat → Nat => True)) none
  let goal ← mkFreshExprMVar target
  let sawConstructorRecursion ← IO.mkRef false
  let sawProvider ← IO.mkRef false
  let sawProviderRecursion ← IO.mkRef false
  let ctx : SearchCtx := {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }
  let cfg : SearchConfig := {
    contract := some contract
    root := some goal.mvarId!
    providers := ← mkProviders #[``wrapNat] }
  let leaf : Leaf := do
    let term ← instantiateMVars goal
    let hasRecursion := (term.find? fun e => e.isConstOf ``Nat.rec).isSome
    if term.getAppFn.isConstOf ``wrapNat then
      sawProvider.set true
      if hasRecursion then sawProviderRecursion.set true
    if term.getAppFn.isConstOf ``Subtype.mk && hasRecursion then
      sawConstructorRecursion.set true
    return false
  let stopped ← (search cfg leaf cfg.maxSplits
    [{ mvar := goal.mvarId!, depth := 2, allowExtendedRecursion := true }]).run ctx
  if stopped || !(← sawProvider.get) || !(← sawConstructorRecursion.get) then
    throwError "eligibility fixture did not enumerate both root application paths"
  if ← sawProviderRecursion.get then
    throwError "ordinary provider application inherited outer-recursion permission"

end IndexedRecursion
