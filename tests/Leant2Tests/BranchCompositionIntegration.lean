import Leant2

/-!
These are bounded search-route tests, not public synthesis benchmarks. Every
fixture starts with no scoped hook. At an actual search leaf, an installed
scopedBudgetCheck witnesses an active composition prefix. Identical programs
can also be produced by ordinary search, so inspecting Expr constants alone
would not establish which route ran. No fixture calls BranchComposition.run.

Expected terms are leaf observers only, never providers or pruning predicates.
The separate public tree gate owns finite contracts, typed replay, universal
constructor equations, and held-out execution. Printed-source roundtrip is a
separate publication-test obligation.
-/

namespace Leant2Tests.BranchCompositionIntegration

open Lean Meta Elab Term Leant2

private def context : MetaM SearchCtx := do
  let ctx : SearchCtx := {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }
  unless ctx.scopedBudgetCheck.isNone do throwError "route fixture inherited a scope"
  return ctx

private def cfgFor (type : Expr) : SearchConfig := {
  contract := some (mkLambda `candidate .default type (Lean.mkConst ``True))
  proofPortfolio := false
  maxSplits := 1
  skip := ["guards", "7a", "7b", "9c", "residual"] }

private def containsConst (term : Expr) (name : Name) : Bool :=
  (term.find? fun e => e.isConstOf name).isSome

private def hasGuard (term : Expr) : Bool :=
  containsConst term ``Decidable.rec || containsConst term ``Decidable.casesOn

private def requireKernel (value type : Expr) : MetaM Unit := do
  match ← gate .strictConstructive value type none with
  | .ok accepted =>
    unless accepted.axioms.isEmpty do throwError "route witness acquired an axiom"
  | .error _ => throwError "completed route witness failed strict kernel acceptance"

-- Positive controls start at search, not at the direct filler seam. A scoped
-- callback must produce the selected term at the given ordinary depth.
private def requireScoped (type wanted : Expr) (depth : Nat := 1) : MetaM Unit :=
  withoutModifyingState do
    let ctx ← context
    let goal ← mkFreshExprMVar type
    let leaf : Leaf := do
      unless (← read).scopedBudgetCheck.isSome do return false
      let value ← instantiateMVars goal
      if value.hasExprMVar then return false
      withNewMCtxDepth (isDefEq value wanted)
    let found ← (search (cfgFor type) leaf 0
      [{ mvar := goal.mvarId!, depth, tryBranchComposition := true }]).run ctx
    unless found do throwError "positive search route never reached composition"
    requireKernel (← instantiateMVars goal) type

-- Reject every leaf so exclusion checks cover the whole bounded fixture. The
-- selected ordinary route must really occur; a missing route is not a pass.
private def requireUnscopedRoute (type : Expr) (cfg : SearchConfig) (depth splits : Nat)
    (route : Expr → Bool) (incomingComposition := false)
    (outerRecursion := false) (guards := false) : MetaM Unit :=
  withoutModifyingState do
    let ctx ← context
    let goal ← mkFreshExprMVar type
    let reached ← IO.mkRef false
    let leaked ← IO.mkRef false
    let leaf : Leaf := do
      let value ← instantiateMVars goal
      if route value then
        reached.set true
        if (← read).scopedBudgetCheck.isSome then leaked.set true
      return false
    let initial : Goal := {
      mvar := goal.mvarId!, depth
      tryBranchComposition := incomingComposition
      allowExtendedRecursion := outerRecursion
      allowNatGuards := guards }
    let found ← (search cfg leaf splits [initial]).run ctx
    unless ← reached.get do throwError "negative route fixture never reached its ordinary route"
    if found || (← leaked.get) || (← goal.mvarId!.isAssigned) then
      throwError "excluded route inherited composition or leaked rejected search state"

inductive Fork where
  | tip : Fork
  | fork : Fork → Fork → Fork

private def wrapFork (f : Fork → Nat) : {_f : Fork → Nat // True} := ⟨f, trivial⟩

-- The real root Subtype constructor enables the program's outer native minor.
-- The same-result ordinary provider reaches the SAME nonindexed induction rule
-- but must not give its argument that permission. Rejecting all leaves reaches
-- both routes, and only the actual constructor route may have a scoped leaf.
run_elab do
  withoutModifyingState do
    let type ← elabType (← `(Fork → Nat))
    let contract := mkLambda `f .default type (Lean.mkConst ``True)
    let rootType ← mkAppM ``Subtype #[contract]
    let root ← mkFreshExprMVar rootType
    let ctx ← context
    let sawConstructorScope ← IO.mkRef false
    let sawProviderRecursor ← IO.mkRef false
    let leakedProviderScope ← IO.mkRef false
    let cfg : SearchConfig := { cfgFor type with
      root := some root.mvarId!, recursionFirst := true
      providers := ← mkProviders #[``wrapFork] }
    let leaf : Leaf := do
      let value ← instantiateMVars root
      let inComposition := (← read).scopedBudgetCheck.isSome
      if containsConst value ``Fork.rec then
        if value.getAppFn.isConstOf ``Subtype.mk && inComposition then sawConstructorScope.set true
        if value.getAppFn.isConstOf ``wrapFork then
          sawProviderRecursor.set true
          if inComposition then leakedProviderScope.set true
      return false
    let initial : Goal := {
      mvar := root.mvarId!, depth := 3, allowExtendedRecursion := true }
    let found ← (search cfg leaf 1 [initial]).run ctx
    unless (← sawConstructorScope.get) && (← sawProviderRecursor.get) do
      throwError "root provenance fixture did not reach both native-induction routes"
    if found || (← leakedProviderScope.get) || (← root.mvarId!.isAssigned) then
      throwError "same-result provider acquired root composition provenance"

-- Permission survives free introductions regardless of names/binder order.
-- Each selected successor uses a different declaration position. The pair
-- fixture additionally requires the existing invertible cases step to retain it.
run_elab do
  let type ← elabType (← `(Nat → Nat → Nat))
  for expected in [
      (← elabTerm (← `(fun first renamed => Nat.succ first)) (some type)),
      (← elabTerm (← `(fun renamed first => Nat.succ first)) (some type))] do
    requireScoped type expected
  let pairType ← elabType (← `((Nat × Nat) → Nat))
  let pairExpected ← elabTerm
    (← `(fun pair : Nat × Nat => match pair with | (chosen, _unused) => Nat.succ chosen))
    (some pairType)
  requireScoped pairType pairExpected

-- A root data goal does not get a prefix merely from a contract. A type-only
-- function still reaches native Fork recursion, but contract-free minors stay
-- outside composition. The preceding positive controls prove depth one can
-- actually reach a scoped Nat body when the bit is available.
run_elab do
  let natType := Lean.mkConst ``Nat
  requireUnscopedRoute natType (cfgFor natType) 1 0 (fun _ => true)
  let type ← elabType (← `(Fork → Nat))
  requireUnscopedRoute type { cfgFor type with contract := none } 2 1
    (fun value => containsConst value ``Fork.rec) (outerRecursion := true)

inductive ClosureBox where
  | mk : (Nat → Nat) → ClosureBox

private def wrapClosure (f : Nat → Nat) : ClosureBox := .mk f

private class Dictionary where
  value : Nat

set_option warn.classDefReducibility false in
private def makeDictionary (n : Nat) : Dictionary := ⟨n⟩

-- The root prefix cannot fill a function-valued ClosureBox argument. Ordinary
-- constructor/provider fallback can introduce it, after which the Nat body
-- has positive depth. If either cont path copied the bit, scoped leaves would
-- become reachable. Separate class/proposition roots reject the prefix before
-- their data-producing ordinary applications, testing witness/dictionary flow.
run_elab do
  let type ← elabType (← `(ClosureBox))
  let cfg : SearchConfig := { cfgFor type with providers := ← mkProviders #[``wrapClosure] }
  for head in [``ClosureBox.mk, ``wrapClosure] do
    requireUnscopedRoute type cfg 2 0 (fun value => value.getAppFn.isConstOf head)
      (incomingComposition := true)
  let witnessType ← elabType (← `(∃ _n : Nat, True))
  requireUnscopedRoute witnessType (cfgFor witnessType) 2 0 (fun _ => true)
    (incomingComposition := true)
  let dictionaryType ← elabType (← `(Dictionary))
  let dictionaryCfg : SearchConfig := {
    cfgFor dictionaryType with providers := ← mkProviders #[``makeDictionary] }
  requireUnscopedRoute dictionaryType dictionaryCfg 2 0
    (fun value => value.getAppFn.isConstOf ``makeDictionary) (incomingComposition := true)

-- Guard leaves identify an actual native split. No earlier composition in this
-- one-goal fixture can contain that split, because filler arguments cannot run
-- search or guards. Both branch children retain depth one, where the positive
-- controls above show a leaked bit would be effective even with zero splits.
run_elab do
  let type ← elabType (← `(Nat → Nat → Nat))
  let cfg : SearchConfig := { cfgFor type with skip := ["7a", "7b", "9c", "residual"] }
  requireUnscopedRoute type cfg 2 1 hasGuard
    (incomingComposition := true) (guards := true)

inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)

-- The original goal deliberately arrives with both flags. Before extended
-- induction it may enter a prefix, but a prefix cannot manufacture Nat.rec or
-- Vec.rec. Thus a scoped recursor leaf would witness permission escaping into
-- an extended minor. Actual recursor leaves must be reached at this same depth.
run_elab do
  for (type, recursor) in [
      ((← elabType (← `(Nat → Nat))), ``Nat.rec),
      ((← elabType (← `(∀ n, Vec Bool n → Nat))), ``Vec.rec)] do
    requireUnscopedRoute type (cfgFor type) 2 1
      (fun value => containsConst value recursor)
      (incomingComposition := true) (outerRecursion := true)

-- A second binary recursive datatype has a data-carrying base and no label on
-- its binary constructor. It needs a different algebra from the tree probe.
-- The selected reference is used only at the leaf, and the resulting closed
-- program is independently kernel checked. This is assisted route coverage.
inductive Rope where
  | atom : Nat → Rope
  | concat : Rope → Rope → Rope

run_elab do
  withoutModifyingState do
    let type ← elabType (← `(Rope → List Nat))
    let expected ← elabTerm (← `(fun rope : Rope =>
      Rope.rec (motive := fun _ => List Nat) (fun n => [n])
        (fun _west _east fromWest fromEast => List.append fromWest fromEast) rope)) (some type)
    let contract := mkLambda `f .default type (Lean.mkConst ``True)
    let rootType ← mkAppM ``Subtype #[contract]
    let root ← mkFreshExprMVar rootType
    let ctx ← context
    let cfg : SearchConfig := { cfgFor type with
      root := some root.mvarId!, recursionFirst := true
      providers := ← mkProviders #[``List.append] }
    let leaf : Leaf := do
      unless (← read).scopedBudgetCheck.isSome do return false
      let value ← instantiateMVars root
      unless containsConst value ``Rope.rec do return false
      let program ← whnfR (← mkAppM ``Subtype.val #[value])
      withNewMCtxDepth (isDefEq program expected)
    let initial : Goal := {
      mvar := root.mvarId!, depth := 3, allowExtendedRecursion := true }
    unless ← (search cfg leaf 1 [initial]).run ctx do
      throwError "second binary recursive datatype never reached its selected scoped algebra"
    let program ← whnfR (← mkAppM ``Subtype.val #[(← instantiateMVars root)])
    requireKernel program type

end Leant2Tests.BranchCompositionIntegration
