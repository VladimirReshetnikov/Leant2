import Lean
open Lean Meta Elab Tactic
namespace Leant2Prototype
def transaction (action : MetaM Bool) : MetaM Bool := do
  let saved ← saveState
  try
    if ← action then
      return true
  catch ex =>
    match ex with
    | .internal .. => throw ex
    | _ => pure ()
  saved.restore
  return false
partial def search (providers : Array Name) (fuel splits : Nat)
    (goals : List MVarId) : MetaM Bool := do
  match goals with
  | [] => return true
  | goal :: rest =>
    if ← goal.isAssigned then
      return ← search providers fuel splits rest
    if fuel == 0 then
      return false
    goal.withContext do
      let target ← whnf (← goal.getType)
      if target.isForall then
        return ← transaction do
          let (_, next) ← goal.intro1
          search providers (fuel - 1) splits (next :: rest)
      let mut locals := #[]
      for decl in ← getLCtx do
        unless decl.isImplementationDetail do
          locals := locals.push decl.toExpr
      let majors := locals
      for term in majors do
        let localType ← whnf (← inferType term)
        if let .const typeName _ := localType.getAppFn then
          if let some info := getStructureInfo? (← getEnv) typeName then
            for index in [:info.fieldNames.size] do
              locals := locals.push (mkProj typeName index term)
      for term in locals do
        if ← transaction do
          let subgoals ← goal.apply term { newGoals := .all, synthAssignedInstances := false }
          search providers (fuel - 1) splits (subgoals ++ rest)
        then return true
      let mut names := providers
      if let .const name _ := target.getAppFn then
        if let .inductInfo info ← getConstInfo name then
          names := names ++ info.ctors.toArray
      names := names.push ``Eq.refl
      for name in names do
        if ← transaction do
          let term ← mkConstWithFreshMVarLevels name
          let subgoals ← goal.apply term { newGoals := .all, synthAssignedInstances := false }
          search providers (fuel - 1) splits (subgoals ++ rest)
        then return true
      if splits > 0 then
        for term in majors do
          if ← transaction do
            let branches ← goal.cases term.fvarId!
            let subgoals := branches.toList.map (·.mvarId)
            search providers (fuel - 1) (splits - 1) (subgoals ++ rest)
          then return true
      return false
elab "leant2_core" "[" names:ident,* "]" "fuel" fuel:num
    "splits" splits:num : tactic => do
  let providers ← names.getElems.mapM fun name =>
    realizeGlobalConstNoOverloadWithInfo name
  let goal ← getMainGoal
  let saved ← saveState
  try
    let found ← search providers fuel.getNat splits.getNat [goal]
    unless found do
      throwError "leant2_core: bounded search exhausted (not non-inhabitation)"
    let result ← instantiateMVars (mkMVar goal)
    if result.hasExprMVar || result.hasLevelMVar then
      throwError "leant2_core: unresolved metavariables in proposed result"
    replaceMainGoal []
  catch ex =>
    saved.restore
    throw ex
end Leant2Prototype
open Lean Meta Elab Tactic
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
universe u v w
namespace Leant2Tests
def identityNative (A : Sort u) : A → A := by
  leant2_core [] fuel 8 splits 0
def composeNative (A : Sort u) (B : Sort v) (C : Sort w) :
    (B → C) → (A → B) → A → C := by
  leant2_core [] fuel 18 splits 0
def substitutionNative (A B C : Type) :
    (A → B → C) → (A → B) → A → C := by
  leant2_core [] fuel 18 splits 0
def productNative (A : Type u) (B : Type v) : A → B → A × B := by
  leant2_core [] fuel 12 splits 0
def productSwapNative (A : Type u) (B : Type v) : A × B → B × A := by
  leant2_core [] fuel 12 splits 1
def sumSwapNative (A : Type u) (B : Type v) : Sum A B → Sum B A := by
  leant2_core [] fuel 14 splits 1
def emptyEliminationNative (A : Sort u) : Empty → A := by
  leant2_core [] fuel 8 splits 1
def dependentComposeNative (A : Sort u) (B : A → Sort v)
    (C : (a : A) → B a → Sort w) :
    (g : (a : A) → (b : B a) → C a b) → (f : (a : A) → B a) →
    (a : A) → C a (f a) := by
  leant2_core [] fuel 18 splits 0
def sigmaNative : (n : Nat) → Fin (n + 1) → (n : Nat) × Fin (n + 1) := by
  leant2_core [] fuel 12 splits 0
def sigmaProjectionNative (p : (n : Nat) × Fin (n + 1)) : Fin (p.1 + 1) := by
  leant2_core [Sigma.snd] fuel 10 splits 0
inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons : A → Vec A n → Vec A (n + 1)
def indexedHeadNative (A : Type u) (n : Nat) : Vec A (n + 1) → A := by
  leant2_core [] fuel 10 splits 1
def transportNative (A : Type u) (n m : Nat) : n = m → Vec A n → Vec A m := by
  leant2_core [] fuel 12 splits 1
def rankTwoNative : ((∀ A : Type, A → A) → Nat) → Nat := by
  leant2_core [] fuel 12 splits 0
def twoUniversesNative (A : Type u) (B : Type v) :
    ((∀ X : Type u, X → X) → A) → ((∀ Y : Type v, Y → Y) → B) → A × B := by
  leant2_core [] fuel 22 splits 0
def contextualDefaultNative (A : Type u) [Inhabited A] : A := by
  leant2_core [Inhabited.default] fuel 8 splits 0
def dictionaryValue (d : Inhabited Nat) : Nat := @Inhabited.default Nat d
def dictionarySelectionNative :
    { f : Inhabited Nat → Inhabited Nat → Nat // f ⟨11⟩ ⟨29⟩ = 29 } := by
  leant2_core [dictionaryValue] fuel 14 splits 0
def exampleConstrainedNative :
    { f : ∀ A : Type, A → A → A // f Nat 11 29 = 29 } := by
  leant2_core [] fuel 18 splits 0
def universallyConstrainedNative :
    { f : ∀ A : Type, A → A → A // ∀ (A : Type) (x y : A), f A x y = y } := by
  leant2_core [] fuel 22 splits 0
def successorConstrainedNative (n : Nat) : { m : Nat // m = n + 1 } := by
  leant2_core [] fuel 14 splits 0
theorem conjunctionNative (P Q : Prop) : P → Q → P ∧ Q := by
  leant2_core [] fuel 10 splits 0
theorem disjunctionSwapNative (P Q : Prop) : P ∨ Q → Q ∨ P := by
  leant2_core [] fuel 14 splits 1
theorem rejectsFalse : True := by
  fail_if_success (have bad : False := by leant2_core [] fuel 6 splits 0)
  exact True.intro
theorem rejectsFalseContract : True := by
  fail_if_success
    have bad : { b : Bool // False } := by leant2_core [] fuel 6 splits 0
  exact True.intro
theorem rejectsScopeEscape : True := by
  fail_if_success
    have bad : ∀ A : Type, (A → A) → A := by leant2_core [] fuel 6 splits 0
  exact True.intro
theorem exhaustionIsNotRefutation : True := by
  fail_if_success (have inhabited : Nat := by leant2_core [] fuel 0 splits 0)
  exact True.intro
example (A : Sort u) (x : A) : identityNative A x = x := rfl
example : exampleConstrainedNative.val Nat 11 29 = 29 :=
  exampleConstrainedNative.property
example (A : Type) (x y : A) : universallyConstrainedNative.val A x y = y :=
  universallyConstrainedNative.property A x y
example (n : Nat) : (successorConstrainedNative n).val = n + 1 :=
  (successorConstrainedNative n).property
example : productSwapNative Nat Bool (17, true) = (true, 17) := rfl
example : sumSwapNative Nat Bool (.inl 17) = .inr 17 := rfl
example : indexedHeadNative Nat Nat.zero (.cons 17 .nil) = 17 := rfl
example : dictionarySelectionNative.val ⟨11⟩ ⟨29⟩ = 29 :=
  dictionarySelectionNative.property
#eval exampleConstrainedNative.val Nat 11 29
#eval dictionarySelectionNative.val ⟨11⟩ ⟨29⟩
#eval (successorConstrainedNative 41).val
#eval Lean.versionString
run_cmd do
  let names := #[``identityNative, ``composeNative, ``substitutionNative,
    ``productNative, ``productSwapNative, ``sumSwapNative, ``emptyEliminationNative,
    ``dependentComposeNative, ``sigmaNative, ``sigmaProjectionNative,
    ``indexedHeadNative, ``transportNative, ``rankTwoNative, ``twoUniversesNative,
    ``contextualDefaultNative, ``dictionarySelectionNative, ``exampleConstrainedNative,
    ``universallyConstrainedNative, ``successorConstrainedNative,
    ``conjunctionNative, ``disjunctionSwapNative, ``rejectsFalse,
    ``rejectsFalseContract, ``rejectsScopeEscape, ``exhaustionIsNotRefutation]
  for name in names do
    let axioms ← collectAxioms name
    logInfo m!"AXIOMS {name}: {axioms}"
    unless axioms.all (fun ax => #[``propext, ``Quot.sound, ``Classical.choice].contains ax) do
      throwError "{name}: unexpected axioms {axioms}"
  logInfo m!"LEANT2_AUDIT: {names.size} declarations; standard-axiom audit passed"
end Leant2Tests
