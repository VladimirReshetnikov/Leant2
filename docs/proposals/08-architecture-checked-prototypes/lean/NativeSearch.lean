import Lean
open Lean Meta Elab Tactic
namespace Leant2Prototype
partial def search (fuel : Nat) (providers : Array Name) : TacticM Bool := do
  let goals ← (← getGoals).filterM fun g => return !(← g.isAssigned)
  setGoals goals
  if goals.isEmpty then return true
  if fuel == 0 then return false
  let goal := goals.head!
  let rest := goals.tail!
  let tryRule (rule : TacticM (List MVarId)) : TacticM Bool := do
    let saved ← Tactic.saveState
    try
      let children ← rule
      setGoals (children ++ rest)
      if ← search (fuel - 1) providers then return true
    catch _ => pure ()
    saved.restore
    return false
  withMainContext do
    if ← tryRule (do goal.refl; return []) then return true
    if ← tryRule (do let (_, child) ← goal.intro1; return [child]) then return true
    let mut locals : Array FVarId := #[]
    for decl in (← getLCtx) do
      unless decl.isImplementationDetail do
        locals := locals.push decl.fvarId
    for fvar in locals do
      if ← tryRule (goal.apply (mkFVar fvar)) then return true
    for name in providers do
      if ← tryRule (do goal.apply (← mkConstWithFreshMVarLevels name)) then return true
    let target ← whnf (← goal.getType)
    if let .const name _ := target.getAppFn then
      if let some (.inductInfo info) := (← getEnv).find? name then
        for ctor in info.ctors do
          if ← tryRule (do goal.apply (← mkConstWithFreshMVarLevels ctor)) then return true
    for fvar in locals do
      let localType ← whnf (← inferType (mkFVar fvar))
      if let .const name _ := localType.getAppFn then
        if let some (.inductInfo _) := (← getEnv).find? name then
          if ← tryRule (do
              let branches ← goal.cases fvar
              return branches.toList.map (·.mvarId)) then return true
    return false
elab "leant2_core" "[" ids:ident,* "]" : tactic => do
  let providers := ids.getElems.map (·.getId)
  let original ← Tactic.saveState
  for fuel in [1:18] do
    original.restore
    if ← search fuel providers then return
  original.restore
  throwError "leant2_core: no solution within the rule-step bound (not a refutation)"
universe u v w
def identity {α : Sort u} : α → α := by leant2_core []
def compose {α : Sort u} {β : Sort v} {γ : Sort w} :
    (β → γ) → (α → β) → α → γ := by leant2_core []
def swap {α : Type u} {β : Type v} : α × β → β × α := by leant2_core []
def distribute {α : Type u} {β : Type v} {γ : Type w} :
    α × (β ⊕ γ) → (α × β) ⊕ (α × γ) := by leant2_core []
def dependentPair {α : Type u} {β : α → Type v} :
    (a : α) → β a → Sigma β := by leant2_core []
def singleton {α : Type u} (a : α) : {xs : List α // xs = [a]} := by leant2_core []
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)
def vectorHead {α : Type u} {n : Nat} : Vec α (n + 1) → α := by leant2_core []
def preserveDictionary {α : Type u} (d : Inhabited α) : α := by leant2_core []
def polymorphicArgument (k : ((α : Type) → α → α) → Nat) :
    {n : Nat // n = k (fun _ x => x)} := by leant2_core []
def double (n : Nat) : {m : Nat // m = n + n} := by leant2_core [Nat.add]
def dependentApply {α : Type u} {β : α → Type v} :
    ((a : α) → β a) → (a : α) → β a := by leant2_core []
theorem identity_spec (x : Nat) : identity x = x := rfl
theorem compose_spec (f g : Nat → Nat) (x : Nat) : compose f g x = f (g x) := rfl
theorem singleton_spec {α : Type u} (a : α) : (singleton a).val = [a] := (singleton a).property
theorem dictionary_spec : preserveDictionary (α := Nat) ⟨37⟩ = 37 := rfl
theorem polymorphic_spec (k : ((α : Type) → α → α) → Nat) :
    (polymorphicArgument k).val = k (fun _ x => x) := (polymorphicArgument k).property
example : True := by
  fail_if_success have : False := by leant2_core []
  trivial
example : True := by
  fail_if_success have : (α : Type) → α := by leant2_core []
  trivial
example : True := by
  fail_if_success have : {n : Nat // False} := by leant2_core []
  trivial
#print axioms double
#print axioms dependentApply
#print axioms identity
#print axioms compose
#print axioms swap
#print axioms distribute
#print axioms dependentPair
#print axioms singleton
#print axioms vectorHead
#print axioms preserveDictionary
#print axioms polymorphicArgument
#print axioms singleton_spec
#print axioms polymorphic_spec
#print polymorphicArgument
#print vectorHead
#eval Lean.versionString
end Leant2Prototype
