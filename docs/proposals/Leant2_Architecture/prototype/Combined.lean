import Lean
open Lean Meta Elab Tactic
namespace Leant2Prototype
def search : Nat → List MVarId → Array Name → MetaM Bool
  | _, [], _ => pure true
  | 0, _ :: _, _ => pure false
  | fuel + 1, goal :: rest, providers => do
      if ← goal.isAssigned then
        return ← search fuel rest providers
      goal.withContext do
        let checkpoint ← saveState
        let attempt (action : MetaM (List MVarId)) : MetaM Bool := do
          checkpoint.restore
          try
            let children ← action
            if ← search fuel (children ++ rest) providers then
              return true
          catch _ => pure ()
          checkpoint.restore
          return false
        let target ← whnf (← goal.getType)
        if target.isForall then
          return ← attempt do
            let (_, child) ← goal.intro1
            return [child]
        if ← attempt do goal.refl; return [] then return true
        for decl in ← getLCtx do
          unless decl.isImplementationDetail do
            if ← attempt (goal.apply decl.toExpr) then return true
        for name in providers do
          if ← attempt do
            goal.apply (← mkConstWithFreshMVarLevels name)
          then return true
        match target.getAppFn with
        | .const name _ =>
          match ← getConstInfo name with
          | .inductInfo info =>
            for ctor in info.ctors do
              if ← attempt do
                goal.apply (← mkConstWithFreshMVarLevels ctor)
              then return true
          | _ => pure ()
        | _ => pure ()
        checkpoint.restore
        return false
elab "leant2_core" : tactic => do
  unless ← search 24 (← getGoals) #[] do
    throwError "Leant2 prototype: bounded search exhausted (not a refutation)"
  setGoals []
elab "leant2_small" : tactic => do
  unless ← search 6 (← getGoals) #[] do
    throwError "Leant2 prototype: bounded search exhausted (not a refutation)"
  setGoals []
elab "leant2_with " names:ident,* : tactic => do
  let providers := names.getElems.map (·.getId)
  for name in providers do
    discard <| getConstInfo name
  unless ← search 32 (← getGoals) providers do
    throwError "Leant2 prototype: bounded search exhausted (not a refutation)"
  setGoals []
universe u v w
def identity : (α : Sort u) → α → α := by leant2_core
def compose {α : Sort u} {β : Sort v} {γ : Sort w} :
    (β → γ) → (α → β) → α → γ := by leant2_core
def sComb {α : Sort u} {β : Sort v} {γ : Sort w} :
    (α → β → γ) → (α → β) → α → γ := by leant2_core
def swap {α : Type u} {β : Type v} : α → β → β × α := by leant2_core
def dependentApply {α : Sort u} {β : α → Sort v} :
    ((x : α) → β x) → (x : α) → β x := by leant2_core
def sigmaPack {α : Type u} {β : α → Type v} :
    (x : α) → β x → Sigma β := by leant2_core
def rankTwo : ((α : Type) → α → α) → Nat → Nat := by leant2_core
def successorSpec : {f : Nat → Nat // ∀ n, f n = n + 1} := by
  leant2_with Nat.succ
def chooseOne : {n : Nat // n = 1} := by leant2_core
theorem identity_behavior (n : Nat) : identity Nat n = n := rfl
theorem successor_behavior (n : Nat) : successorSpec.val n = n + 1 :=
  successorSpec.property n
example : True := by
  fail_if_success have : (α : Type) → (β : Type) → α → β := by leant2_small
  trivial
#print axioms identity
#print axioms compose
#print axioms sComb
#print axioms swap
#print axioms dependentApply
#print axioms sigmaPack
#print axioms rankTwo
#print axioms successorSpec
#print axioms chooseOne
#print axioms identity_behavior
#print axioms successor_behavior
#eval successorSpec.val 12
#eval chooseOne.val
#eval Lean.versionString
end Leant2Prototype
open Lean Meta Elab Tactic
namespace Leant2Prototype
universe u v
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)
def vcons {α : Type u} {n : Nat} : α → Vec α n → Vec α (n + 1) := by
  leant2_core
def vecMap {α : Type u} {β : Type v} (f : α → β) {n : Nat}
    (xs : Vec α n) : Vec β n :=
  match xs with
  | .nil => by leant2_core
  | .cons a xs => by
    have ih := vecMap f xs
    leant2_core
def vecToList {α : Type u} {n : Nat} : Vec α n → List α
  | .nil => []
  | .cons a xs => a :: vecToList xs
theorem vecMap_behavior {α : Type u} {β : Type v} (f : α → β) {n : Nat}
    (xs : Vec α n) : vecToList (vecMap f xs) = (vecToList xs).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [vecMap, vecToList, ih]
def transport {α : Sort u} (β : α → Sort v) {a b : α}
    (h : a = b) (x : β a) : β b := by
  cases h
  leant2_core
def inheritedDefault {α : Type u} [Inhabited α] : α := by
  leant2_with Inhabited.default
structure Payload where
  value : Nat
def chooseRight (left right : Payload) : {p : Payload // p.value = right.value} := by
  leant2_core
def rankTwoSpec :
    {h : ((α : Type) → α → α) → Nat → Nat // ∀ f n, h f n = f Nat n} := by
  leant2_core
def higherRank : (((α : Type) → α → α) → Nat) → Nat := by leant2_core
theorem noPolyCast : ((α : Type) → (β : Type) → α → β) → False := by
  intro f
  exact Empty.elim (f Unit Empty ())
#print axioms vcons
#print axioms vecMap
#print axioms vecMap_behavior
#print axioms transport
#print axioms inheritedDefault
#print axioms chooseRight
#print axioms rankTwoSpec
#print axioms higherRank
#print axioms noPolyCast
#eval (chooseRight ⟨2⟩ ⟨9⟩).val.value
#eval vecToList (vecMap (fun n => n + 1) (.cons 2 (.cons 3 .nil)))
end Leant2Prototype
