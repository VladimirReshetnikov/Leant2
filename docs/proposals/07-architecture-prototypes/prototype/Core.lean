import Lean

set_option autoImplicit false
set_option linter.unusedTactic false

open Lean Meta Elab Tactic

namespace Leant2Prototype

/-- Bounded continuation search. Every alternative includes *all* remaining
    goals, so a failed dependent sibling can backtrack into an earlier witness. -/
partial def solve (fuel : Nat) (goals : List MVarId)
    (splitUsed : List FVarId := []) : MetaM Bool := do
  let goals ← goals.filterM fun g => return !(← g.isAssigned)
  if goals.isEmpty then return true
  if fuel == 0 then return false
  let g := goals.head!
  let rest := goals.tail!
  g.withContext do
    let attempt (step : MetaM (List MVarId))
        (used : List FVarId := splitUsed) : MetaM Bool := do
      let saved ← saveState
      try
        let children ← step
        if ← solve (fuel - 1) (children ++ rest) used then return true
      catch _ => pure ()
      saved.restore
      return false
    let target ← whnf (← g.getType)
    if target.isForall then
      if ← attempt (do let (_, child) ← g.intro1; pure [child]) then return true
    if ← attempt (do g.refl; pure []) then return true
    let context ← getLCtx
    for localDecl in context do
      if !localDecl.isImplementationDetail then
        if ← attempt (g.apply (mkFVar localDecl.fvarId) {newGoals := .all}) then
          return true
    if let .const name _ := target.getAppFn then
      if let some (.inductInfo info) := (← getEnv).find? name then
        for ctor in info.ctors do
          if ← attempt (do
              let e ← mkConstWithFreshMVarLevels ctor
              g.apply e {newGoals := .all}) then return true
    -- Only non-recursive, non-indexed shapes are automatically split in this
    -- intentionally small prototype. Indexed recursion is tested as a sketch.
    for localDecl in context do
      if !localDecl.isImplementationDetail && !splitUsed.contains localDecl.fvarId then
        let ty ← whnf localDecl.type
        if let .const name _ := ty.getAppFn then
          if let some (.inductInfo info) := (← getEnv).find? name then
            if !info.isRec && info.numIndices == 0 then
              if ← attempt (do
                  let branches ← g.cases localDecl.fvarId
                  pure (branches.toList.map (·.mvarId)))
                  (localDecl.fvarId :: splitUsed) then return true
    return false

/-- Experimental tactic, not a production Leant2 implementation. -/
elab "leant2_core" : tactic => do
  let goals ← getGoals
  let saved ← saveState
  if ← solve 30 goals then
    setGoals []
  else
    saved.restore
    throwError "Leant2 prototype exhausted its bounded search"

universe u v w
def ident (A : Sort u) : A → A := by leant2_core
def compose (A : Sort u) (B : Sort v) (C : Sort w) :
    (B → C) → (A → B) → A → C := by leant2_core
def swap (A : Type u) (B : Type v) : A × B → B × A := by leant2_core
def sumElim (A : Type u) (B : Type v) (C : Type w) :
    (A → C) → (B → C) → Sum A B → C := by leant2_core
def depApply (A : Sort u) (B : A → Sort v) :
    ((x : A) → B x) → (x : A) → B x := by leant2_core
def sigmaRepack (A : Type u) (B : A → Type v) :
    (x : A) → B x → Sigma B := by leant2_core
def dependentChoice : {n : Nat // n = 1} := by leant2_core
def twoUniverses (A : Type u) (B : Type v) :
    ((X : Type u) → X → X) → ((Y : Type v) → Y → Y) →
    A → B → A × B := by leant2_core
def higherRank (A : Type u) :
    (((X : Type u) → X → X) → A) → A := by leant2_core
def absurdElim (A : Sort u) : False → A := by leant2_core
theorem actualFalseControl : True := by
  fail_if_success have : False := by leant2_core
  trivial
theorem noWitnessControl : True := by
  fail_if_success have : {n : Nat // n = n + 1} := by leant2_core
  trivial

def dependentProjection (A : Type u) (B : A → Type v) :
    (s : Sigma B) → B s.1 := by leant2_core
def strictIdentity : ⦃A : Type u⦄ → A → A := by leant2_core
class Token (A : Type u) where
  payload : A
def fromInstance (A : Type u) [Token A] : A := by leant2_core
theorem propEliminationControl (A : Type u) : True := by
  fail_if_success have : Nonempty A → A := by leant2_core
  trivial
theorem uniformEmpty : (∀ A : Type, A) → False := by
  intro f
  exact Empty.elim (f Empty)

inductive Vec (A : Type u) : Nat → Type u
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)

variable {A : Type u} {B : Type v} {n : Nat}

def vecMap (f : A → B) : {n : Nat} → Vec A n → Vec B n
  | _, .nil => by leant2_core
  | _, .cons x xs =>
      let tail := vecMap f xs
      by leant2_core

def Vec.toList : {n : Nat} → Vec A n → List A
  | _, .nil => []
  | _, .cons x xs => x :: xs.toList

theorem vecMap_spec (f : A → B) (xs : Vec A n) :
    (vecMap f xs).toList = xs.toList.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [vecMap, Vec.toList, ih]

theorem allTests :
    ident Nat 7 = 7 ∧
    compose Nat Nat Nat (fun x => x + 1) (fun x => x * 2) 3 = 7 ∧
    swap Nat Bool (4, true) = (true, 4) ∧
    dependentChoice.val = 1 := by decide

#print axioms ident
#print axioms swap
#print axioms sumElim
#print axioms depApply
#print axioms sigmaRepack
#print axioms dependentProjection
#print axioms strictIdentity
#print axioms fromInstance
#print axioms uniformEmpty
#print axioms vecMap
#print axioms actualFalseControl
#print axioms noWitnessControl
#print axioms propEliminationControl
#print axioms allTests
#print axioms vecMap_spec
#print axioms dependentChoice
#print axioms compose
#print axioms twoUniverses
#print axioms higherRank
#print axioms absurdElim
#eval Lean.versionString

end Leant2Prototype
