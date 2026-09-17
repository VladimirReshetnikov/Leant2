import Lean

/-!
# Leant2 native-search experiment

This is a deliberately small, bounded prototype, not the proposed full system.
It searches native Lean goals, backtracking over the WHOLE remaining goal forest.
Its only global providers are constructors of the current target. It does not
search the environment, invent recursive definitions, or implement CEGIS.
-/
open Lean Meta Elab Tactic
namespace Leant2Demo

/-- Atomic rollback includes assignments made while solving later siblings. -/
partial def search (fuel : Nat) (goals : List MVarId) : MetaM Bool := do
  match goals with
  | [] => return true
  | goal :: rest =>
    if (← goal.isAssigned) then return ← search fuel rest
    if fuel == 0 then return false
    goal.withContext do
      let attempt (action : MetaM (List MVarId)) : MetaM Bool := do
        let saved ← Meta.saveState
        try
          let children ← action
          if ← search (fuel - 1) (children ++ rest) then return true
        catch _ => pure ()
        saved.restore
        return false
      if ← attempt (do goal.refl; return []) then return true
      let target ← whnf (← goal.getType)
      if target.isForall then
        if ← attempt (do let (_, child) ← goal.intro1P; return [child]) then
          return true
      let context ← getLCtx
      for localDecl in context do
        if !localDecl.isImplementationDetail then
          if ← attempt (goal.apply localDecl.toExpr { newGoals := .all }) then
            return true
      if let .const name _ := target.getAppFn then
        if let .inductInfo info ← getConstInfo name then
          for ctor in info.ctors do
            if ← attempt (do
                let term ← mkConstWithFreshMVarLevels ctor
                goal.apply term { newGoals := .all }) then
              return true
      for localDecl in context do
        if !localDecl.isImplementationDetail then
          let localType ← whnf localDecl.type
          if let .const name _ := localType.getAppFn then
            if let .inductInfo _ ← getConstInfo name then
              if ← attempt (do
                  let branches ← goal.cases localDecl.fvarId
                  return branches.toList.map (·.mvarId)) then
                return true
      return false

/-- Run the bounded native search; failure is explicitly inconclusive. -/
elab "leant2_demo" : tactic => do
  let goals ← getGoals
  let saved ← saveState
  if ← search 80 goals then
    setGoals []
  else
    saved.restore
    throwError "Leant2 demo: no solution within the bounded grammar (inconclusive)"

/-- Regression for restoring a successful unification before exploring a sibling. -/
elab "rollback_probe" : tactic => do
  let saved ← Meta.saveState
  let hole ← mkFreshExprMVar (mkConst ``Nat)
  let checkpoint ← Meta.saveState
  unless ← isDefEq hole (mkNatLit 7) do throwError "probe assignment failed"
  checkpoint.restore
  unless (← instantiateMVars hole).isMVar do throwError "assignment leaked"
  saved.restore
  evalTactic (← `(tactic| trivial))

universe u v w

def identity {A : Sort u} : A → A := by leant2_demo

def compose {A : Sort u} {B : Sort v} {C : Sort w} :
    (B → C) → (A → B) → A → C := by leant2_demo

def substitute {A : Sort u} {B : Sort v} {C : Sort w} :
    (A → B → C) → (A → B) → A → C := by leant2_demo

def swap {A : Type u} {B : Type v} : A × B → B × A := by leant2_demo

def mapSum {A : Type u} {B : Type v} {C : Type w} :
    (A → C) → Sum A B → Sum C B := by leant2_demo

def dependentApply {A : Sort u} {B : A → Sort v} :
    (∀ a, B a) → (a : A) → B a := by leant2_demo

def dependentPair {A : Type u} {B : A → Type v} :
    (a : A) → B a → Sigma B := by leant2_demo

def dependentProjection {A : Type u} {B : A → Type v} :
    (p : Sigma B) → B p.1 := by leant2_demo

def transport {A : Sort u} {B : A → Sort v} :
    (a b : A) → a = b → B a → B b := by leant2_demo

def rankN (k : (∀ A : Type, A → A) → Nat) : Nat := by leant2_demo

def mixedUniverses
    (k : (∀ A : Type u, A → A) → (∀ B : Type v, B → B) → Nat) : Nat := by
  leant2_demo

/-- The first value alternative is wrong; the later equality forces backtracking. -/
def chooseSecond : {f : (∀ A : Type, A → A → A) // f Nat 11 29 = 29} := by
  leant2_demo

theorem chooseSecond_all (A : Type) (a b : A) : chooseSecond.val A a b = b := by
  rfl

structure Tagged (A : Type u) where
  value : A

def exactDictionary {A : Type u} (first second : Tagged A) :
    {a : A // a = second.value} := by leant2_demo

theorem emptyElim {A : Sort u} : Empty → A := by leant2_demo

theorem rollback : True := by rollback_probe

theorem noFalse : True := by
  fail_if_success have impossible : False := by leant2_demo
  trivial

theorem universeNegative : True := by
  fail_if_success have impossible : Type := (∀ A : Type, A → A)
  trivial

/-- An indexed family used to exercise Lean's real dependent eliminator. -/
inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)

def vectorHead {A : Type u} {n : Nat} : Vec A (n + 1) → A := by leant2_demo

/-- The recursion skeleton is supplied by the author; branch bodies are synthesized. -/
def vectorMap {A : Type u} {B : Type v} (f : A → B)
    {n : Nat} (xs : Vec A n) : Vec B n := by
  induction xs with
  | nil => leant2_demo
  | cons head tail mapped => leant2_demo

/-- No List.map provider is supplied. The recursion skeleton is explicit. -/
def listMap {A : Type u} {B : Type v} (f : A → B) (xs : List A) :
    {ys : List B // List.Forall₂ (fun a b => b = f a) xs ys} := by
  induction xs with
  | nil => leant2_demo
  | cons head tail mapped => leant2_demo

theorem listMap_length {A : Type u} {B : Type v} (f : A → B) (xs : List A) :
    (listMap f xs).val.length = xs.length := by
  have h := (listMap f xs).property
  induction h with
  | nil => rfl
  | cons relation tail inductionHypothesis =>
    exact congrArg Nat.succ inductionHypothesis

#eval chooseSecond.val Nat 11 29
#eval chooseSecond.val String "left" "right"
#eval (listMap (fun x : Nat => x + 10) [1, 2, 3]).val
#eval vectorHead (Vec.cons 7 Vec.nil)
#eval Lean.versionString

#print identity
#print compose
#print chooseSecond
#print vectorMap
#print listMap

#print axioms identity
#print axioms compose
#print axioms substitute
#print axioms swap
#print axioms mapSum
#print axioms dependentApply
#print axioms dependentPair
#print axioms dependentProjection
#print axioms transport
#print axioms rankN
#print axioms mixedUniverses
#print axioms chooseSecond
#print axioms chooseSecond_all
#print axioms exactDictionary
#print axioms emptyElim
#print axioms rollback
#print axioms noFalse
#print axioms universeNegative
#print axioms vectorHead
#print axioms vectorMap
#print axioms listMap
#print axioms listMap_length
end Leant2Demo
