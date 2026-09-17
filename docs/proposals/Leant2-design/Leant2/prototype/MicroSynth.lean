import Lean

/-! A deliberately small, bounded Lean-native synthesis experiment.
It is not the complete Leant2 design. Every choice includes the continuation
for all remaining goals, so later contract failures can undo earlier terms. -/

open Lean Meta Elab Tactic
namespace Leant2Micro

/-- Failed alternatives restore the complete MetaM state, not just the goal list. -/
def transaction (action : MetaM Bool) : MetaM Bool := do
  let saved ← saveState
  try
    if ← action then return true
  catch ex =>
    if ex.isInterrupt then throw ex
  saved.restore
  return false

/-- Bounded continuation-aware search. The full pending goal list is one branch. -/
partial def search (root : Expr) (pending : List MVarId)
    (fuel : Nat) (providers : Array Name) : MetaM Bool := do
  match pending with
  | [] => return !(← instantiateMVars root).hasMVar
  | goal :: rest =>
    if ← goal.isAssigned then return ← search root rest fuel providers
    if fuel == 0 then return false
    goal.withContext do
      let target ← goal.getType
      let locals := (← getLCtx).foldl (init := #[]) fun acc decl =>
        if decl.isImplementationDetail then acc else acc.push decl.toExpr
      -- Exact local terms are tried before expanding applications.
      for term in locals do
        if ← transaction do
            unless ← isDefEq (← inferType term) target do return false
            goal.assign term
            search root rest (fuel - 1) providers
          then return true
      let target ← whnf target
      if target.isForall then
        if ← transaction do
            let (_, body) ← goal.intro1
            search root (body :: rest) (fuel - 1) providers
          then return true
      -- Constructors are obtained from the actual environment declaration.
      let mut heads := providers
      if let .const name _ := target.getAppFn then
        if let .inductInfo info ← getConstInfo name then
          heads := info.ctors.toArray ++ heads
      for name in heads do
        if ← transaction do
            let term ← mkConstWithFreshMVarLevels name
            let children ← goal.apply term
              { newGoals := .all, approx := false,
                synthAssignedInstances := false, allowSynthFailures := true }
            search root (children ++ rest) (fuel - 1) providers
          then return true
      for term in locals do
        if ← transaction do
            let children ← goal.apply term
              { newGoals := .all, approx := false,
                synthAssignedInstances := false, allowSynthFailures := true }
            search root (children ++ rest) (fuel - 1) providers
          then return true
      return false

syntax (name := microSynth) "micro_synth" ("[" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| micro_synth $[[$names,*]]?) => do
    let ids := (names.map fun ns => ns.getElems).getD #[]
    let providers ← ids.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
    let goal ← getMainGoal
    let root := mkMVar goal
    for fuel in [1:25] do
      if ← transaction (search root [goal] fuel providers) then
        let term ← instantiateMVars root
        unless !term.hasMVar do throwError "unresolved synthesis metavariables"
        replaceMainGoal []
        return
    throwError "micro_synth: no result within the configured finite search"

end Leant2Micro

open Leant2Micro
set_option autoImplicit false
set_option maxHeartbeats 2000000
universe u v w

-- Pure and dependent functions; no source-language type approximation.
def microIdentity (A : Sort u) : A → A := by micro_synth

def microCompose (A : Sort u) (B : Sort v) (C : Sort w) :
    (B → C) → (A → B) → A → C := by micro_synth

def microDependent (A : Sort u) (B : A → Sort v) :
    ((x : A) → B x) → (x : A) → B x := by micro_synth

def microSigma (A : Type u) (B : A → Type v) (x : A) (y : B x) :
    Sigma B := by micro_synth

-- The callback arguments must themselves be polymorphic functions.
def microRankN (R : Type w)
    (consume : ((A : Type u) → A → A) → R) : R := by micro_synth

def microTwoUniverses (R : Type w)
    (consume : ((A : Type u) → A → A) → ((B : Type v) → B → B) → R) :
    R := by micro_synth

inductive IndexedVec (A : Type u) : Nat → Type u where
  | nil : IndexedVec A 0
  | cons {n : Nat} : A → IndexedVec A n → IndexedVec A (n + 1)

def microIndexed (A : Type u) (n : Nat) (x : A) (xs : IndexedVec A n) :
    IndexedVec A (n + 1) := by micro_synth

def microFin (k n : Nat) (bound : k < n) : Fin n := by micro_synth

-- The first type-correct function returns 11 and fails the second field.
-- A greedy solver of the first field would not recover the second projection.
def microChooseSecond : { f : Nat → Nat → Nat // f 11 29 = 29 } := by
  micro_synth

def microChooseFirst : { f : Nat → Nat → Nat // f 11 29 = 11 } := by
  micro_synth

theorem microConjunction (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by micro_synth

def microStrictImplicit : ⦃A : Type u⦄ → A → A := by micro_synth

class Payload (A : Type u) where
  value : A

def microInstance (A : Type u) [Payload A] : A := by
  micro_synth [Payload.value]

-- Universal contracts, including an exact choice between same-typed dictionaries.
def microChooseSecondAll :
    { f : Nat → Nat → Nat // ∀ x y, f x y = y } := by micro_synth

def microDictionaryChoice :
    { f : Payload Nat → Payload Nat → Nat // ∀ p q, f p q = q.value } := by
  micro_synth [Payload.value]

-- Two manually supplied elimination skeletons with synthesized branch terms.
def transportSkeleton (A : Sort u) (P : A → Sort v) (x y : A)
    (h : x = y) (px : P x) : P y := by
  cases h
  micro_synth

def indexedHeadSkeleton (A : Type u) (n : Nat) (xs : IndexedVec A (n + 1)) :
    A := by
  cases xs with
  | cons x rest => micro_synth

-- Bounded-failure controls, not proofs of general non-inhabitation.
example : True := by
  fail_if_success
    have : False := by micro_synth
  trivial

example (A : Type u) (h : Nonempty A) : True := by
  fail_if_success
    have : A := by micro_synth
  trivial

example : True := by
  fail_if_success
    have : { b : Bool // b = true ∧ b = false } := by micro_synth
  trivial

#eval microChooseSecond.val 11 29
#eval microChooseFirst.val 11 29
#print microRankN
#print microTwoUniverses
#print microChooseSecond
#print axioms microIdentity
#print axioms microCompose
#print axioms microDependent
#print axioms microSigma
#print axioms microRankN
#print axioms microTwoUniverses
#print axioms microIndexed
#print axioms microFin
#print axioms microChooseSecond
#print axioms microChooseFirst
#print axioms microConjunction
#print axioms microStrictImplicit
#print axioms microInstance
#print axioms microChooseSecondAll
#print axioms microDictionaryChoice
#print axioms transportSkeleton
#print axioms indexedHeadSkeleton
#eval Lean.versionString
