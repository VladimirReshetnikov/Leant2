import Lean

open Lean Meta Elab Tactic

/-!
A deliberately small, bounded Leant2 experiment, not the proposed full engine.
It searches native Lean goals, uses transactional continuation backtracking,
and discovers constructors and case splits from the actual environment.
It has no external solver, library index, recursion discovery, or negative oracle.
-/
namespace Leant2Mini

private def attempt (action : MetaM Bool) : MetaM Bool := do
  let saved ← saveState
  try
    if ← action then return true
  catch error =>
    saved.restore
    if error.isInterrupt || error.isMaxHeartbeat then throw error
  saved.restore
  return false

private def constructors (type : Expr) : MetaM (List Name) := do
  let type ← whnf type
  match type.getAppFn with
  | .const name _ =>
    match (← getEnv).find? name with
    | some (.inductInfo info) => return info.ctors
    | _ => return []
  | _ => return []

/-- Fuel bounds a complete continuation path, not total work or elapsed time.
    A successful choice must solve every remaining goal before it commits. -/
private partial def solve (fuel splits : Nat) (goals : List MVarId) : MetaM Bool := do
  match goals with
  | [] => return true
  | goal :: rest =>
    if ← goal.isAssigned then return ← solve fuel splits rest
    match fuel with
    | 0 => return false
    | fuel + 1 => goal.withContext do
      let target ← whnf (← goal.getType)
      if target.isForall then
        return ← attempt do
          let (_, body) ← goal.intro1
          solve fuel splits (body :: rest)
      if ← attempt do
        goal.refl
        solve fuel splits rest
      then return true
      let mut locals : Array FVarId := #[]
      for decl in (← getLCtx) do
        if !decl.isImplementationDetail then
          locals := locals.push decl.fvarId
      for localId in locals do
        if ← attempt do
          let children ← goal.apply (mkFVar localId) { newGoals := .all }
          solve fuel splits (children ++ rest)
        then return true
      -- Projection proposals retain the exact dictionary/structure value.
      -- They must precede recursive constructor growth (e.g. Nat.succ).
      for localId in locals do
        let localType ← whnf (← inferType (mkFVar localId))
        if let .const name _ := localType.getAppFn then
          if let some info := getStructureInfo? (← getEnv) name then
            for index in [:info.fieldNames.size] do
              if ← attempt do
                let projection := Expr.proj name index (mkFVar localId)
                let children ← goal.apply projection { newGoals := .all }
                solve fuel splits (children ++ rest)
              then return true
      for name in (← constructors target) do
        if ← attempt do
          let constructor ← mkConstWithFreshMVarLevels name
          let children ← goal.apply constructor { newGoals := .all }
          solve fuel splits (children ++ rest)
        then return true
      if splits > 0 then
        for localId in locals do
          let localType ← whnf (← inferType (mkFVar localId))
          -- Arithmetic induction is outside this experiment. Avoid unhelpful
          -- repeated splitting of arbitrary natural-number parameters.
          if !localType.isAppOf ``Nat && !(← constructors localType).isEmpty then
            if ← attempt do
              let branches ← goal.cases localId
              let children := branches.toList.map (fun branch => branch.mvarId)
              solve fuel (splits - 1) (children ++ rest)
            then return true
      return false

elab "leant2_mini" : tactic => do
  let saved ← saveState
  let goals ← getGoals
  if ← solve 64 3 goals then
    setGoals []
  else
    saved.restore
    throwError "Leant2Mini: bounded search found no term (not a non-inhabitation result)"

end Leant2Mini

universe u v w
namespace Leant2Experiments

def identitySort (α : Sort u) : α → α := by leant2_mini

def composeDependent {α : Sort u} {P Q R : α → Sort v}
    (f : ∀ x, Q x → R x) (g : ∀ x, P x → Q x) :
    ∀ x, P x → R x := by leant2_mini

def applicationDependent {α : Sort u} {β : α → Sort v}
    (f : ∀ x, β x) (x : α) : β x := by leant2_mini

def usePolymorphic (consume : (∀ α : Type u, α → α) → Nat) : Nat := by
  leant2_mini

def useTwoUniverses {R : Type w}
    (consume : (∀ α : Type u, α → α) → (∀ β : Type v, β → β) → R) : R := by
  leant2_mini

def swapSum {α : Type u} {β : Type v} : Sum α β → Sum β α := by leant2_mini

def swapProd {α : Type u} {β : Type v} : α × β → β × α := by leant2_mini

def dependentWitness (a b : Nat) : {n : Nat // n = b} := by leant2_mini

-- This checks the chosen computational witness, not merely its type.
theorem dependentWitness_value (a b : Nat) : (dependentWitness a b).val = b := by rfl

def transport {α : Type u} {P : α → Type v} (a b : α)
    (equality : a = b) (value : P a) : P b := by leant2_mini

inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

def vectorHead {α : Type u} {n : Nat} : Vec α (n + 1) → α := by leant2_mini

-- Recursion skeleton selected by hand; only its branch bodies are synthesized.
def vectorReplicate {α : Type u} (n : Nat) (a : α) : Vec α n := by
  induction n with
  | zero => leant2_mini
  | succ n smaller => leant2_mini

class Token (α : Type u) where
  value : α

def chooseDictionary (first second : Token Nat) : {n : Nat // n = second.value} := by
  leant2_mini

theorem chooseDictionary_value (first second : Token Nat) :
    (chooseDictionary first second).val = second.value := by rfl

-- Expected failures are asserted, not left as failing declarations or sorries.
example : True := by
  fail_if_success have impossible : False := by leant2_mini
  trivial

example : True := by
  fail_if_success have impossible : (∀ α : Type, α) := by leant2_mini
  trivial

#print axioms identitySort
#print axioms composeDependent
#print axioms applicationDependent
#print axioms usePolymorphic
#print axioms useTwoUniverses
#print axioms swapSum
#print axioms swapProd
#print axioms dependentWitness
#print axioms dependentWitness_value
#print axioms transport
#print axioms vectorHead
#print axioms vectorReplicate
#print axioms chooseDictionary
#print axioms chooseDictionary_value
#eval Lean.versionString
end Leant2Experiments
