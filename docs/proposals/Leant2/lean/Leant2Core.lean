import Lean

/-!
# Leant2: a deliberately small executable research prototype

Native dependent expressions, fresh universes, whole-continuation backtracking,
constructor search, and bounded case analysis. This is not the complete design.
No environment-wide provider discovery, recursion invention, completeness claim,
or production admission audit is implemented here. Final declarations are checked
by Lean in the ordinary way. The tests include an explicit axiom audit.
-/

open Lean Meta Elab Tactic

namespace Leant2Prototype

/-- Roll back the complete MetaM state unless the whole continuation succeeds.
Internal exceptions (including interruption/resource failures) propagate. -/
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

/-- All remaining obligations belong to one AND continuation. In particular,
solving a value hole is not committed before its behavioral proof succeeds. -/
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
      -- Projections must be applied to a known major premise before matching.
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

/-- Research syntax: provider names, then derivation and case-analysis bounds.
Fully qualified provider names are accepted, and the elaborator resolves names
in the caller's namespace before entering the MetaM search. -/
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
