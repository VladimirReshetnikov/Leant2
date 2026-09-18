import Lean
import Leant2.Core.Types
import Leant2.Native.Transaction
/-!
# Construction search (unified proposal, Sections 5, 7, 15)

A depth-bounded search over a list of obligations. Every alternative runs
inside a saved state and is committed only if the *whole* continuation
(`children ++ rest`) succeeds: the continuation discipline of Decision 2.2.

Each obligation carries its own remaining depth (the depth of the subterm
that may fill it); children of a rule get one less than their parent, and
sibling obligations keep theirs.

Rules, in the order tried on each goal:
introduction; invertible destructuring of single-constructor locals;
reflexivity; exact locals; type frontier for `Sort`-valued goals; projections
of local structure values as heads; constructors of the target's inductive
head; application of locals (most recent first); bounded case analysis on
multi-constructor locals; head-filtered providers; the proof portfolio on
closed propositions.

The search enumerates candidates: the leaf callback decides whether to stop.
-/
namespace Leant2

open Lean Meta Elab

/-- A provider with the head constant of its conclusion, if the conclusion is
constant-headed; `none` means the conclusion is a variable (or a sort). For
variable-headed providers, `argHeads` lists the constant heads of the
explicit argument types: such a provider is tried only when some local has one
of those heads (demand-directed retrieval, Section 9). -/
structure Provider where
  name : Name
  head : Option Name
  argHeads : Array Name := #[]
  /-- Bypass the demand filter (eliminators such as `Empty.elim`). -/
  always : Bool := false
  deriving Inhabited

structure SearchConfig where
  maxDepth : Nat := 10
  maxSplits : Nat := 2
  /-- Global constants that may be applied. -/
  providers : Array Provider := #[]
  /-- Closed types tried for `Sort`-valued holes. -/
  typeFrontier : Array Expr := #[]
  /-- Allow `Classical.em` and friends as providers. -/
  classical : Bool := false
  /-- Run the proof portfolio on closed propositions. -/
  proofPortfolio : Bool := true

/-- Leaf callback: receives the search state with all goals assigned and
returns `true` to stop the search. -/
abbrev Leaf := SearchM Bool

/-- An obligation with its remaining depth. -/
abbrev Goal := MVarId × Nat

/-- Run one alternative. If it does not stop the search, restore the state so
the next alternative starts from the same point. -/
def alternative (act : SearchM Bool) : SearchM Bool := do
  let saved : Meta.SavedState ← Meta.saveState
  try
    if ← act then return true
  catch e =>
    if isInterrupt e then throw e
  saved.restore
  return false

/-- Names never used as providers even when discovered. -/
def forbiddenProviders : Array Name :=
  #[``sorryAx, ``lcProof, ``lcUnreachable, ``Lean.ofReduceBool, ``Lean.ofReduceNat,
    ``Classical.choice, ``Classical.choose, ``Classical.choose_spec, ``Classical.propDecidable]

/-- Compute the conclusion head of a constant. -/
def mkProvider (n : Name) : MetaM (Option Provider) := do
  let some ci := (← getEnv).find? n | return none
  let ty ← instantiateMVars ci.type
  let (concl, argHeads) ← forallTelescopeReducing ty fun xs b => do
    let b ← whnfR b
    let mut hs : Array Name := #[]
    for x in xs do
      let xt ← whnfR (← inferType x)
      if let .const c _ := xt.getAppFn then hs := hs.push c
    return (b.getAppFn, hs)
  let head := match concl with
    | .const c _ => some c
    | _ => none
  return some { name := n, head, argHeads }

def mkProviders (ns : Array Name) (always := false) : MetaM (Array Provider) := do
  let mut out := #[]
  for n in ns do
    if forbiddenProviders.contains n then continue
    if let some p ← mkProvider n then out := out.push { p with always }
  return out

/-- Constants the classical lane adds. `absurd` is deliberately absent: an
arbitrary `Prop` hole explodes the search. -/
def classicalProviders : MetaM (Array Provider) :=
  mkProviders #[``Classical.em, ``Classical.byContradiction, ``False.elim] (always := true)

private def isTypeSort (e : Expr) : MetaM Bool := do
  match ← whnfR e with
  | .sort _ => return true
  | _ => return false

/-- Try to close a *closed* `Prop` goal (no metavariables, no locals) with a
small tactic portfolio. Messages the tactics log are discarded. -/
def proofPortfolio (g : MVarId) : SearchM Bool := do
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar || t.hasFVar then return false
  -- `False` has no proof and `True` is a constructor: not worth a tactic run
  if t.isConstOf ``False || t.isConstOf ``True then return false
  unless ← isProp t do return false
  charge fun l => { l with proofAttempts := l.proofAttempts + 1 }
  let savedMsgs := (← getThe Core.State).messages
  let r ← Term.TermElabM.run' do
    let stx ← `(tactic| first | rfl | decide | (simp) | omega)
    try
      let gs ← Tactic.run g (Tactic.evalTactic stx)
      return gs.isEmpty
    catch _ => return false
  modifyThe Core.State fun s => { s with messages := savedMsgs }
  return r

private def localsToTry : MetaM (Array LocalDecl) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    out := out.push d
  return out.reverse -- most recent first

private def applyCfg : ApplyConfig :=
  { newGoals := .all, synthAssignedInstances := false, allowSynthFailures := true }

/-- Inductive info of a local's (whnf) type, if any. -/
private def inductiveOfLocal (decl : LocalDecl) : MetaM (Option InductiveVal) := do
  let dty ← whnfR (← instantiateMVars decl.type)
  if let .const iname _ := dty.getAppFn then
    if let some (.inductInfo ii) := (← getEnv).find? iname then return some ii
  return none

/-- A local whose type is a non-recursive single-constructor inductive without
indices can be destructured without loss (Prod, And, Iff, Sigma, Subtype...). -/
private def isInvertible (ii : InductiveVal) : Bool :=
  ii.ctors.length == 1 && !ii.isRec && ii.numIndices == 0

/-- The search over a goal list. -/
partial def search (cfg : SearchConfig) (leaf : Leaf) (splits : Nat) :
    List Goal → SearchM Bool
  | [] => leaf
  | (g, depth) :: rest => do
    if ← g.isAssigned then return ← search cfg leaf splits rest
    if depth = 0 then return false
    checkDeadline
    charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
    g.withContext do
    let target ← instantiateMVars (← g.getType)
    let targetW ← whnfR target
    let d := depth - 1
    let cont (children : List MVarId) : SearchM Bool :=
      search cfg leaf splits (children.map (·, d) ++ rest)
    let applyHead (e : Expr) : SearchM Bool := alternative do
      charge fun l => { l with unifications := l.unifications + 1 }
      let children ← g.apply e applyCfg
      cont children
    -- 1. introduction (default transparency, so that `Not` and similar unfold).
    -- Invertible, hence free of depth cost.
    if (← whnf target).isForall then
      return ← alternative do
        let (_, g') ← g.intro1P
        search cfg leaf splits ((g', depth) :: rest)
    let locals ← localsToTry
    -- 2. invertible destructuring (does not consume depth or splits)
    for decl in locals do
      if let some ii ← inductiveOfLocal decl then
        if isInvertible ii then
          if ← alternative (do
              let subgoals ← g.cases decl.fvarId
              search cfg leaf splits (subgoals.toList.map ((·.mvarId, depth)) ++ rest)) then
            return true
          -- destructuring failed (e.g. Prop into data): fall through
    -- 3. reflexivity
    if targetW.isAppOfArity ``Eq 3 then
      if ← alternative (do g.refl; cont []) then return true
    let targetIsSort ← isTypeSort target
    -- 4. exact locals
    for decl in locals do
      if ← alternative (do
          charge fun l => { l with unifications := l.unifications + 1 }
          if ← isDefEq (← inferType decl.toExpr) target then
            g.assign decl.toExpr
            cont []
          else return false) then return true
    if targetIsSort then
      for t in cfg.typeFrontier do
        if ← alternative (do
            if ← isDefEq (← inferType t) target then
              g.assign t; cont []
            else return false) then return true
    -- 5. bounded case analysis on multi-constructor locals
    if splits > 0 && !targetIsSort then
      for decl in locals do
        if let some ii ← inductiveOfLocal decl then
          if isInvertible ii || ii.name == ``Nat then continue
          if ← alternative (do
              let subgoals ← g.cases decl.fvarId
              search cfg leaf (splits - 1) (subgoals.toList.map ((·.mvarId, d)) ++ rest)) then
            return true
    -- 6. projections of local structure values, applied as heads
    for decl in locals do
      let dty ← whnfR (← instantiateMVars decl.type)
      if let .const sname _ := dty.getAppFn then
        if isStructure (← getEnv) sname then
          for field in getStructureFields (← getEnv) sname do
            let p? ← attempt (mkProjection decl.toExpr field)
            if let some p := p? then
              if ← applyHead p then return true
    -- 6. constructors of the target's inductive head
    let targetHead : Option Name := match targetW.getAppFn with
      | .const c _ => some c
      | _ => none
    if let some iname := targetHead then
      if let some (.inductInfo ii) := (← getEnv).find? iname then
        for c in ii.ctors do
          if ← applyHead (← mkConstWithFreshMVarLevels c) then return true
    if !targetIsSort then
      -- 7. application of locals (default transparency: `¬p` is a function)
      for decl in locals do
        let dty ← whnf (← instantiateMVars decl.type)
        unless dty.isForall do continue
        if ← applyHead decl.toExpr then return true
      -- 9. providers, head-filtered: a constant-headed conclusion must match the
      -- target head; a variable-headed provider needs a local demanding one of its
      -- argument heads
      let provs ← if cfg.classical then do pure (cfg.providers ++ (← classicalProviders))
                  else pure cfg.providers
      let localHeads ← locals.filterMapM fun decl => do
        let dty ← whnfR (← instantiateMVars decl.type)
        return match dty.getAppFn with | .const c _ => some c | _ => none
      for p in provs do
        match p.head with
        | some h =>
          match targetHead with
          | some th => if h != th then continue
          | none => continue
        | none =>
          if !p.always && !p.argHeads.isEmpty && !p.argHeads.any localHeads.contains then continue
        if ← applyHead (← mkConstWithFreshMVarLevels p.name) then return true
      -- 10. proof portfolio on closed propositions
      if cfg.proofPortfolio then
        if ← alternative (do if ← proofPortfolio g then cont [] else return false) then
          return true
    return false

end Leant2
