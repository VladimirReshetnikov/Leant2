import Leant2.Frontend.Sketch.ChildProjection
import Leant2.Frontend.Sketch.Run

/-! Deterministic exact-case regression. No public synthesis run occurs.
The checker below is copied from frozen case038 with all 36 observations.
No reference/oracle implementation is imported or provided to search. -/

set_option linter.unusedVariables false
namespace BehaviorPartial
universe u v
abbrev CList (A : Type u) := ∀ R : Type, (A → R → R) → R → R
abbrev CMaybe (A : Type u) := ∀ R : Type, R → (A → R) → R
abbrev CEither (A : Type u) (B : Type v) := ∀ R : Type, (A → R) → (B → R) → R
abbrev CPair (A : Type u) (B : Type v) := ∀ R : Type, (A → B → R) → R
abbrev CBool := ∀ R : Type, R → R → R
def enc {A : Type} (xs : List A) : CList A := fun _ step zero => xs.foldr step zero
def dec {A : Type} (xs : CList A) : List A := xs (List A) List.cons []
def maybe {A : Type} (m : Option A) : CMaybe A := fun _ zero some => m.elim zero some
def either {A B : Type} (e : Sum A B) : CEither A B := fun _ onLeft onRight => e.elim onLeft onRight
def bool (flag : Bool) : CBool := fun _ yes no => if flag then yes else no
def pair {A B : Type} (p : A × B) : CPair A B := fun _ k => k p.1 p.2
def decPair {A B : Type} (p : CPair A B) : A × B := p (A × B) Prod.mk
def dict {A B : Type} (xs : List (A × B)) : CList (CPair A B) := fun _ step zero => xs.foldr (fun p rest => step (fun _ k => k p.1 p.2) rest) zero
end BehaviorPartial
def BehaviorPartial.check_foldl1 (f : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0))))) : Bool := ((((((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((-99) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((-99) : Int))) && ((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)))) && (((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((4) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((39) : Int))) && ((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((0) : Int)) && ((((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((13) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((99) : Int)))))) && ((((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((99) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int))) && ((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((4) : Int)))) && (((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((39) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((0) : Int))) && ((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((13) : Int)) && ((((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([] : (List Bool))))) == (false : Bool)) && (((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false] : (List Bool))))) == (false : Bool))))))) && (((((((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([true] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false,true,false] : (List Bool))))) == (false : Bool))) && ((((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false] : (List Bool))))) == (false : Bool)))) && (((((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([true] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false,true,false] : (List Bool))))) == (false : Bool))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(-99)] : (List Int))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(-99)] : (List Int))) && (((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))))))) && ((((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))) && (((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(2),(3),(4)] : (List Int)))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(3),(2),(1),(4)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(99)] : (List Int))))) && (((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(99)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int)))) && ((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))) && ((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(2),(3),(4)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(3),(2),(1),(4)] : (List Int)))))))))

namespace Leant2Tests.SketchChildFoldl1
open Lean Meta Elab
open Lean.Elab.Term hiding mkConst
open Leant2 Leant2.Frontend.Sketch

private structure Snapshot where
  coreState : Core.State
  metaState : Meta.State
  termState : Term.State

private def snapshot : TermElabM Snapshot := do
  return {
    coreState := ← getThe Core.State
    metaState := ← getThe Meta.State
    termState := ← getThe Term.State }

private def restore (before : Snapshot) : TermElabM Unit := do
  modifyThe Meta.State fun _ => before.metaState
  modifyThe Core.State fun _ => before.coreState
  modifyThe Term.State fun _ => before.termState

private unsafe def assertRestored (before : Snapshot) : TermElabM Unit := do
  let after ← snapshot
  unless ptrEq before.coreState after.coreState && ptrEq before.metaState after.metaState &&
      ptrEq before.termState after.termState do
    throwError "foldl1 child: exact Core/Meta/Term state was not restored"

private def catchAll (action : TermElabM α) : TermElabM (Except Exception α) := do
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch exception => return .error exception

private def pass (name : String) : TermElabM Unit := IO.println s!"PASS foldl1-child-{name}"

private def replay (value type : Expr) : MetaM Unit := withLCtx {} #[] do
  unless ChildProjection.closed value && ChildProjection.closed type do
    throwError "foldl1 child: open independent replay input"
  let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let .ok axioms ← kernelCheckAndAudit `Leant2Tests.SketchChildFoldl1 value type levels false
    | throwError "foldl1 child: independent safe kernel replay failed"
  unless axioms.isEmpty do throwError "foldl1 child: replay used an axiom"

private def originalQuery : TermElabM Query := do
  let target ← elabType (← `((∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0))))))
  let contract ← elabTerm (← `(fun f : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0)))) => BehaviorPartial.check_foldl1 (f) = true)) none
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let contract ← instantiateMVars contract
  unless ChildProjection.closed target && ChildProjection.closed contract do
    throwError "foldl1 child: exact original query is not frozen"
  return {
    target
    contract := some contract
    providers := #[]
    profile := .strictConstructive
    budgetMs := 5000
    maxCandidates := 1
    graceMs := 0 }

private def sketch : TermElabM (TSyntax `term) :=
  `(fun (A : Type) (d : A) (combine : A → A → A) =>
    (fun (step : A → (Option A → A) → Option A → A) (init : Option A → A)
         (xs : ∀ R : Type, (A → R → R) → R → R) =>
      xs (Option A → A) step init none) ?step ?init)

private def owned (prepared : Prepared) (name : Name) : MetaM OwnedHole := do
  let some hole := prepared.holes.find? (·.spec.sourceName.eraseMacroScopes == name)
    | throwError "foldl1 child: missing original owned hole {name}"
  return hole

private def localNamed (hole : OwnedHole) (name : Name) : MetaM Expr := do
  for entry in hole.declaration.lctx do
    if entry.userName.eraseMacroScopes == name then return entry.toExpr
  throwError "foldl1 child: missing original local {name}"

private structure Branch where
  step : OwnedHole
  init : OwnedHole
  child : MVarId
  childDecl : MetavarDecl
  A : Expr
  d : Expr
  combine : Expr
  x : Expr
  next : Expr
  state : Expr

/-- Use real native intro/apply, never a fabricated partial lambda assignment. -/
private def makeBranch (prepared : Prepared) (projection : ChildProjection.State)
    (goodInit : Bool := false) : MetaM Branch := do
  let step ← owned prepared `step
  let init ← owned prepared `init
  let A ← localNamed step `A
  let d ← localNamed step `d
  let combine ← localNamed step `combine
  unless init.declaration.lctx.getFVars == #[A, d, combine] do
    throwError "foldl1 child: original initializer uses a different telescope"
  let (initArg, initBody) ← init.pending.intro1P
  if goodInit then
    initBody.withContext do
      let identity ← withLocalDeclD `item A fun item => mkLambdaFVars #[item] item
      let value ← mkAppM ``Option.elim #[mkFVar initArg, d, identity]
      ChildProjection.typedAssign initBody value
  else
    ChildProjection.typedAssign initBody d
  let (x, first) ← step.pending.intro1P
  let (next, second) ← first.intro1P
  let (state, body) ← second.intro1P
  let children ← body.apply (mkFVar next)
    { newGoals := .all, synthAssignedInstances := false, allowSynthFailures := true }
  let [child] := children | throwError "foldl1 child: next application did not create exactly one child"
  let declaration ← child.getDecl
  -- Native apply uses forallMetaTelescopeReducing's default .natural kind.
  -- Keep that actual kind: retagging would manufacture prototype eligibility.
  unless declaration.kind.isNatural && declaration.depth == prepared.depth &&
      !projection.beforeSearch.decls.contains child &&
      !(prepared.holes.any (·.pending == child)) do
    throwError "foldl1 child: apply child lost freshness, ownership, kind or depth"
  let args := #[A, d, combine, mkFVar x, mkFVar next, mkFVar state]
  unless declaration.lctx.getFVars == args do
    throwError "foldl1 child: child telescope differs from original A/d/combine/x/next/state"
  child.withContext do
    unless ← isDefEq (← child.getType) (mkApp (mkConst ``Option [.zero]) A) do
      throwError "foldl1 child: next argument changed its dependent Option A type"
  unless !(← child.isAssignedOrDelayedAssigned) do
    throwError "foldl1 child: child is already complete"
  return {
    step
    init
    child
    childDecl := declaration
    A
    d
    combine
    x := mkFVar x
    next := mkFVar next
    state := mkFVar state }

private def requireRefuted (report : ObservationReport) : MetaM Unit := do
  unless report.statuses.size == 36 && report.refuted &&
      report.statuses[0]! == some .satisfied && report.statuses[1]! == some .satisfied &&
      report.statuses[2]! == some .refuted &&
      (report.statuses.toList.drop 3).all Option.isNone do
    throwError "foldl1 child: wrong original observation refutation: {repr report.statuses}"

private def requireStuck (report : ObservationReport) : MetaM Unit := do
  unless report.statuses.size == 36 && !report.refuted &&
      report.statuses[0]! == some .satisfied && report.statuses[1]! == some .satisfied &&
      report.statuses[2]! == some .stuck do
    throwError "foldl1 child: original singleton observation should remain stuck: {repr report.statuses}"

private structure Captured where
  step : Expr
  program : Expr

/-- Return only closed abstractions. No callback placeholder escapes. -/
private def capture (projection : ChildProjection.State) (branch : Branch) : MetaM Captured :=
  ChildProjection.withPartialView projection branch.step.pending fun view => do
    let some child := view.childInterfaces[0]?
      | throwError "foldl1 child: missing extracted child interface"
    unless view.wholeParameters.size == 2 && view.childParameters.size == 1 &&
        view.childInterfaces.size == 1 && child.id == branch.child &&
        child.arguments == branch.childDecl.lctx.getFVars do
      throwError "foldl1 child: extracted child/interface identity changed"
    let step ← mkLambdaFVars view.parameters view.partialClosure (usedOnly := false)
    let program ← mkLambdaFVars view.parameters view.program (usedOnly := false)
    unless ChildProjection.closed step && ChildProjection.closed program do
      throwError "foldl1 child: captured projection retained a free placeholder"
    replay step (← inferType step)
    replay program (← inferType program)
    return { step, program }

private def ownedClosure (item : Projection.HoleInterface) : MetaM Expr :=
  withLCtx item.owned.declaration.lctx item.owned.declaration.localInstances do
    let value ← instantiateMVars (mkMVar item.owned.pending)
    unless ChildProjection.frozen value do throwError "foldl1 child: owned body still open"
    let value ← mkLambdaFVars item.arguments value (usedOnly := false) (usedLetOnly := false)
    let value ← instantiateMVars value
    replay value item.closedType
    return value

private def childValue (branch : Branch) (index : Nat) : MetaM Expr := branch.child.withContext do
  let someValue (value : Expr) := mkApp2 (mkConst ``Option.some [.zero]) branch.A value
  match index with
  | 0 => return mkApp (mkConst ``Option.none [.zero]) branch.A
  | 1 => return someValue branch.x
  | 2 => return branch.state
  | 3 => return someValue branch.d
  | 4 => return someValue (mkApp branch.next branch.state)
  | _ => throwError "foldl1 child: unknown correspondence completion"

private def searchContext : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private unsafe def fixture : TermElabM Unit := do
  let query ← originalQuery
  let contract := query.contract.get!
  let observations ← mkObservations contract query.target
  unless observations.size == 36 && query.providers.isEmpty do
    throwError "foldl1 child: original contract/provider inventory changed"
  let nextExample ← elabTerm (← `(fun o : Option Nat => o.elim 100 (fun n => n + 1))) none
  synthesizeSyntheticMVarsNoPostponing
  let nextExample ← instantiateMVars nextExample
  let sketchSyntax ← sketch
  let before ← snapshot
  discard <| withPreparedSketch query.target sketchSyntax fun prepared => do
    unless prepared.holes.map (·.spec.sourceName.eraseMacroScopes) == #[`step, `init] &&
        prepared.holes.all (fun h => h.declaration.lctx.getFVars.size == 3) do
      throwError "foldl1 child: exact original holes/scopes changed"
    let initial ← snapshot
    let projection ← ChildProjection.build prepared
    assertRestored initial
    pass "exact-original-query-and-build"
    let branch ← makeBranch prepared projection
    let partialState ← snapshot
    pass "native-intro-apply-fresh-option-child"
    let ordinary ← Projection.observe projection.base query.profile contract observations
    assertRestored partialState
    requireStuck ordinary
    Projection.withView projection.base fun _ _ completed => do
      unless completed == #[false, true] do
        throwError "foldl1 child: existing observer exposed the partial step"
    assertRestored partialState
    pass "whole-owned-step-remains-opaque"
    let result ← ChildProjection.observe projection branch.step.pending query.profile contract observations
    assertRestored partialState
    unless result.enhanced do throwError "foldl1 child: enhanced path fell back silently"
    requireRefuted result.report
    unless !(← branch.child.isAssignedOrDelayedAssigned) do
      throwError "foldl1 child: refutation completed the open child"
    pass "enhanced-refutes-before-option-completion"
    let captured ← capture projection branch
    assertRestored partialState
    let some stepInterface := projection.base.interfaces[0]?
      | throwError "foldl1 child: missing original step interface"
    let some initInterface := projection.base.interfaces[1]?
      | throwError "foldl1 child: missing original initializer interface"
    for index in [:5] do
      restore partialState
      let value ← childValue branch index
      let childClosure ← branch.child.withContext do
        let closure ← mkLambdaFVars branch.childDecl.lctx.getFVars value
          (usedOnly := false) (usedLetOnly := false)
        instantiateMVars closure
      replay childClosure (← inferType childClosure)
      ChildProjection.typedAssign branch.child value
      let nativeStep ← ownedClosure stepInterface
      let nativeInit ← ownedClosure initInterface
      let nativeProgram ← instantiateMVars prepared.expression
      let arguments := #[nativeStep, nativeInit, childClosure]
      let projectedStep := mkAppN captured.step arguments
      let projectedProgram := mkAppN captured.program arguments
      replay projectedStep stepInterface.closedType
      replay projectedProgram query.target
      replay nativeProgram query.target
      unless (← isDefEq projectedStep nativeStep) && (← isDefEq projectedProgram nativeProgram) do
        throwError "foldl1 child: native/parameter substitution mismatch at completion {index}"
      -- Whole-program agreement alone would be vacuous under constant init.
      let chosenNextArgs := #[mkConst ``Nat, mkNatLit 7, mkConst ``Nat.add,
        mkNatLit 4, nextExample, mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Nat) (mkNatLit 9)]
      let expected := #[100, 5, 10, 8, 11][index]!
      let stepObservation := mkAppN projectedStep chosenNextArgs
      unless ← isDefEq stepObservation (mkNatLit expected) do
        throwError "foldl1 child: step observation erased or permuted a dependency at {index}"
      replay (← mkEqRefl (mkNatLit expected)) (← mkEq stepObservation (mkNatLit expected))
      let completeState ← snapshot
      let report ← Projection.observe projection.base query.profile contract observations
      assertRestored completeState
      requireRefuted report
      -- This is the complete original checker, not just the selected singleton.
      let decision ← mkDecide (mkApp contract nativeProgram)
      let falseType ← mkEq decision (mkConst ``Bool.false)
      replay (← mkEqRefl (mkConst ``Bool.false)) falseType
      pass s!"native-step-and-original-query-correspondence-{index}"
    restore partialState
    let ctx ← searchContext
    let entered ← IO.mkRef false
    let leafReached ← IO.mkRef false
    let proof ← mkFreshExprMVar (contract.beta #[prepared.expression])
    let root ← mkFreshExprMVar (← mkAppM ``Subtype #[contract])
    root.mvarId!.assign (mkApp4 (mkConst ``Subtype.mk [← getLevel query.target])
      query.target contract prepared.expression proof)
    let cfg : SearchConfig := {
      providers := #[], profile := query.profile, contract := some contract,
      root := some root.mvarId!, skip := ["residual"]
      partialPruner := some fun goal => do
        unless goal == branch.child do return false
        unless !(← branch.child.isAssignedOrDelayedAssigned) do
          throwError "foldl1 child: actual callback ran after child completion"
        let active ← read
        let some report ← ChildProjection.tryObservePartial? projection branch.step.pending
            query.profile contract observations (check := checkDeadline.run active)
          | throwError "foldl1 child: deferred callback did not validate the refutation"
        requireRefuted report
        entered.set true
        return true }
    let seeded ← snapshot
    let stopped ← (alternative <| search cfg (do leafReached.set true; return true) cfg.maxSplits
      [{ mvar := branch.child, depth := 1 }, { mvar := proof.mvarId!, depth := 1 }]).run ctx
    unless !stopped && (← entered.get) && !(← leafReached.get) do
      throwError "foldl1 child: actual search callback did not reject before the leaf"
    -- Native alternative restores its documented backtrackable state; the
    -- projection itself is required above to restore full state identity.
    unless ptrEq seeded.metaState.mctx (← getMCtx) &&
        !(← branch.child.isAssignedOrDelayedAssigned) && !(← proof.mvarId!.isAssigned) do
      throwError "foldl1 child: child callback/search leaked branch assignments"
    pass "actual-search-child-callback-before-completion"
    restore partialState
    let token ← IO.CancelToken.new
    let reached ← IO.mkRef false
    let cancelled ← catchAll <| withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
      ChildProjection.withPartialView projection branch.step.pending fun _ => do
        reached.set true
        discard <| mkFreshExprMVar (mkConst ``Nat)
        discard <| mkFreshLevelMVar
        logInfo "foldl1 child speculative cancellation diagnostic"
        token.set
        Core.checkInterrupted
    assertRestored partialState
    let .error error := cancelled | throwError "foldl1 child: cancellation was swallowed"
    unless (← reached.get) && error.isInterrupt do
      throwError "foldl1 child: cancellation identity or injection point changed"
    pass "view-cancellation-restores-original-partial-state"
    restore initial
    let recovery ← makeBranch prepared projection (goodInit := true)
    let recoveryState ← snapshot
    let result ← ChildProjection.observe projection recovery.step.pending query.profile contract observations
    assertRestored recoveryState
    unless result.enhanced do throwError "foldl1 child: recovery did not exercise enhanced projection"
    requireStuck result.report
    let deferred ← ChildProjection.tryObservePartial? projection recovery.step.pending
      query.profile contract observations
    assertRestored recoveryState
    unless deferred.isNone do
      throwError "foldl1 child: deferred recovery exposed an inconclusive report"
    unless !(← recovery.child.isAssignedOrDelayedAssigned) do
      throwError "foldl1 child: recovery filled its child"
    pass "rollback-correct-init-remains-stuck"
  assertRestored before
  pass "preparation-restores-after-entire-fixture"
  IO.println "FOLDL1 CHILD FIXTURE COMPLETE"

run_elab do fixture

end Leant2Tests.SketchChildFoldl1
