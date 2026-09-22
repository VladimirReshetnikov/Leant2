import Leant2

/-!
Focused checks of the finite native branch filler and its continuation boundary.
Direct-filler tests use a leaf observer as an oracle, never a provider or pruning
rule. Public tree synthesis remains a separate unassisted acceptance obligation.
-/
namespace Leant2Tests.BranchComposition

open Lean Meta Elab Term Leant2

private def context : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def observeAll (action : MetaM α) : MetaM (Except Exception α) := do
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch ex => return .error ex

private def config (type : Expr) (names : Array Name) : MetaM SearchConfig := do
  return {
    contract := some (mkLambda `candidate .default type (mkConst ``True))
    providers := ← mkProviders names }

private def natType : Expr := mkConst ``Nat
private def listType : Expr := mkApp (mkConst ``List [0]) natType
private def cons (x xs : Expr) : Expr := mkApp3 (mkConst ``List.cons [0]) natType x xs
private def append (xs ys : Expr) : Expr := mkApp3 (mkConst ``List.append [0]) natType xs ys
private def succ (x : Expr) : Expr := mkApp (mkConst ``Nat.succ) x

private def withLists (next : Expr → Expr → Expr → Array LocalDecl → MetaM Unit) : MetaM Unit :=
  withLocalDeclD `leftResult listType fun left =>
    withLocalDeclD `label natType fun label =>
      withLocalDeclD `rightResult listType fun right => do
        -- Deliberately explicit order, independent of user-facing local names.
        let locals ← #[left, label, right].mapM fun x => x.fvarId!.getDecl
        next left label right locals

private def isWanted (goal : Expr) (wanted : Expr) : SearchM Bool := do
  let value ← instantiateMVars goal
  return ← withNewMCtxDepth (isDefEq value wanted)

run_meta do
  for (depth, expected) in [(1, false), (2, true)] do
    withoutModifyingState do
      withLists fun left label right locals => do
        let goal ← mkFreshExprMVar listType
        let cfg ← config listType #[``List.append]
        let ctx ← context
        let stats ← IO.mkRef ({} : Leant2.BranchComposition.Stats)
        let wanted := append left (cons label right)
        let found ← (Leant2.BranchComposition.run cfg goal.mvarId! depth locals
          (isWanted goal wanted) {} (some stats)).run ctx
        unless found == expected do throwError "ordinary depth / two-head branch mismatch"
        if found then
          let program ← mkLambdaFVars #[left, label, right] (← instantiateMVars goal)
          let .ok _ ← gate .strictConstructive program (← inferType program) none
            | throwError "completed open branch failed its closed native gate"
          unless (← stats.get).entered[1]! do throwError "two-head witness never entered grade two"
        else if ← goal.mvarId!.isAssigned then
          throwError "failed depth-one prefix leaked an assignment"

run_meta do
  -- Three total heads remain outside the grammar even with enough ordinary depth.
  withoutModifyingState do
    withLists fun left label right locals => do
      let goal ← mkFreshExprMVar listType
      let cfg ← config listType #[``List.append]
      let ctx ← context
      let wanted := append (cons label left) (cons label right)
      if ← (Leant2.BranchComposition.run cfg goal.mvarId! 4 locals (isWanted goal wanted)).run ctx then
        throwError "head credits were duplicated across sibling arguments"
      if ← goal.mvarId!.isAssigned then throwError "three-head miss leaked goal assignment"

run_meta do
  -- Withholding append must not be bypassed by constructors or local function application.
  withoutModifyingState do
    withLists fun left label right locals => do
      let functionType ← mkArrow listType (← mkArrow listType listType)
      withLocalDeclD `consumedAppend functionType fun forbidden => do
        let goal ← mkFreshExprMVar listType
        let ctx ← context
        let cfg ← config listType #[]
        let locals := locals.push (← forbidden.fvarId!.getDecl)
        let wanted := mkApp2 forbidden left (cons label right)
        if ← (Leant2.BranchComposition.run cfg goal.mvarId! 2 locals (isWanted goal wanted)).run ctx then
          throwError "filler applied a local function head outside its grammar"
        if ← goal.mvarId!.isAssigned then throwError "withheld-provider miss leaked assignment"

run_meta do
  let providers ← mkProviders (curatedProviders ++ #[])
  let eligible := providers.filter fun p => p.head == some ``List && p.arity <= 2
  unless eligible.size >= 4 && eligible[3]!.name == ``List.append do
    throwError "fresh curated provider prefix no longer contains append in its audited position"

structure Box where
  value : Nat

class MissingDictionary where
  value : Nat

def boxed [Inhabited Nat] (x : Nat) : Box := ⟨x⟩
def boxedMissing [MissingDictionary] (x : Nat) : Box := ⟨x⟩

run_meta do
  for (provider, expected) in [(``boxed, true), (``boxedMissing, false)] do
    withoutModifyingState do
      withLocalDeclD `value natType fun value => do
        let goal ← mkFreshExprMVar (mkConst ``Box)
        let cfg ← config (mkConst ``Box) #[provider]
        let ctx ← context
        let found ← (Leant2.BranchComposition.run cfg goal.mvarId! 1
          #[(← value.fvarId!.getDecl)] (do
            let term ← instantiateMVars goal
            return term.getAppFn.isConstOf provider)).run ctx
        unless found == expected do throwError "native resolved/unresolved dictionary policy changed"

run_meta do
  -- A crowded grade one hits its one-callback reservation, then grade two can stop.
  withoutModifyingState do
    withLocalDeclD `n natType fun n => do
      let goal ← mkFreshExprMVar natType
      let cfg ← config natType #[``Nat.succ]
      let ctx ← context
      let stats ← IO.mkRef ({} : Leant2.BranchComposition.Stats)
      let found ← (Leant2.BranchComposition.run cfg goal.mvarId! 2
        #[(← n.fvarId!.getDecl)] (isWanted goal (succ (succ n)))
        { callbacks := 4 } (some stats)).run ctx
      let stats ← stats.get
      unless found && stats.entered[1]! && stats.grades[0]!.callbacks == 1 do
        throwError "grade one starved the reserved two-head grade"
      unless stats.total.callbacks <= 4 && stats.total.attempts <= 2048 do
        throwError "grade budgets were restarted instead of shared"

run_meta do
  -- The fourth total callback is admitted and may finish; checking >=4
  -- continuously immediately after its admission would fail this test.
  withoutModifyingState do
    withLocalDeclD `n natType fun n => do
      let goal ← mkFreshExprMVar natType
      let cfg ← config natType #[``Nat.succ]
      let ctx ← context
      let calls ← IO.mkRef 0
      let stats ← IO.mkRef ({} : Leant2.BranchComposition.Stats)
      let next : SearchM Bool := do
        calls.modify (· + 1)
        return (← calls.get) == 4
      let found ← (Leant2.BranchComposition.run cfg goal.mvarId! 2
        #[(← n.fvarId!.getDecl)] next { callbacks := 4 } (some stats)).run ctx
      unless found && (← calls.get) == 4 && (← stats.get).total.callbacks == 4 do
        throwError "last admitted callback was refused or allowed cap was exceeded"

run_meta do
  -- Native assignments made before a rejected original continuation restore;
  -- global charges and callback observations remain nonrefundable.
  withoutModifyingState do
    withLocalDeclD `n natType fun n => do
      let goal ← mkFreshExprMVar natType
      let sibling ← mkFreshExprMVar (mkConst ``Bool)
      let level ← mkFreshLevelMVar
      let before ← getMCtx
      let cfg ← config natType #[``Nat.succ]
      let ctx ← context
      let visits ← IO.mkRef 0
      let next : SearchM Bool := do
        unless ← goal.mvarId!.isAssigned do throwError "continuation ran before branch assignment"
        visits.modify (· + 1)
        sibling.mvarId!.assign (mkConst ``Bool.true)
        assignLevelMVar level.mvarId! .zero
        discard <| mkFreshExprMVar natType
        return false
      if ← (Leant2.BranchComposition.run cfg goal.mvarId! 2
          #[(← n.fvarId!.getDecl)] next { callbacks := 4 }).run ctx then
        throwError "false continuation stopped enumeration"
      if (← visits.get) == 0 || (← ctx.ledger.get).unifications == 0 then
        throwError "rollback fixture did not execute charged native work"
      if (← goal.mvarId!.isAssigned) || (← sibling.mvarId!.isAssigned) ||
          (getLevelMVarAssignmentExp (← getMCtx) level.mvarId!).isSome ||
          (← getMCtx).mvarCounter != before.mvarCounter then
        throwError "failed branch did not restore sibling/universe/metavariable state"

run_meta do
  -- A successful stop remains successful after both local and inherited quota
  -- expiry. The accepted marker is external state and must not cause fallback.
  withoutModifyingState do
    withLocalDeclD `n natType fun n => do
      let goal ← mkFreshExprMVar natType
      let cfg ← config natType #[``Nat.succ]
      let ctx ← context
      let accepted ← IO.mkRef 0
      let fallback ← IO.mkRef false
      let next : SearchM Bool := do
        accepted.modify (· + 1)
        charge fun l => { l with ruleApplications := l.ruleApplications + 10000 }
        return true
      let found ← (withScopedBudget (do return (← accepted.get) != 0) fun _ => do
        let found ← Leant2.BranchComposition.run cfg goal.mvarId! 1
          #[(← n.fvarId!.getDecl)] next { continuationRules := 4 }
        unless found do fallback.set true
        return found).run ctx
      unless found && (← accepted.get) == 1 && !(← fallback.get) do
        throwError "quota changed an externally recorded success stop into fallback"

run_meta do
  -- On false, an inherited scope's token must escape the inner grade and
  -- reach its owner. It must not be consumed as a local grade-two opportunity.
  withoutModifyingState do
    withLocalDeclD `n natType fun n => do
      let goal ← mkFreshExprMVar natType
      let cfg ← config natType #[``Nat.succ]
      let ctx ← context
      let outerExpired ← IO.mkRef false
      let escapedInner ← IO.mkRef false
      let found ← (withScopedBudget outerExpired.get fun _ => do
        discard <| Leant2.BranchComposition.run cfg goal.mvarId! 1
          #[(← n.fvarId!.getDecl)] (do outerExpired.set true; return false)
        escapedInner.set true
        return false).run ctx
      if found || (← escapedInner.get) || (← goal.mvarId!.isAssigned) then
        throwError "inner grade swallowed an inherited quota or leaked its assignment"

run_meta do
  -- Real cancellation wins over simultaneous quota expiry on both callback outcomes.
  for success in [false, true] do
    withoutModifyingState do
      withLocalDeclD `n natType fun n => do
        let goal ← mkFreshExprMVar natType
        let cfg ← config natType #[``Nat.succ]
        let ctx ← context
        let token ← IO.CancelToken.new
        let accepted ← IO.mkRef 0
        let result ← observeAll <| withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
          (Leant2.BranchComposition.run cfg goal.mvarId! 1 #[(← n.fvarId!.getDecl)] (do
            if success then accepted.modify (· + 1)
            charge fun l => { l with ruleApplications := l.ruleApplications + 10000 }
            token.set
            return success) { callbacks := 4, continuationRules := 4 }).run ctx
        let .error ex := result | throwError "real cancellation was swallowed by heuristic scope"
        unless ex.isInterrupt do throwError "native cancellation changed exception identity"
        if ← goal.mvarId!.isAssigned then throwError "cancellation failed to restore branch state"
        unless (← accepted.get) == (if success then 1 else 0) do
          throwError "rollback changed external acceptance-marker semantics"

run_meta do
  -- An unknown internal failure from the original continuation is neither a
  -- bounded miss nor a lane timeout, and restores the already assigned branch.
  withoutModifyingState do
    let unknown ← registerInternalExceptionId `compositionDraftUnknown
    withLocalDeclD `n natType fun n => do
      let goal ← mkFreshExprMVar natType
      let cfg ← config natType #[``Nat.succ]
      let ctx ← context
      let result ← observeAll <| (Leant2.BranchComposition.run cfg goal.mvarId! 1
        #[(← n.fvarId!.getDecl)] (throw (.internal unknown))).run ctx
      match result with
      | .error (.internal id _) => unless id == unknown do throwError "internal identity changed"
      | _ => throwError "unknown internal failure was swallowed"
      if ← goal.mvarId!.isAssigned then throwError "internal failure leaked branch assignment"

run_meta do
  -- A term outside the two-head prefix remains available to ordinary search.
  -- Nat is used as a small direct-filler fixture, not as production eligibility.
  withoutModifyingState do
    withLocalDeclD `n natType fun n => do
      let goal ← mkFreshExprMVar natType
      let cfg ← config natType #[]
      let ctx ← context
      let wanted := succ (succ (succ n))
      let next := isWanted goal wanted
      let locals := #[(← n.fvarId!.getDecl)]
      if ← (Leant2.BranchComposition.run cfg goal.mvarId! 3 locals next).run ctx then
        throwError "prefix constructed a three-head witness"
      unless ← (search cfg next 0 [{ mvar := goal.mvarId!, depth := 3 }]).run ctx do
        throwError "ordinary search could not run after a restored prefix miss"

end Leant2Tests.BranchComposition
