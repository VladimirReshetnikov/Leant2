import Leant2

/-! Provider-isolated construction, universal post-checks, printed-source execution,
native partial closures, permission boundaries, and transactional cancellation
are deliberately separate assertions. No reference is a synthesis provider. -/

open Lean Meta Elab Term Command Leant2

private def guardContext : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def hasGuard (e : Expr) : Bool :=
  (e.find? fun e => e.isConstOf ``Decidable.rec || e.isConstOf ``Decidable.casesOn).isSome

-- Count occurrences, not distinct names: Expr.foldConsts deduplicates names.
private partial def guardCount : Expr → Nat
  | .const name _ => if name == ``Decidable.rec || name == ``Decidable.casesOn then 1 else 0
  | .app f a => guardCount f + guardCount a
  | .lam _ type body _ | .forallE _ type body _ => guardCount type + guardCount body
  | .letE _ type value body _ => guardCount type + guardCount value + guardCount body
  | .mdata _ body | .proj _ _ body => guardCount body
  | _ => 0

elab "#guard_synthesize " n:ident " : " ty:term " where " pred:term : command => do
  let accepted ← liftTermElabM <| withoutErrToSorry do
    let target ← elabType ty
    let contract ← elabTerm pred (some (← mkArrow target (mkSort .zero)))
    synthesizeSyntheticMVarsNoPostponing
    let target ← instantiateMVars target
    let contract ← instantiateMVars contract
    let outcome ← runQuery {
      target, contract := some contract, providers := #[], profile := .strictConstructive
      budgetMs := 10000, maxCandidates := 1, graceMs := 0 }
    let .verified candidates _ := outcome
      | throwError "guard fixture did not synthesize with its empty provider inventory"
    let candidate := candidates[0]!
    unless ← isDefEq candidate.programType target do
      throwError "guard fixture changed the requested type"
    unless hasGuard candidate.program do
      throwError "fixture did not exercise native constructive guard introduction"
    unless candidate.axioms.isEmpty do
      throwError "constructive guard candidate introduced an axiom"
    return candidate
  unless ← Presentation.publish n.getId accepted do
    throwError "guard candidate did not compile"
  let ci ← liftCoreM <| getConstInfo n.getId
  unless ci.value! == accepted.program && ci.type == accepted.programType do
    throwError "guard publication changed the exact certified expression"

#guard_synthesize guardMaximum : Nat → Nat → Nat where
  fun f => f 2 5 = 5 ∧ f 7 3 = 7 ∧ f 4 4 = 4 ∧ f 0 1 = 1

#guard_synthesize guardMinimum : Nat → Nat → Nat where
  fun f => f 2 5 = 2 ∧ f 7 3 = 3 ∧ f 4 4 = 4 ∧ f 0 1 = 0 ∧ f 1 0 = 0

#guard_synthesize guardDropZeros : List Nat → List Nat where
  fun f => f [0, 2, 0, 3] = [2, 3] ∧ f [0, 0] = [] ∧ f [4, 5] = [4, 5]

-- This query cannot reuse List.filter/foldr/etc: Query.providers was #[], and
-- the accepted expression must actually contain the native recursive recursor.
run_meta do
  let ci ← getConstInfo ``guardDropZeros
  unless (ci.value!.find? fun e => e.isConstOf ``List.rec).isSome do
    throwError "dropzeros fixture did not exercise recursive branch guards"
  for forbidden in [``List.filter, ``List.filterMap, ``List.foldr, ``List.foldl] do
    if (ci.value!.find? fun e => e.isConstOf forbidden).isSome then
      throwError "restricted dropzeros reused forbidden library implementation {forbidden}"

-- These universal checks are independent of the finite search contracts.
example : ∀ a b : Nat, guardMaximum a b = Nat.max a b := by
  intro a b
  cases hd : (inferInstance : Decidable (a ≤ b)) <;> simp_all [guardMaximum, Nat.max_def]

example : ∀ a b : Nat, guardMinimum a b = Nat.min a b := by
  intro a b
  cases hd : (inferInstance : Decidable (a ≤ b)) <;> simp_all [guardMinimum, Nat.min_def]

example : ∀ xs : List Nat, guardDropZeros xs = xs.filter (fun n => n != 0) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons n xs ih =>
    cases hd : (inferInstance : Decidable (n = 0)) with
    | isFalse h =>
      have hb : (n != 0) = true := bne_iff_ne.mpr h
      simpa only [guardDropZeros, List.filter, hd, hb] using congrArg (List.cons n) ih
    | isTrue h => simp_all [guardDropZeros, List.filter]

/-- info: (9, 11, 0, 7) -/
#guard_msgs in
#eval (guardMaximum 0 9, guardMaximum 11 2, guardMinimum 9 0, guardMinimum 7 7)

/-- info: ([], [], [8], [2, 5, 9]) -/
#guard_msgs in
#eval (guardDropZeros [], guardDropZeros [0], guardDropZeros [8],
  guardDropZeros [0, 2, 0, 0, 5, 9, 0])

-- Independent source parsing and compilation, not Syntax metadata reuse.
run_cmd do
  for name in [``guardMaximum, ``guardMinimum, ``guardDropZeros] do
    let displayName := name ++ `_guard_display
    let cmd ← liftTermElabM do
      let ci ← getConstInfo name
      let stx ← Presentation.programSyntax ci.value!
      let text := (← PrettyPrinter.ppTerm stx).pretty
      if (text.splitOn ".rec").length != 1 then
        throwError "printed guard source retained a raw recursor: {text}"
      let stx ← match Parser.runParserCategory (← getEnv) `term text with
        | .ok stx => pure (⟨stx⟩ : TSyntax `term)
        | .error error => throwError "printed guard source is invalid: {error}"
      let type ← PrettyPrinter.delab ci.type
      `(command| def $(mkIdent displayName) : $type := $stx)
    elabCommand cmd
    let ci ← liftCoreM <| getConstInfo displayName
    if ci.value!.hasMVar || ci.value!.hasSorry || isNoncomputable (← getEnv) displayName then
      throwError "printed guard source did not compile completely"

example : ∀ a b : Nat, guardMaximum._guard_display a b = guardMaximum a b := by
  intro a b
  cases hd : (inferInstance : Decidable (a ≤ b)) <;>
    simp_all [guardMaximum._guard_display, guardMaximum]

example : ∀ a b : Nat, guardMinimum._guard_display a b = guardMinimum a b := by
  intro a b
  cases hd : (inferInstance : Decidable (a ≤ b)) <;>
    simp_all [guardMinimum._guard_display, guardMinimum]

-- The printed local recursion elaborates to a fresh auxiliary declaration.
-- Obtain its name from the actual compiled definition instead of hard-coding
-- the presentation's fresh counter or silently omitting its defining equations.
run_cmd do
  let unfoldTerms ← liftCoreM do
    let ci ← getConstInfo ``guardDropZeros._guard_display
    let names := #[``guardDropZeros._guard_display, ``guardDropZeros] ++
      ci.value!.getUsedConstants.filter (``guardDropZeros._guard_display).isPrefixOf
    return names
  let unfoldTerms ← unfoldTerms.mapM fun name => `(Parser.Tactic.simpLemma| $(mkIdent name):term)
  elabCommand (← `(example : ∀ xs : List Nat,
      guardDropZeros._guard_display xs = guardDropZeros xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons n xs ih =>
      cases hd : (inferInstance : Decidable (n = 0)) <;> simp_all [$unfoldTerms,*]))

/-- info: (9, 0, [2, 5, 9]) -/
#guard_msgs in
#eval (guardMaximum._guard_display 0 9, guardMinimum._guard_display 9 0,
  guardDropZeros._guard_display [0, 2, 0, 0, 5, 9, 0])

-- Grammar bound, stable ordering, and no assignment of unknown input types.
run_elab do
  let telescope ← elabType (← `(∀ (_a _b _c _d _e _f : Nat), Nat))
  forallTelescope telescope fun values _ => do
    let locals ← values.reverse.mapM fun e => e.fvarId!.getDecl
    let predicates ← natGuardPredicates locals
    unless predicates.size == 10 do throwError "Nat guard grammar escaped its four-local bound"
    let expected ← mkAppM ``LE.le #[values[2]!, values[3]!]
    unless predicates[0]! == expected do throwError "Nat guard ordering changed"
    for p in predicates do
      if (p.find? fun e => e == values[0]! || e == values[1]!).isSome then
        throwError "Nat guard grammar used a local outside its bound"
  let α ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `x α fun x => do
    unless (← natGuardPredicates #[(← x.fvarId!.getDecl)]).isEmpty do
      throwError "Nat guard invented an input type"
    if ← α.mvarId!.isAssigned then throwError "Nat guard assigned an input type hole"
  withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
    let p ← mkEq n (mkNatLit 0)
    for known in [p, mkNot p] do
      withLocalDeclD `h known fun h => do
        unless (← natGuardPredicates #[(← h.fvarId!.getDecl), (← n.fvarId!.getDecl)]).isEmpty do
          throwError "Nat guard repeated an already-known branch test"

-- Native guarded partial functions stay closed apart from tracked branch holes.
-- A decided observation and an undecided one must remain distinct; a rejected
-- sibling cannot reuse the earlier satisfied report after restoration.
run_elab do
  let type ← elabType (← `(Nat → Nat))
  let contract ← elabTerm (← `(fun f : Nat → Nat => f 0 = 0 ∧ f 2 = 2)) none
  let observations ← mkObservations contract type
  let root ← mkFreshExprMVar type
  let (n, body) ← root.mvarId!.intro1P
  let (positive, negative) ← body.withContext do
    let predicate ← mkEq (mkFVar n) (mkNatLit 0)
    body.byCasesDec predicate (← synthInstance (mkApp (Lean.mkConst ``Decidable) predicate))
  let fork ← saveState
  positive.mvarId.assign (mkNatLit 0)
  let partialProgram ← instantiatePartial root
  if partialProgram.hasFVar then throwError "native guard partial closure leaked a local"
  let (partialReport, cache) ← evalObservations observations partialProgram #[] instantiatePartial
  unless partialReport.statuses == #[some .satisfied, some .stuck] do
    throwError "guard residual confused an open branch with failure: {repr partialReport.statuses}"
  negative.mvarId.assign (mkFVar n)
  let complete ← instantiateMVars root
  if complete.hasExprMVar || complete.hasFVar then throwError "native guard did not close its branch binders"
  match ← gate .strictConstructive complete type none with
  | .ok _ => pure ()
  | .error _ => throwError "complete native guard failed kernel certification"
  let (completeReport, cache) ← evalObservations observations complete cache instantiatePartial
  unless completeReport.statuses == #[some .satisfied, some .satisfied] do
    throwError "complete native guard failed its observations"
  fork.restore
  positive.mvarId.assign (mkNatLit 1)
  let (badReport, _) ← evalObservations observations (← instantiatePartial root) cache instantiatePartial
  unless badReport.refuted do throwError "guard observation cache hid a rejected sibling"

-- Stronger closure probe: the assigned branch actually uses its guard proof
-- in a dependent Subtype value, rather than merely ignoring the new binder.
-- This is diagnostic evidence, not justification for enabling partial pruning.
run_elab do
  let type ← elabType (← `((n : Nat) → {m : Nat // m = n}))
  let contract ← elabTerm (← `(fun f : (n : Nat) → {m : Nat // m = n} =>
    (f 0).val = 0 ∧ (f 2).val = 2)) none
  let observations ← mkObservations contract type
  let root ← mkFreshExprMVar type
  let (n, body) ← root.mvarId!.intro1P
  let (positive, negative) ← body.withContext do
    let predicate ← mkEq (mkFVar n) (mkNatLit 0)
    body.byCasesDec predicate (← synthInstance (mkApp (Lean.mkConst ``Decidable) predicate))
  positive.mvarId.withContext do
    let subtype ← whnfR (← positive.mvarId.getType)
    let proof ← mkEqSymm (mkFVar positive.fvarId)
    positive.mvarId.assign (mkApp4 (Lean.mkConst ``Subtype.mk [.succ .zero])
      (Lean.mkConst ``Nat) (subtype.getArg! 1) (mkNatLit 0) proof)
  let partialProgram ← instantiatePartial root
  if partialProgram.hasFVar then throwError "proof-dependent partial guard escaped its binder"
  let (report, _) ← evalObservations observations partialProgram #[] instantiatePartial
  unless report.statuses == #[some .satisfied, some .stuck] do
    throwError "proof-dependent guard residual confused its open sibling: {repr report.statuses}"
  negative.mvarId.withContext do
    let subtype ← whnfR (← negative.mvarId.getType)
    let proof ← mkEqRefl (mkFVar n)
    negative.mvarId.assign (mkApp4 (Lean.mkConst ``Subtype.mk [.succ .zero])
      (Lean.mkConst ``Nat) (subtype.getArg! 1) (mkFVar n) proof)
  let complete ← instantiateMVars root
  if complete.hasExprMVar || complete.hasFVar then throwError "dependent native guard did not close"
  match ← gate .strictConstructive complete type none with
  | .ok _ => pure ()
  | .error _ => throwError "proof-dependent native guard failed kernel certification"

-- A poisoned partial-observation array is a tripwire: it must never be read
-- under this initial guarded tier. The real finite contract and its deciders
-- remain intact and must still be proved on the fully closed candidate.
run_elab do
  let type ← elabType (← `(Nat → Nat))
  let contract ← elabTerm (← `(fun f : Nat → Nat => f 0 = 0 ∧ f 2 = 2)) none
  let program ← mkFreshExprMVar type
  let proof ← mkFreshExprMVar (mkApp contract program)
  let rootType := mkApp2 (Lean.mkConst ``Subtype [.succ .zero]) type contract
  let root ← mkFreshExprMVar rootType
  root.mvarId!.assign (mkApp4 (Lean.mkConst ``Subtype.mk [.succ .zero]) type contract program proof)
  let (n, body) ← program.mvarId!.intro1P
  let poison ← elabTerm (← `(fun _ : Nat → Nat => False)) none
  let ctx ← guardContext
  let cfg : SearchConfig := {
    root := some root.mvarId!, contract := some contract, recursionFirst := true
    residual := ← mkResidual contract type, observations := ← mkObservations poison type }
  let stopped ← body.withContext do
    (constructiveNatGuards cfg (pure true) 2 1 body #[(← n.getDecl)]
      [{ mvar := proof.mvarId!, depth := 1 }]).run ctx
  unless stopped do throwError "guarded search evaluated the poisoned partial-observation tripwire"
  unless (← ctx.observationReport.get).reductions == 0 do
    throwError "guarded search unexpectedly enabled partial residual pruning"
  let program ← instantiateMVars program
  let proof ← instantiateMVars proof
  match ← gate .strictConstructive program type (some (proof, contract.beta #[program])) with
  | .ok _ => pure ()
  | .error _ => throwError "guarded search did not certify the real closed contract"

private def wrapGuardProgram (f : Nat → Nat → Nat) : {g : Nat → Nat → Nat // True} :=
  ⟨f, trivial⟩

-- Only the actual root constructor enables guards. A same-result provider must
-- not acquire root-program permission for its ordinary input argument.
run_elab do
  let type ← elabType (← `({_g : Nat → Nat → Nat // True}))
  let contract ← elabTerm (← `(fun _ : Nat → Nat → Nat => True)) none
  let root ← mkFreshExprMVar type
  let sawConstructorGuard ← IO.mkRef false
  let sawWrapper ← IO.mkRef false
  let sawWrapperGuard ← IO.mkRef false
  let ctx ← guardContext
  let cfg : SearchConfig := {
    root := some root.mvarId!, contract := some contract, proofPortfolio := false
    providers := ← mkProviders #[``wrapGuardProgram], skip := ["rec"] }
  let leaf : Leaf := do
    let term ← instantiateMVars root
    if term.getAppFn.isConstOf ``Subtype.mk && hasGuard term then sawConstructorGuard.set true
    if term.getAppFn.isConstOf ``wrapGuardProgram then
      sawWrapper.set true
      if hasGuard term then sawWrapperGuard.set true
    return false
  if ← (search cfg leaf 2 [{ mvar := root.mvarId!, depth := 2 }]).run ctx then
    throwError "rejecting permission fixture unexpectedly committed"
  unless (← sawConstructorGuard.get) && (← sawWrapper.get) do
    throwError "permission fixture did not enumerate both construction paths"
  if ← sawWrapperGuard.get then throwError "ordinary provider inherited root guard permission"
  if ← root.mvarId!.isAssigned then throwError "permission enumeration leaked a candidate"

-- The rule itself also rejects proof, sort, class and open goals before making
-- a split. This guards direct internal callers as well as normal dispatch.
run_elab do
  withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
    let contract ← elabTerm (← `(fun _ : Nat => True)) none
    let openType ← mkFreshExprMVar (mkSort (.succ .zero))
    let classType ← elabType (← `(Inhabited Nat))
    let ctx ← guardContext
    let cfg : SearchConfig := { contract := some contract }
    for type in [mkSort .zero, Lean.mkConst ``True, classType, openType] do
      let goal ← mkFreshExprMVar type
      let before ← getMCtx
      let result ← (constructiveNatGuards cfg (pure true) 2 2 goal.mvarId!
        #[(← n.fvarId!.getDecl)] []).run ctx
      if result || (← goal.mvarId!.isAssigned) || (← getMCtx).mvarCounter != before.mvarCounter then
        throwError "guard split a proof, sort, class or open goal"
    if ← openType.mvarId!.isAssigned then throwError "guard assigned an open goal type"

-- The guard flag on a proposition must not reach an existential data witness.
run_elab do
  withLocalDeclD `n (Lean.mkConst ``Nat) fun _n => do
    let type ← elabType (← `(∃ _k : Nat, True))
    let contract ← elabTerm (← `(fun _ : Nat => True)) none
    let goal ← mkFreshExprMVar type
    let reached ← IO.mkRef false
    let sawGuard ← IO.mkRef false
    let ctx ← guardContext
    let cfg : SearchConfig := { contract := some contract, proofPortfolio := false, skip := ["rec"] }
    let leaf : Leaf := do
      reached.set true
      if hasGuard (← instantiateMVars goal) then sawGuard.set true
      return false
    let _ ← (search cfg leaf 2 [{ mvar := goal.mvarId!, depth := 2, allowNatGuards := true }]).run ctx
    unless ← reached.get do throwError "proof eligibility fixture never produced a witness"
    if ← sawGuard.get then throwError "guard permission escaped into a proof witness"

private class GuardDictionary where
  witness : Nat

-- Deliberately an ordinary provider, not an instance-reducible definition.
set_option warn.classDefReducibility false in
private def makeGuardDictionary (n : Nat) : GuardDictionary := ⟨n⟩

-- Direct helper exclusion is insufficient here: the class goal can still use
-- an ordinary provider after its guard helper returns false. Its Nat argument
-- must not inherit permission from the class goal's incoming flag.
run_elab do
  withLocalDeclD `n (Lean.mkConst ``Nat) fun _n => do
    let contract ← elabTerm (← `(fun _ : Nat => True)) none
    let goal ← mkFreshExprMVar (Lean.mkConst ``GuardDictionary)
    let reachedProvider ← IO.mkRef false
    let sawGuard ← IO.mkRef false
    let ctx ← guardContext
    let cfg : SearchConfig := {
      contract := some contract, proofPortfolio := false, skip := ["rec"]
      providers := ← mkProviders #[``makeGuardDictionary] }
    let leaf : Leaf := do
      let term ← instantiateMVars goal
      if term.getAppFn.isConstOf ``makeGuardDictionary then
        reachedProvider.set true
        if hasGuard term then sawGuard.set true
      return false
    let _ ← (search cfg leaf 2 [{ mvar := goal.mvarId!, depth := 2, allowNatGuards := true }]).run ctx
    unless ← reachedProvider.get do throwError "class eligibility fixture never applied its provider"
    if ← sawGuard.get then throwError "class provider passed guard permission to its Nat argument"

-- One split constructs one guard even when further depth and splits remain.
-- Use two Nat locals: with only n, the split on n=0 makes the sole predicate
-- known, and predicate dedup would conceal accidentally inherited permission.
run_elab do
  withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
    withLocalDeclD `m (Lean.mkConst ``Nat) fun m => do
      let contract ← elabTerm (← `(fun _ : Bool => True)) none
      let goal ← mkFreshExprMVar (Lean.mkConst ``Bool)
      let reached ← IO.mkRef false
      let bad ← IO.mkRef false
      let ctx ← guardContext
      let cfg : SearchConfig := { contract := some contract, proofPortfolio := false }
      let locals := #[(← m.fvarId!.getDecl), (← n.fvarId!.getDecl)]
      let leaf : Leaf := do
        reached.set true
        if guardCount (← instantiateMVars goal) > 1 then bad.set true
        return false
      let _ ← (constructiveNatGuards cfg leaf 2 1 goal.mvarId! locals []).run ctx
      unless ← reached.get do throwError "guard budget fixture never reached its continuation"
      if ← bad.get then throwError "guard children regained guard permission"
      let noBudget ← (constructiveNatGuards cfg (pure true) 0 1 goal.mvarId! locals []).run ctx
      if noBudget || (← goal.mvarId!.isAssigned) then throwError "guard ignored split budget or rollback"
      -- Positive control: under a known n≤m branch, distinct zero tests remain.
      -- An enabled child can really form another guard at the tested depth.
      let predicate ← mkAppM ``LE.le #[n, m]
      withLocalDeclD `h predicate fun _h => do
        let child ← mkFreshExprMVar (Lean.mkConst ``Bool)
        let sawEnabledGuard ← IO.mkRef false
        let childLeaf : Leaf := do
          if hasGuard (← instantiateMVars child) then sawEnabledGuard.set true
          return false
        let _ ← (search cfg childLeaf 1
          [{ mvar := child.mvarId!, depth := 1, allowNatGuards := true }]).run ctx
        unless ← sawEnabledGuard.get do
          throwError "guard-budget positive control did not exercise a still-available test"

-- Clearing extended-induction permission is checked separately. Normally the
-- split-count check would also block it (child splits1, default maxSplits2).
-- This controlled direct-helper call makes those counts equal, so the metadata
-- itself is necessary. The enabled positive control must actually find Nat.rec.
run_elab do
  withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
    let contract ← elabTerm (← `(fun _ : Bool => True)) none
    let cfg : SearchConfig := { contract := some contract, proofPortfolio := false, maxSplits := 1 }
    let ctx ← guardContext
    let goal ← mkFreshExprMVar (Lean.mkConst ``Bool)
    let reached ← IO.mkRef false
    let sawDisabledRecursion ← IO.mkRef false
    let leaf : Leaf := do
      reached.set true
      let term ← instantiateMVars goal
      if (term.find? fun e => e.isConstOf ``Nat.rec).isSome then sawDisabledRecursion.set true
      return false
    let _ ← (constructiveNatGuards cfg leaf 2 2 goal.mvarId!
      #[(← n.fvarId!.getDecl)] []).run ctx
    unless ← reached.get do throwError "guarded induction-permission fixture never reached its continuation"
    if ← sawDisabledRecursion.get then throwError "guard child regained outer-induction permission"
    let predicate ← mkEq n (mkNatLit 0)
    withLocalDeclD `h predicate fun _h => do
      let child ← mkFreshExprMVar (Lean.mkConst ``Bool)
      let sawEnabledRecursion ← IO.mkRef false
      let childLeaf : Leaf := do
        let term ← instantiateMVars child
        if (term.find? fun e => e.isConstOf ``Nat.rec).isSome then sawEnabledRecursion.set true
        return false
      let _ ← (search cfg childLeaf 1
        [{ mvar := child.mvarId!, depth := 2, allowExtendedRecursion := true }]).run ctx
      unless ← sawEnabledRecursion.get do
        throwError "extended-induction positive control never exercised its enabled branch"

private def observeAllGuard (action : MetaM α) : MetaM (Except Exception α) := do
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch e => return .error e

-- Rejection and cancellation happen after native byCasesDec has assigned the
-- original goal and completed both branches. The continuation also mutates an
-- unrelated sibling, declaration, and diagnostic to test whole-state rollback.
run_meta do
  for failure in [none, some (Exception.error .missing m!"ordinary guarded branch failure"),
      some (Exception.internal interruptExceptionId),
      some (.internal deadlineExceptionId), some (.internal unsupportedSyntaxExceptionId)] do
    withoutModifyingState do
      withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
        let predicate ← mkEq n (mkNatLit 0)
        let goal ← mkFreshExprMVar (Lean.mkConst ``Nat)
        let sibling ← mkFreshExprMVar (Lean.mkConst ``Nat)
        let before ← getMCtx
        let messages := (← getThe Core.State).messages.toList.length
        let marker := ((← getEnv).asyncPrefix?.getD `GuardTests) ++ (← mkFreshUserName `rollbackMarker)
        let ctx ← guardContext
        let reached ← IO.mkRef false
        let result ← observeAllGuard <| (splitNatGuard goal.mvarId! predicate fun yes no => do
          yes.assign (mkNatLit 0)
          no.assign n
          unless ← goal.mvarId!.isAssigned do throwError "native guard failed to assign its parent"
          reached.set true
          sibling.mvarId!.assign (mkNatLit 9)
          addDecl <| .defnDecl {
            name := marker, levelParams := [], type := Lean.mkConst ``Nat, value := mkNatLit 1
            hints := .abbrev, safety := .safe }
          logInfo "guard continuation diagnostic must roll back"
          if let some ex := failure then throw ex
          return false).run ctx
        unless ← reached.get do throwError "guard rollback fixture did not reach its continuation"
        match result, failure with
        | .ok false, none => pure ()
        | .ok false, some (.error ..) => pure ()
        | .error (.internal actual _), some (.internal expected _) =>
          unless actual == expected do throwError "guard changed exception identity"
        | _, _ => throwError "guard swallowed cancellation or changed rejection"
        if (← goal.mvarId!.isAssigned) || (← sibling.mvarId!.isAssigned) ||
            (← getMCtx).mvarCounter != before.mvarCounter || (← getEnv).contains marker ||
            (← getThe Core.State).messages.toList.length != messages then
          throwError "guard failed to restore the entire rejected continuation"
        unless (← ctx.ledger.get).ruleApplications == 1 do
          throwError "guard rollback refunded or duplicated charged work"

-- A real IO.CancelToken is raised only after the split mutates the Meta state.
-- It is scoped to this action so the surrounding test elaborator stays usable.
run_meta do
  withoutModifyingState do
    withLocalDeclD `n (Lean.mkConst ``Nat) fun n => do
      let predicate ← mkEq n (mkNatLit 0)
      let goal ← mkFreshExprMVar (Lean.mkConst ``Nat)
      let before ← getMCtx
      let ctx ← guardContext
      let token ← IO.CancelToken.new
      let reached ← IO.mkRef false
      let result ← observeAllGuard <|
        withTheReader Core.Context (fun c => { c with cancelTk? := some token }) do
          (splitNatGuard goal.mvarId! predicate fun yes no => do
            yes.assign (mkNatLit 0)
            no.assign n
            reached.set true
            token.set
            checkDeadline
            return true).run ctx
      unless ← reached.get do throwError "native cancellation fixture did not enter its guard"
      match result with
      | .error ex => unless ex.isInterrupt do throwError "native guard cancellation changed kind"
      | .ok _ => throwError "native guard cancellation was ignored"
      if (← goal.mvarId!.isAssigned) || (← getMCtx).mvarCounter != before.mvarCounter then
        throwError "native guard cancellation leaked a branch assignment"
