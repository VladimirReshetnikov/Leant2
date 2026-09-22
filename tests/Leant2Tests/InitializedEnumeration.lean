import Leant2.Engine

/-! Initialized roots retain ordinary enumeration order while explicit pending
obligations, whole-contract acceptance, native closures, and caller-owned state
restoration are exercised independently. No sketch frontend is assumed. -/

namespace Leant2Tests.InitializedEnumeration
open Lean Meta Elab Leant2

private def context : MetaM SearchCtx := do
  return {
    ledger := ← IO.mkRef {}
    refutedPrograms := ← IO.mkRef {}
    observationCache := ← IO.mkRef #[]
    observationReport := ← IO.mkRef {}
    graceDeadline := ← IO.mkRef none }

private def restoring (action : MetaM α) : MetaM α := do
  let coreState ← getThe Core.State
  let metaState ← getThe Meta.State
  try action finally
    modifyThe Meta.State fun _ => metaState
    modifyThe Core.State fun _ => coreState

private def observeAll (action : MetaM α) : MetaM (Except Exception α) := do
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  try return .ok (← action)
  catch ex => return .error ex

private def sameException (expected actual : Exception) : Bool :=
  match expected, actual with
  | .internal a _, .internal b _ => a == b
  | .error _ a, .error _ b => a.stripNestedTags.kind == b.stripNestedTags.kind
  | _, _ => false

private def replay (candidate : Accepted) : MetaM Unit := do
  unless !candidate.program.hasMVar && !candidate.program.hasFVar &&
      !candidate.program.hasLooseBVars && !candidate.program.hasSorry do
    throwError "initialized enumeration exported an incomplete program"
  let .ok axioms ← kernelCheckAndAudit `Leant2Tests.InitializedEnumeration
      candidate.program candidate.programType candidate.levelParams false
    | throwError "initialized program did not replay after restoration"
  unless axioms.isEmpty do throwError "initialized fixture introduced an axiom"

-- Ordinary entry and the generalized entry retain the exact constructor order,
-- productive-depth boundary, and work counts on an actual enumerated type.
run_meta do
  let run (initialized : Bool) : MetaM (Array Expr × Nat × String × Array Nat) := restoring do
    let ctx ← context
    let seen ← IO.mkRef (#[] : Array Expr)
    let initializedDepths ← IO.mkRef (#[] : Array Nat)
    let completed ← IO.mkRef 0
    let accept : Expr → SearchM Bool := fun value => do
      seen.modify (·.push value)
      return false
    let productive : SearchM Bool := do return !(← seen.get).isEmpty
    if initialized then
      enumerateInitialized ctx {} (fun depth => do
        initializedDepths.modify (·.push depth)
        let root ← mkFreshExprMVar (mkConst ``Bool)
        return {
          root := root.mvarId!
          goals := [{ mvar := root.mvarId!, depth, allowExtendedRecursion := true }] })
        accept productive [0, 1, 2] completed
    else
      enumerate ctx {} (mkConst ``Bool) accept productive [0, 1, 2] completed
    return (← seen.get, ← completed.get, reprStr (← ctx.ledger.get), ← initializedDepths.get)
  let ordinary ← run false
  let initialized ← run true
  let expected := #[mkConst ``Bool.false, mkConst ``Bool.true]
  unless ordinary.1 == expected && initialized.1 == expected &&
      ordinary.2.1 == 1 && initialized.2.1 == 1 &&
      ordinary.2.2.1 == initialized.2.2.1 && initialized.2.2.2 == #[0] do
    throwError "initialized enumeration changed ordinary terms, order, work, or productive depth"

private def offsetContract (target : Expr) : MetaM Expr :=
  withLocalDeclD `f target fun f => do
    let equation (xs : List Nat) (expected : Nat) : MetaM Expr := do
      let list ← mkListLit (mkConst ``Nat) (xs.map mkNatLit)
      mkEq (mkApp f list) (mkNatLit expected)
    let equations ← [( [], 1 ), ([2], 3), ([2, 3], 6), ([0, 4, 0], 5)].mapM fun (xs, n) =>
      equation xs n
    let first :: rest := equations | throwError "missing offset observations"
    let predicate := rest.foldl (mkApp2 (mkConst ``And)) first
    mkLambdaFVars #[f] predicate

-- A fixed List.foldr has two independent holes. Its actual root is assigned
-- before search starts, so searching just the root would skip both holes.
-- Wrong completed combinations are rejected by the real whole-function
-- contract; a successful leaf contains both the program and its actual proof.
run_meta do
  let target ← mkArrow (← mkAppM ``List #[mkConst ``Nat]) (mkConst ``Nat)
  let contract ← offsetContract target
  let found ← IO.mkRef (#[] : Array Accepted)
  let ledger ← restoring do
    withNewMCtxDepth do
      let ctx ← context
      let ctx := { ctx with deadline := some ((← IO.monoMsNow) + 10000) }
      let stepType ← mkArrow (mkConst ``Nat) (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
      let step ← mkFreshExprMVar stepType .syntheticOpaque
      let init ← mkFreshExprMVar (mkConst ``Nat) .syntheticOpaque
      let program ← withLocalDeclD `xs (target.bindingDomain!) fun xs => do
        mkLambdaFVars #[xs] (← mkAppM ``List.foldr #[step, init, xs])
      let residual ← mkResidual contract target
      let providers ← mkProviders #[``Nat.add]
      let cfg : SearchConfig := {
        providers, contract := some contract, residual, recursionFirst := true
        skip := ["residual"] }
      let preparedCore ← getThe Core.State
      let preparedMeta ← getThe Meta.State
      let initializedDepths ← IO.mkRef (#[] : Array Nat)
      let initializeSeed : Nat → SearchM EnumerationSeed := fun depth => do
        modifyThe Core.State fun _ => preparedCore
        modifyThe Meta.State fun _ => preparedMeta
        checkDeadline
        unless (← getMCtx).depth == preparedMeta.mctx.depth &&
            !(← step.mvarId!.isAssigned) && !(← init.mvarId!.isAssigned) do
          throwError "prepared holes were not restored at their owned depth"
        let marker := `Leant2Tests.InitializedEnumeration.passMarker
        if (← getEnv).contains marker then
          throwError "the previous pass environment was not restored"
        addDecl (.thmDecl {
          name := marker, levelParams := [],
          type := mkConst ``True, value := mkConst ``True.intro })
        initializedDepths.modify (·.push depth)
        let proof ← mkFreshExprMVar (contract.beta #[program]) .syntheticOpaque
        let root ← mkFreshExprMVar (← mkAppM ``Subtype #[contract])
        root.mvarId!.assign (mkApp4 (mkConst ``Subtype.mk [.succ .zero])
          target contract program proof)
        return {
          root := root.mvarId!
          goals := [{ mvar := step.mvarId!, depth }, { mvar := init.mvarId!, depth },
            { mvar := proof.mvarId!, depth }] }
      let completed ← IO.mkRef 0
      enumerateInitialized ctx cfg initializeSeed (fun value => do
        unless value.isAppOfArity ``Subtype.mk 4 do
          throwError "acceptance received a component instead of the whole root"
        let program := value.getArg! 2
        let proof := value.getArg! 3
        let .ok candidate ← gate .strictConstructive program target
            (some (proof, mkApp contract program))
          | throwError "initialized root failed its original whole-function contract"
        found.modify (·.push candidate)
        return true) (do return !(← found.get).isEmpty) [0, 1, 2, 3] completed
      unless !(← found.get).isEmpty && (← initializedDepths.get).size ≥ 2 &&
          (← completed.get) == (← initializedDepths.get).size do
        throwError "initialized two-hole fold did not complete a productive pass"
      return ← ctx.ledger.get
  let candidates ← found.get
  unless candidates.size == 1 && ledger.rejected > 0 do
    throwError "two-hole search did not reject wrong complete programs before acceptance"
  if (← getEnv).contains `Leant2Tests.InitializedEnumeration.passMarker then
    throwError "the prepared pass environment escaped its lifetime"
  let candidate := candidates[0]!
  replay candidate
  let .ok proofAxioms ← kernelCheckAndAudit `Leant2Tests.InitializedEnumeration
      candidate.proof (mkApp contract candidate.program) candidate.levelParams true
    | throwError "whole-contract proof did not replay after prepared-state restoration"
  unless proofAxioms.isEmpty do throwError "whole contract introduced an axiom"

-- A pending goal created inside a lambda is not replaced with its closed
-- wrapper. Ordinary search fills the real local goal; native instantiation
-- must then close the entire expression before acceptance.
run_meta do
  let target ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let found ← IO.mkRef (none : Option Accepted)
  restoring do
    withNewMCtxDepth do
      let (program, pending) ← withLocalDeclD `value (mkConst ``Nat) fun value => do
        let pending ← mkFreshExprMVar (mkConst ``Nat) .syntheticOpaque
        return (← mkLambdaFVars #[value] pending, pending.mvarId!)
      unless program.hasExprMVar do throwError "closure fixture was already complete"
      let ctx ← context
      let completed ← IO.mkRef 0
      enumerateInitialized ctx {} (fun depth => do
        checkDeadline
        let root ← mkFreshExprMVar target
        root.mvarId!.assign program
        return { root := root.mvarId!, goals := [{ mvar := pending, depth }] })
        (fun value => do
          let .ok accepted ← gate .strictConstructive value target none
            | throwError "native lambda closure did not complete"
          found.set (some accepted)
          return true) (do return (← found.get).isSome) [0, 1] completed
  let some accepted ← found.get | throwError "owned lambda body was not synthesized"
  replay accepted
  unless ← isDefEq accepted.program (mkLambda `value .default (mkConst ``Nat) (.bvar 0)) do
    throwError "lambda completion changed its local binder meaning"

-- A zero-hole root uses no fictitious pending goal. The initializer owns its
-- deadline checkpoint. A successful stop is not invalidated by a heuristic
-- quota that expires only after acceptance has escaped into IO storage.
run_meta do
  restoring do
    let stopped ← IO.mkRef false
    let checks ← IO.mkRef 0
    let initialized ← IO.mkRef 0
    let ctx ← context
    let ctx := { ctx with scopedBudgetCheck := some (do
      checks.modify (· + 1)
      if ← stopped.get then throw (.internal unsupportedSyntaxExceptionId)) }
    let completed ← IO.mkRef 0
    enumerateInitialized ctx {} (fun _ => do
      checkDeadline
      initialized.modify (· + 1)
      let root ← mkFreshExprMVar (mkConst ``Nat)
      root.mvarId!.assign (mkNatLit 7)
      return { root := root.mvarId!, goals := [] })
      (fun value => do
        unless value == mkNatLit 7 do throwError "zero-hole leaf changed the supplied root"
        stopped.set true
        return true) (do stopped.get) [1, 2] completed
    unless (← stopped.get) && (← checks.get) == 1 &&
        (← initialized.get) == 1 && (← completed.get) == 1 do
      throwError "enumeration changed accepted stop, initializer admission, or depth accounting"

-- Initialization runs outside branch-failure handling. Callback ordinary errors
-- retain the old meaning of a failed alternative; internal/runtime exceptions
-- preserve identity and prevent a depth from being counted as completed.
run_meta do
  let ordinary : Exception := .error .missing m!"initializer regression"
  let heartbeat : Exception := .error .missing (.tagged `runtime.maxHeartbeats m!"test")
  let unrelated : Exception := .error .missing (.tagged `runtime.initializerTest m!"test")
  for inInitializer in [true, false] do
    for ex in [ordinary, .internal interruptExceptionId, .internal deadlineExceptionId,
        .internal graceExceptionId, heartbeat, unrelated, .internal unsupportedSyntaxExceptionId] do
      let ctx ← context
      let completed ← IO.mkRef 0
      let accepted ← IO.mkRef 0
      let beforeCore ← getThe Core.State
      let beforeMeta ← getThe Meta.State
      let result ← observeAll <| restoring do
        enumerateInitialized ctx {} (fun _ => do
          charge fun l => { l with ruleApplications := l.ruleApplications + 1 }
          logInfo "speculative initializer diagnostic"
          addDecl (.thmDecl {
            name := `Leant2Tests.InitializedEnumeration.exceptionMarker
            levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })
          let root ← mkFreshExprMVar (mkConst ``Nat)
          root.mvarId!.assign (mkNatLit 0)
          if inInitializer then throw ex
          return { root := root.mvarId!, goals := [] })
          (fun _ => do accepted.modify (· + 1); throw ex) (pure false) [0] completed
      let mustPropagate := inInitializer || Leant2.isInterrupt ex
      match result with
      | .error actual =>
        unless mustPropagate && sameException ex actual && (← completed.get) == 0 do
          throwError "initialized enumeration changed exception identity/depth accounting"
      | .ok _ =>
        unless !mustPropagate && (← completed.get) == 1 do
          throwError "initialized enumeration swallowed an initialization/internal exception"
      unless (← accepted.get) == (if inInitializer then 0 else 1) &&
          (← ctx.ledger.get).ruleApplications == 1 &&
          (← getMCtx).mvarCounter == beforeMeta.mctx.mvarCounter &&
          !(← getEnv).contains `Leant2Tests.InitializedEnumeration.exceptionMarker &&
          (← getThe Core.State).messages.toList.length == beforeCore.messages.toList.length do
        throwError "initializer/callback cleanup lost work or leaked caller state"

end Leant2Tests.InitializedEnumeration
