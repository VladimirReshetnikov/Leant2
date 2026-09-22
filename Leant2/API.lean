import Leant2.Engine
import Leant2.Native.Export

/-! Public closed-query synthesis with caller-state isolation. Results are
transported back to the original environment and independently kernel-checked
before they are returned to another metaprogram. -/

namespace Leant2
open Lean Meta

namespace API

/-- Full snapshots are required: native SavedState.restore restores only its
backtrackable subset, not every cache, diagnostic, and name generator. -/
private def inState (coreState : Core.State) (metaState : Meta.State) (act : MetaM α) : MetaM α := do
  let beforeCore ← getThe Core.State
  let beforeMeta ← getThe Meta.State
  try
    modifyThe Core.State fun _ => coreState
    modifyThe Meta.State fun _ => metaState
    withNewMCtxDepth <| withLCtx {} #[] act
  finally
    modifyThe Meta.State fun _ => beforeMeta
    modifyThe Core.State fun _ => beforeCore

private def complete (e : Expr) : Bool :=
  !e.hasExprMVar && !e.hasLevelMVar && !e.hasFVar && !e.hasLooseBVars && !e.hasSorry

/-- The public API's initial version accepts frozen types. Assigned holes are
instantiated, but remaining expression/universe holes are refused, not solved.
The lower-level runQuery retains the existing flexible-universe command path. -/
private def prepare (query : Query) : MetaM (Except String Query) :=
  tryCatchRuntimeEx (do
    let target ← instantiateMVars query.target
    let contract ← query.contract.mapM instantiateMVars
    unless complete target && contract.all complete do
      return .error "synthesize: target and contract must be closed and free of holes and sorry"
    if query.maxCandidates == 0 then
      return .error "synthesize: maxCandidates must be positive"
    withLCtx {} #[] do
      check target
      unless (← whnf (← inferType target)).isSort do
        return .error "synthesize: target must be a type"
      if let some contract := contract then
        check contract
        let expected ← mkArrow target (mkSort .zero)
        unless ← isDefEq (← inferType contract) expected do
          return .error "synthesize: contract must have type target → Prop"
      for provider in query.providers do
        unless (← getEnv).contains provider do
          return .error s!"synthesize: unknown provider {provider}"
      return .ok { query with target, contract })
    (fun ex => do
      match ex with
      | .internal .. => throw ex
      | .error .. =>
        if ex.isRuntime || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
        return .error s!"synthesize: invalid query: {← ex.toMessageData.toString}")

/-- A successful closed tactic can package its proof into fresh theorems.
Copy only those theorem bodies before restoring the original environment.
The finite cap is per exported candidate and shared by all four expressions.
Unknown constants, new axioms/definitions/opaque declarations, and cycles are
not silently trusted; original-environment kernel replay below rejects them. -/
private def extract (original : Environment) (remaining : IO.Ref Nat) (e : Expr) : MetaM Expr := do
  Native.inlineNewTheorems original (← getEnv) remaining Core.checkInterrupted
    (.error Syntax.missing m!"synthesize: auxiliary theorem export limit reached") e

/-- The same zero-substitution as Engine.atProp?, restricted to the already
frozen expressions accepted by this API. Unrelated caller universe equations
must not disable replay of a closed candidate in the original snapshot. -/
private def atPropFrozen (e : Expr) : Expr :=
  let levels := (collectLevelParams {} e).params.toList
  e.instantiateLevelParams levels (levels.map fun _ => .zero)

private def checkExpected (candidate : Accepted) (proofType target : Expr)
    (contract : Option Expr) : MetaM (Option (Array Name)) := do
  unless complete target && contract.all complete do
    throwError "synthesize: output validation received an unfrozen query"
  unless ← isDefEq candidate.programType target do return none
  if let some contract := contract then
    unless ← isDefEq proofType (mkApp contract candidate.program) do return none
  let .ok axioms ← kernelCheckAndAudit `Leant2.API candidate.program target
      candidate.levelParams false
    | throwError "synthesize: program does not establish the expected target"
  if let some contract := contract then
    let .ok proofAxioms ← kernelCheckAndAudit `Leant2.API candidate.proof
        (mkApp contract candidate.program) candidate.levelParams true
      | throwError "synthesize: proof does not establish the expected contract"
    return some (axioms ++ proofAxioms)
  return some axioms

/-- Internal test seam, not part of the supported public API. Capture the
proof's exact type before restoring the environment, then replay both checked
objects there. A replay error is an API error, never logical refutation.

An optional original query additionally restricts the actual programType to
the original target or its documented simultaneous zero-universe specialization,
and replays the proof against the corresponding contract. The actual recorded
programType is preserved; a specialized result does not prove the original
polymorphic goal. -/
def exportCandidate (originalCore : Core.State) (originalMeta : Meta.State)
    (profile : Profile) (candidate : Accepted) (expectedQuery? : Option Query := none) : MetaM Accepted := do
  let fuel ← IO.mkRef 64
  let original := originalCore.env
  let program ← extract original fuel candidate.program
  let programType ← extract original fuel candidate.programType
  let proofType ← extract original fuel (← inferType candidate.proof)
  let proof ← extract original fuel candidate.proof
  unless [program, programType, proof, proofType].all complete do
    throwError "synthesize: engine returned an incomplete candidate"
  inState originalCore originalMeta do
    Core.checkInterrupted
    let .ok programAxioms ← kernelCheckAndAudit `Leant2.API program programType
        candidate.levelParams false
      | throwError "synthesize: program does not replay in the original environment"
    let .ok proofAxioms ← kernelCheckAndAudit `Leant2.API proof proofType
        candidate.levelParams true
      | throwError "synthesize: proof does not replay in the original environment"
    let mut expectedAxioms := #[]
    if let some query := expectedQuery? then
      let transported := { candidate with program, programType, proof }
      let original ← checkExpected transported proofType query.target query.contract
      let matched ← match original with
        | some axioms => pure (some axioms)
        | none =>
          checkExpected transported proofType (atPropFrozen query.target)
            (query.contract.map atPropFrozen)
      let some axioms := matched
        | throwError "synthesize: output does not match the original or Prop-specialized query"
      expectedAxioms := axioms
    let axioms := (programAxioms ++ proofAxioms ++ expectedAxioms).toList.eraseDups.toArray
    unless axioms.all profile.allowedAxioms.contains do
      throwError "synthesize: exported candidate violates the requested axiom profile"
    Core.checkInterrupted
    return { candidate with
      program, programType, proof, axioms
      classical := axioms.contains ``Classical.choice }

private def exportRefutation (originalCore : Core.State) (originalMeta : Meta.State)
    (query : Query) (expected : Expr) (certificate : Accepted) : MetaM Accepted := do
  let certificate ← exportCandidate originalCore originalMeta query.profile certificate
  inState originalCore originalMeta do
    Core.checkInterrupted
    let .ok expectedAxioms ← kernelCheckAndAudit `Leant2.API certificate.program
        expected certificate.levelParams true
      | throwError "synthesize: refutation does not establish the original negative statement"
    let axioms := (certificate.axioms ++ expectedAxioms).toList.eraseDups.toArray
    unless axioms.all query.profile.allowedAxioms.contains do
      throwError "synthesize: refutation violates the requested axiom profile"
    Core.checkInterrupted
    return { certificate with axioms, classical := axioms.contains ``Classical.choice }

/-- Internal output-validation seam. Mathematical negatives require evidence
for the original statement; bounded negatives carry no certificate. Invalid
engine outputs raise an exception, never a preflight or negative result. -/
def exportOutcome (originalCore : Core.State) (originalMeta : Meta.State)
    (query : Query) (outcome : Outcome) : MetaM Outcome := do
  match outcome with
  | .verified candidates ledger =>
    if candidates.isEmpty then throwError "synthesize: engine returned an empty verified result"
    return .verified (← candidates.mapM fun candidate =>
      exportCandidate originalCore originalMeta query.profile candidate (some query)) ledger
  | .negative .impossible certificate ledger =>
    let some certificate := certificate
      | throwError "synthesize: impossibility result has no certificate"
    let expected ← mkArrow query.target (mkConst ``False)
    return .negative .impossible
      (some (← exportRefutation originalCore originalMeta query expected certificate)) ledger
  | .negative .contractImpossible certificate ledger =>
    let some contract := query.contract
      | throwError "synthesize: contract impossibility result has no original contract"
    let some certificate := certificate
      | throwError "synthesize: contract impossibility result has no certificate"
    let expected ← withLocalDeclD `f query.target fun f =>
      mkForallFVars #[f] (mkApp (mkConst ``Not) (mkApp contract f))
    return .negative .contractImpossible
      (some (← exportRefutation originalCore originalMeta query expected certificate)) ledger
  | .negative kind certificate ledger =>
    if certificate.isSome then
      throwError "synthesize: bounded negative result unexpectedly carries a certificate"
    return .negative kind none ledger
  | other => return other

end API

/-- Synthesize from a closed, fully elaborated query without changing caller
Core/Meta state or using the ambient local context as additional providers.

Accepted programs, types, and proofs are complete and kernel-replayable in the
original environment, with their returned levelParams and axiom inventory.
Inspect each programType and proof type: classical search can specialize the
target/contract pair to Prop, including universes that occur only in the contract.
No result aliases, compiler adapters, or executable definitions are published.

Mathematical negative outcomes carry a checked certificate for the original
negative statement. Bounded negative outcomes carry no certificate.
Malformed inputs yield preflightError. Recognized search limits keep the
existing Outcome semantics. User cancellation, unrelated runtime/internal
exceptions, and failed output replay propagate after state restoration.
The budget is cooperative; this is not a hard end-to-end timeout. -/
def synthesize (query : Query) : MetaM Outcome := do
  Core.checkInterrupted
  let originalCore ← getThe Core.State
  let originalMeta ← getThe Meta.State
  try
    withNewMCtxDepth <| withLCtx {} #[] do
      match ← API.prepare query with
      | .error message => return .preflightError message
      | .ok query =>
        let outcome ← runQuery query
        let outcome ← API.exportOutcome originalCore originalMeta query outcome
        Core.checkInterrupted
        return outcome
  finally
    modifyThe Meta.State fun _ => originalMeta
    modifyThe Core.State fun _ => originalCore

end Leant2
