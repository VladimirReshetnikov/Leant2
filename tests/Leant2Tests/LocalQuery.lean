import Leant2.Frontend.Local

/-! Local closure and adversarial replay are tested independently of parser,
presentation, and public fresh-file frontend acceptance. -/
namespace Leant2Tests.LocalQuery

open Lean Meta Elab Term Leant2 Leant2.Frontend

private def prepared (type : Expr) : MetaM LocalQuery := do
  let .ok query ← prepareLocalQuery type | throwError "local query preparation failed"
  return query

private def rejected (query : LocalQuery) (term : Expr) : MetaM Unit := do
  if (← replayLocalCandidate query .standard term).isSome then
    throwError "malformed candidate escaped original-type replay"

run_meta do
  -- A candidate certified for Prop-specialized identity is not an inhabitant
  -- of the caller's universally polymorphic identity signature.
  let level := Level.param `u
  let target := mkForall `A .implicit (.sort level)
    (mkForall `a .default (.bvar 0) (.bvar 1))
  let query ← prepared target
  let specialized := mkLambda `A .implicit (.sort .zero)
    (mkLambda `a .default (.bvar 0) (.bvar 0))
  let original := mkLambda `A .implicit (.sort level)
    (mkLambda `a .default (.bvar 0) (.bvar 0))
  rejected query specialized
  unless (← replayLocalCandidate query .strictConstructive original).isSome do
    throwError "original polymorphic identity did not replay"

run_meta do
  let query ← prepared (mkConst ``Nat)
  rejected query (mkConst ``True.intro)
  rejected query (.bvar 0)
  rejected query (mkConst ``sorryAx)
  rejected query (.sort (.param `foreignUniverse))
  let hole ← mkFreshExprMVar (mkConst ``Nat)
  rejected query hole
  unless !(← hole.mvarId!.isAssigned) do throwError "replay assigned an incoming hole"
  let foreign ← withLocalDeclD `foreign (mkConst ``Nat) pure
  rejected query foreign

run_meta do
  let hole ← mkFreshExprMVar (mkSort (.succ .zero))
  let .error .unresolvedDependency ← prepareLocalQuery hole
    | throwError "open expected type was not deferred"
  unless !(← hole.mvarId!.isAssigned) do throwError "preparation assigned the expected type"
  let level ← mkFreshLevelMVar
  let .error .unresolvedDependency ← prepareLocalQuery (.sort level)
    | throwError "open expected universe was not deferred"
  unless (← instantiateLevelMVars level) == level do
    throwError "preparation specialized an incoming universe"
  withLocalDeclD `pending hole fun _ => do
    let .error .unresolvedDependency ← prepareLocalQuery (mkConst ``Nat)
      | throwError "open local provider type was ignored"
    unless !(← hole.mvarId!.isAssigned) do throwError "preparation assigned a local type"

run_meta do
  -- Excluded implementation details cannot escape into the closed query.
  withLocalDecl `hidden .default (mkSort (.succ .zero)) (kind := .implDetail) fun hidden => do
    let .error .unsupportedDependency ← prepareLocalQuery hidden
      | throwError "hidden dependency escaped closure"
  withLocalDecl `recursivePlaceholder .default (mkConst ``Nat) (kind := .auxDecl) fun hidden => do
    let query ← prepared (mkConst ``Nat)
    unless query.locals.isEmpty do throwError "recursive placeholder became a provider"
    rejected query hidden

run_meta do
  -- Terminal genuine let: its value is available as a provider even when the
  -- reduced target has no leading forall. No numeral-37 provider is supplied.
  withLetDecl `kept (mkConst ``Nat) (mkNatLit 37) fun kept => do
    let predicate ← withLocalDeclD `n (mkConst ``Nat) fun n => do
      mkLambdaFVars #[n] (← mkEq n kept)
    let type ← mkAppM ``Subtype #[predicate]
    let query ← prepared type
    unless query.closedTarget.isLet && query.arguments.isEmpty do
      throwError "genuine let was generalized or applied as an argument"
    let value ← synthesizeLocal query #[] 5000 .strictConstructive
    unless ← isDefEq (← mkAppM ``Subtype.val #[value]) (mkNatLit 37) do
      throwError "terminal let provider was not preserved"

run_meta do
  -- Nondependent have-values may deliberately be ill-typed. The native API
  -- requires treating them as assumptions and never inspecting that value.
  withLetDecl `opaqueHave (mkConst ``Nat) (mkConst ``True.intro) (nondep := true) fun h => do
    let query ← prepared (mkConst ``Nat)
    unless query.closedTarget.isForall && query.arguments == #[h] do
      throwError "nondependent have was not generalized and reapplied"
    let identity := mkLambda `h .default (mkConst ``Nat) (.bvar 0)
    let some value ← replayLocalCandidate query .strictConstructive identity
      | throwError "nondependent have did not replay"
    unless ← isDefEq value h do throwError "nondependent have argument mapping changed"

run_meta do
  -- Interleaved parameter, genuine let, and dependent parameter. Reopening
  -- applies exactly the two ordinary locals, retaining the let in between.
  withLocalDeclD `n (mkConst ``Nat) fun n =>
    withLetDecl `m (mkConst ``Nat) n fun m => do
      let finType ← mkAppM ``Fin #[← mkAppM ``Nat.succ #[m]]
      withLocalDeclD `i finType fun i => do
        let query ← prepared finType
        unless query.arguments == #[n, i] do throwError "interleaved local arguments shifted"
        let closed ← mkLambdaFVars query.locals i (usedOnly := false) (usedLetOnly := false)
        let some value ← replayLocalCandidate query .strictConstructive closed
          | throwError "dependent local did not replay"
        unless ← isDefEq value i do throwError "dependent local changed on reopening"

axiom projectOnly : Nat

run_meta do
  let query ← prepared (mkConst ``Nat)
  rejected query (mkConst ``projectOnly)
  unless (← replayLocalCandidate query (.projectRelative [``projectOnly])
      (mkConst ``projectOnly)).isSome do
    throwError "explicit project-relative profile was ignored"

run_elab do
  let target ← elabType (← `(Nonempty Nat → Nat))
  let value ← elabTerm (← `(fun (h : Nonempty Nat) => Classical.choice h)) (some target)
  synthesizeSyntheticMVarsNoPostponing
  let query ← prepared (← instantiateMVars target)
  let value ← instantiateMVars value
  unless (← replayLocalCandidate query .standard value).isSome do
    throwError "standard choice candidate should replay"
  if (← replayLocalCandidate query .strictConstructive value).isSome then
    throwError "strict profile admitted Classical.choice"

run_meta do
  -- A real native cancellation token is propagated after isolated search has
  -- restored its state. Incoming obligations and diagnostics remain intact.
  let query ← prepared (mkConst ``Nat)
  let incoming ← mkFreshExprMVar (mkConst ``Nat)
  let originalEnv ← getEnv
  let originalMessages := (← getThe Core.State).messages.toList.length
  let token ← IO.CancelToken.new
  token.set
  let _ : MonadExceptOf Exception MetaM := MonadAlwaysExcept.except
  let outcome ← try
    withTheReader Core.Context (fun context => { context with cancelTk? := some token }) do
      discard <| synthesizeLocal query #[] 5000
    pure false
  catch ex => pure ex.isInterrupt
  unless outcome do throwError "frontend search consumed native cancellation"
  unless !(← incoming.mvarId!.isAssigned) &&
      (← getThe Core.State).messages.toList.length == originalMessages &&
      (← getEnv).constants.map₂.toList.length == originalEnv.constants.map₂.toList.length do
    throwError "canceled frontend search leaked speculative state"

end Leant2Tests.LocalQuery
