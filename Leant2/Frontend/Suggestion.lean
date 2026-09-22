import Leant2.Frontend.Local

/-! Complete native declaration elaboration for recursive tactic suggestions.
The temporary declaration is discarded after checking its finished kernel term.
This complements the tactic frontend's original-goal and sibling-goal checks. -/

namespace Leant2.Frontend

open Lean Meta Elab Term

/-- Finish native `let rec` lifting before checking a source suggestion. The
original local declarations are abstracted with the same policy as `LocalQuery`;
the type is embedded as an expression, so neither names nor universes are guessed.
Every speculative declaration and elaboration-state change is discarded.

This checks a completed term at the original type, not equality to a synthesized
term. The caller first checks the tactic's original goal and sibling behavior. -/
def validateCompletedSuggestion (query : LocalQuery)
    (tacticSyntax : TSyntax `tactic) : TermElabM Bool := do
  Core.checkInterrupted
  let savedCore ← getThe Core.State
  let savedMeta ← getThe Meta.State
  let savedTerm ← getThe Term.State
  tryCatchRuntimeEx
    (do return (← tryFinally' (do
      modifyThe Core.State fun s => { s with messages := {} }
      let declPrefix := (← getEnv).asyncPrefix?.getD (← getDeclNGen).namePrefix
      withNewMCtxDepth <| withDeclNameForAuxNaming declPrefix do
      withOptions (fun opts => opts.setBool `Elab.async false
          |>.setBool `debug.skipKernelTC false) do
      TermElabM.run' <| withLevelNames query.levelParams <| withoutErrToSorry do
        let name ← mkAuxName `_leant2_suggestion
        withDeclName name do
        let value ← elabTermEnsuringType (← `(term| by $tacticSyntax:tactic)) query.target
        synthesizeSyntheticMVarsNoPostponing
        let value ← instantiateMVars value
        let closed ← mkLambdaFVars query.locals value (usedOnly := false) (usedLetOnly := false)
        -- Like Lean's #eval pipeline, keep the pending let-rec registrations
        -- in this fresh elaborator while native mutual-definition closure runs.
        let bodySyntax ← exprToSyntax closed
        let typeSyntax ← exprToSyntax query.closedTarget
        let declaration ← `(Parser.Command.definition|
          def $(mkIdent (rootNamespace ++ name)):ident : $typeSyntax := $bodySyntax)
        let scope : Command.Scope := { header := "", opts := ← getOptions }
        let view := Command.mkDefViewOfDef { computeKind := .noncomputable } declaration
        Term.elabMutualDef #[] scope #[view]
        if (← getThe Core.State).messages.hasErrors then return false
        let info ← getConstInfo name
        let some completed := info.value? (allowOpaque := true) | return false
        if completed.hasMVar || completed.hasLevelMVar || completed.hasFVar ||
            completed.hasLooseBVars || completed.hasSorry || info.type.hasMVar ||
            info.type.hasLevelMVar || info.type.hasFVar || info.type.hasSorry then return false
        unless info.levelParams.all query.levelParams.contains do return false
        let valid := (← replayLocalCandidate query .standard completed).isSome
        Core.checkInterrupted
        return valid) fun _ => do
          modifyThe Term.State fun _ => savedTerm
          modifyThe Meta.State fun _ => savedMeta
          modifyThe Core.State fun _ => savedCore).1)
    (fun ex => do
      if Leant2.isInterrupt ex then throw ex
      return false)

end Leant2.Frontend
