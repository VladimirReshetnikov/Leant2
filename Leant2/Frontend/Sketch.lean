import Leant2.Frontend.Command
import Leant2.Frontend.Sketch.Run

/-! A closed whole-function sketch command. The identifier names the program
inside its contract; completed programs use the existing `it1`, ... aliases.
The fixed body is retained and all explicit holes share one continuation. -/

namespace Leant2.Frontend.Sketch
open Lean Meta Elab Command Term

syntax (name := sketchCommand) "#leant2_sketch " ident " : " term " := " term
  (" where " term)? : command

private def queryFromSyntax (name type : Syntax) (contract : Option Syntax) :
    TermElabM (Expr × Option Expr) :=
  tryCatchRuntimeEx (do
    let errorsBefore := ((← getThe Core.State).messages.toList.filter
      (·.severity == .error)).length
    let query ← elabQuery (some name) type contract
    unless ((← getThe Core.State).messages.toList.filter
        (·.severity == .error)).length == errorsBefore do
      throwError "query elaboration emitted an error"
    return query) fun ex => do
    if Leant2.isInterrupt ex || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
    throwError "leant2 sketch: preparation failed: {ex.toMessageData}"

/-- Supplementary source for the first certified completion. Fresh-process
replay is a separate check; the published kernel expression is authoritative. -/
private def reportSource (candidate : Accepted) : TermElabM Unit :=
  tryCatchRuntimeEx (do
    let termSyntax ← Presentation.programSyntax candidate.program
    let source ← PrettyPrinter.ppTerm termSyntax
    logInfo m!"leant2 sketch source:\n{source}") fun ex => do
      if Leant2.isInterrupt ex || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
      logInfo "leant2 sketch: completed a checked term; supplementary source was unavailable"

@[command_elab sketchCommand] def elabSketchCommand : CommandElab := fun stx => do
  let saved ← get
  let (result, _) ← tryFinally' (do
    let whereSyntax := if stx[6].getNumArgs > 0 then some stx[6][1] else none
    let result ← liftTermElabM do
      let (target, contract) ← queryFromSyntax stx[1] stx[3] whereSyntax
      synthesizeSketch {
        target, contract, profile := ← sessionProfile
        providers := curatedProviders ++ (← sessionConstants)
        budgetMs := leant2.budgetMs.get (← getOptions) } ⟨stx[5]⟩
    if let .verified candidates _ := result.outcome then
      bindIts candidates
    else
      clearCandidateBindings
    liftTermElabM do
      logInfo m!"leant2 sketch: prepared {result.preparation.holes.size} hole(s)"
      logInfo m!"leant2 sketch: {← outcomeMessage result.outcome}"
      if let .verified candidates _ := result.outcome then
        if let some candidate := candidates[0]? then reportSource candidate
      Core.checkInterrupted)
    fun result? => do if result?.isNone then set saved
  return result

end Leant2.Frontend.Sketch
