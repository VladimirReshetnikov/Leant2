import Leant2.Frontend.Results

/-! Imported, process-local sentinels for a sketch command cancellation test.
The delaborator is inert unless the test arms it, and only cancels after it
observes an actually installed, different result binding. No production hook
or supplied synthesis witness is involved. -/
namespace Leant2Tests.SketchEffects
open Lean PrettyPrinter Delaborator

def displayValue : Nat := 23

initialize token : IO.Ref (Option IO.CancelToken) ← IO.mkRef none
initialize previousBinding : IO.Ref (Option Name) ← IO.mkRef none
initialize observedBinding : IO.Ref (Option Name) ← IO.mkRef none

@[app_delab displayValue] def delabDisplayValue : Delab := do
  if let some cancellation ← token.get then
    let current := Leant2.resultBinding? (← getEnv) `it1
    if current.isSome && current != (← previousBinding.get) then
      observedBinding.set current
      cancellation.set
  return ⟨(mkIdent ``displayValue).raw⟩

end Leant2Tests.SketchEffects
