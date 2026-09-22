import Leant2.Frontend.Sketch.Run

/-!
UNVALIDATED DRAFT: no native compilation or synthesis result is claimed.
Exact church_case_039 supplied-default type and all 36 original observations.
One fixed Option carrier; step, init, finish are all open. Empty explicit
providers and strict constructive profile. Never import Controls.lean here.
-/

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
def BehaviorPartial.check_foldr1 (f : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0))))) : Bool := ((((((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((-99) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((-99) : Int))) && ((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)))) && (((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((6) : Int)) && (((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((23) : Int))) && ((((f) (Int) (((-99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((8) : Int)) && ((((f) (Int) (((-99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((7) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((99) : Int)))))) && ((((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([] : (List Int))))) == ((99) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int))) && ((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(-5)] : (List Int))))) == ((-5) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((6) : Int)))) && (((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(8),(3),(1)] : (List Int))))) == ((23) : Int)) && (((f) (Int) (((99) : Int)) ((fun x y => x - y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((8) : Int))) && ((((f) (Int) (((99) : Int)) ((fun x y => 2*x + y)) ((BehaviorPartial.enc ([(2),(-3),(4),(1)] : (List Int))))) == ((7) : Int)) && ((((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([] : (List Bool))))) == (false : Bool)) && (((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false] : (List Bool))))) == (false : Bool))))))) && (((((((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([true] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((false : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false,true,false] : (List Bool))))) == (true : Bool))) && ((((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false] : (List Bool))))) == (false : Bool)))) && (((((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([true] : (List Bool))))) == (true : Bool)) && (((f) (Bool) ((true : Bool)) ((fun x y => (!x) || y)) ((BehaviorPartial.enc ([false,true,false] : (List Bool))))) == (true : Bool))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(-99)] : (List Int))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(-99)] : (List Int))) && (((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))))))) && ((((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))) && (((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(2),(3),(4)] : (List Int)))) && ((((f) ((List Int)) (([(-99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(3),(2),(4)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(99)] : (List Int))))) && (((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([] : (List (List Int)))))) == ([(99)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int)))) && ((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)]] : (List (List Int)))))) == ([(1)] : (List Int))) && ((((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(2),(3),(4)] : (List Int))) && (((f) ((List Int)) (([(99)] : (List Int))) ((fun x y => x.reverse ++ y)) ((BehaviorPartial.enc ([[(1)],[(2),(3)],[(4)]] : (List (List Int)))))) == ([(1),(3),(2),(4)] : (List Int)))))))))

namespace Foldr1CarrierProbe
open Lean Meta Elab
open Lean.Elab.Term hiding mkConst
open Leant2 Leant2.Frontend.Sketch

private def complete (value : Expr) : Bool :=
  !value.hasMVar && !value.hasFVar && !value.hasLooseBVars && !value.hasSorry

private def printWork (work : Ledger) : TermElabM Unit :=
  IO.println s!"PROBE_LEDGER {reprStr work}"

private def checkProgramDependencies (program : Expr) : MetaM Nat := do
  let mut pending := program.getUsedConstants
  let mut visited : Std.HashSet Name := {}
  let mut cursor := 0
  while cursor < pending.size do
    Core.checkInterrupted
    let name := pending[cursor]!
    cursor := cursor + 1
    if visited.contains name then continue
    visited := visited.insert name
    if (`BehaviorPartial).isPrefixOf name || (`BehaviorPartialOracle).isPrefixOf name ||
        (`BehaviorPartialControl).isPrefixOf name || (`Foldr1CarrierControl).isPrefixOf name then
      throwError "completed program used an excluded observer/reference dependency: {name}"
    let info ← getConstInfo name
    pending := pending ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  return visited.size

private def validateCandidate (query : Query) (candidate : Accepted) (index : Nat) : TermElabM Unit := do
  let some contract := query.contract | throwError "probe lost its original contract"
  unless [candidate.program, candidate.programType, candidate.proof].all complete do
    throwError "probe received an incomplete accepted object"
  unless ← isDefEq candidate.programType query.target do
    throwError "probe changed the exact original supplied-default type"
  let .ok programAxioms ← kernelCheckAndAudit `Foldr1CarrierProbe
      candidate.program query.target candidate.levelParams false
    | throwError "program failed independent replay at the original target"
  let .ok proofAxioms ← kernelCheckAndAudit `Foldr1CarrierProbe
      candidate.proof (mkApp contract candidate.program) candidate.levelParams true
    | throwError "proof failed independent replay of all 36 original observations"
  unless programAxioms.isEmpty && proofAxioms.isEmpty &&
      candidate.axioms.isEmpty && !candidate.classical do
    throwError "strict constructive foldr1 acceptance introduced an axiom"
  -- The file declares no reference implementations. All observer declarations
  -- have this namespace; they are needed in the contract, never the program.
  -- Native constructors/case analysis are still available with providers #[];
  -- this is not a whitelist of every constant occurring in native proofs.
  let dependencyCount ← checkProgramDependencies candidate.program
  let constants := candidate.program.getUsedConstants
  IO.println s!"PROBE_CANDIDATE {index} original_type_replayed=true original_observations_replayed=36 strict_axioms=0"
  IO.println s!"PROBE_PROGRAM_TYPE {← ppExpr candidate.programType}"
  IO.println s!"PROBE_PROGRAM {← ppExpr candidate.program}"
  IO.println s!"PROBE_PROGRAM_CONSTANTS {constants.toList}"
  IO.println s!"PROBE_PROGRAM_DEPENDENCIES_REVIEWED {dependencyCount}"

run_elab do
  let budgetText := (← IO.getEnv "LEANT2_SKETCH_PROBE_BUDGET_MS").getD "5000"
  let some budget := budgetText.toNat? | throwError "probe budget is not a natural number"
  unless budget == 5000 || budget == 10000 do
    throwError "this probe uses the unchanged source at the established 5000/10000 ms budgets"
  let target ← elabType (← `((∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0))))))
  let contract ← elabTerm (← `(fun f : (∀ (church0 : Type), (church0 → ((church0 → (church0 → church0)) → ((∀ (church1 : Type), ((church0 → (church1 → church1)) → (church1 → church1))) → church0)))) => BehaviorPartial.check_foldr1 (f) = true)) none
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let contract ← instantiateMVars contract
  let query : Query := {
    target, contract := some contract, profile := .strictConstructive
    providers := #[], budgetMs := budget, maxCandidates := 1, graceMs := 0 }
  let sketch ← `(
    fun (A : Type) (d : A) (combine : A → A → A) =>
      (fun (step : A → Option A → Option A) (init : Option A)
           (finish : Option A → A)
           (xs : ∀ R : Type, (A → R → R) → R → R) =>
        finish (xs (Option A) step init)) ?step ?init ?finish)
  IO.println s!"PROBE_BEGIN case=church_case_039 operation=foldr1 observations=36 providers=0 profile=strictConstructive budgetMs={budget}"
  let start ← IO.monoMsNow
  let result ← synthesizeSketch query sketch
  IO.println s!"PROBE_ELAPSED_MS {(← IO.monoMsNow) - start}"
  IO.println s!"PROBE_PREPARATION {reprStr result.preparation}"
  unless result.preparation.holes.size == 3 &&
      result.preparation.holes.map (fun hole => hole.sourceName.eraseMacroScopes) == #[`step, `init, `finish] do
    throwError "the probe did not retain all three named open holes in source order"
  match result.outcome with
  | .verified candidates work =>
    IO.println s!"PROBE_OUTCOME verified candidates={candidates.size}"
    printWork work
    unless !candidates.isEmpty do throwError "verified outcome was empty"
    for index in [:candidates.size] do
      validateCandidate query candidates[index]! index
    IO.println "PROBE_ACCEPTED exact_type_and_all_36_observations_replayed"
  | .refutedAll rejected work =>
    IO.println s!"PROBE_OUTCOME refutedAll rejected={rejected}"
    printWork work
    IO.println "PROBE_NOT_ACCEPTED bounded_proposals_failed_no_impossibility_claim"
  | .negative kind certificate work =>
    IO.println s!"PROBE_OUTCOME negative kind={reprStr kind} certificate={certificate.isSome}"
    printWork work
    if let some candidate := certificate then
      IO.println s!"PROBE_NEGATIVE_STATEMENT {← ppExpr candidate.programType}"
      IO.println s!"PROBE_NEGATIVE_CERTIFICATE {← ppExpr candidate.program}"
    IO.println "PROBE_NOT_ACCEPTED inspect_negative_kind_and_certificate"
  | .preflightError message =>
    IO.println s!"PROBE_OUTCOME preflightError {message}"
    throwError "probe input failed preflight: {message}"

end Foldr1CarrierProbe
