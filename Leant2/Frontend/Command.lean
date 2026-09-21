import Lean
import Leant2.Engine
import Leant2.Frontend.Results
/-!
# `#leant2` command

`#leant2 T` synthesizes inhabitants of `T` and reports them.
`#leant2 f : T where P` adds a contract.
`#leant2_check ...` fails unless at least one candidate is accepted;
`#leant2_none ...` fails if one is. Free lowercase names are auto-bound.
-/
namespace Leant2

open Lean Elab Command Term Meta

/-- Elaborate `T` and `P` (under `f : T`) into a closed target and contract. -/
def elabQuery (nameStx : Option Syntax) (tyStx : Syntax) (whereStx : Option Syntax) :
    TermElabM (Expr × Option Expr) := do
  -- no error recovery: an ill-typed query or assertion is a preflight error
  withoutErrToSorry <| withAutoBoundImplicit do
    let t ← elabType tyStx
    synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars t
    if t.hasSorry then throwError "leant2: the query type contains errors"
    let xs ← addAutoBoundImplicits #[] none
    let tc ← mkForallFVars xs t
    -- remaining universe metavariables stay flexible during search (`Type _` and
    -- auto-bound sorts are the user's placeholders); the gate generalizes them
    let tc ← instantiateMVars tc
    match whereStx with
    | none => return (tc, none)
    | some p =>
      let fname := match nameStx with
        | some n => n.getId
        | none => `f
      -- the contract binds f : (closed T)
      let c ← withLocalDeclD fname tc fun f => do
        let pe ← elabTerm p (some (mkSort Level.zero))
        synthesizeSyntheticMVarsNoPostponing
        let pe ← instantiateMVars pe
        if pe.hasSorry then throwError "leant2: the assertion contains errors"
        mkLambdaFVars #[f] pe
      return (tc, some (← instantiateMVars c))

/-- Session providers: constants declared after `Init`, plus a curated core set. -/
def curatedProviders : Array Name :=
  #[``List.map, ``List.foldr, ``List.foldl, ``List.flatten, ``List.append, ``List.replicate,
    ``List.reverse, ``List.length, ``List.filter, ``List.filterMap, ``List.zip, ``List.head?,
    ``Option.map, ``Option.bind, ``Option.getD, ``Nat.add, ``Nat.succ, ``Nat.zero,
    ``Except.map, ``Except.bind]

/-- Names declared in the current environment after the imports. -/
def sessionConstants : CoreM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.map₂.toList do
    if Presentation.isAuxiliaryName n || isResultName n then continue
    -- private declarations are ordinary session providers; other internal names are not
    if n.isInternal && !isPrivateName n then continue
    -- session bindings `it1`, `it2`, ... are results, not providers
    if let .str .anonymous s := n then
      if s.startsWith "it" && (s.drop 2).all Char.isDigit && s.length > 2 then continue
    -- compiler- and `deriving`-generated auxiliaries are noise as providers
    if isAuxRecursor env n || isNoConfusion env n || isRecCore env n || isCasesOnRecursor env n then continue
    if let .str _ s := n then
      if s ∈ ["noConfusionType", "sizeOf", "injEq", "inj", "sizeOf_spec", "ctorIdx", "ctorElim",
              "brecOn", "binductionOn", "below", "ibelow", "recOn", "casesOn", "ofNat", "toCtorIdx"] then continue
      if s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_" || s.startsWith "instDecidableEq" then continue
    -- instances of decision/printing classes are never term heads (`synthInstance?`
    -- finds them when needed); other instances stay, since an open class goal
    -- (`Choice ?a ?b`) is solved by applying the instance and unifying
    if (← isInstance n) then
      if let some cls := ci.type.getForallBody.getAppFn.constName? then
        if cls ∈ [``DecidableEq, ``Decidable, ``BEq, ``Repr, ``Hashable, ``Ord, ``ToString,
                  ``SizeOf, ``Nonempty, ``Inhabited, ``LawfulBEq] then continue
    -- a declaration that failed to elaborate is recorded with `sorryAx`: not a provider
    if ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false then continue
    match ci with
    | .axiomInfo _ | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .ctorInfo _ => out := out.push n
    | _ => pure ()
  return out

/-- Axioms declared in the session. They are accepted premises under the
project-relative profile (Section 3.4): the corpus models opaque providers
as `axiom` declarations. -/
def sessionAxioms : CoreM (List Name) := do
  let env ← getEnv
  let mut out := []
  for (n, ci) in env.constants.map₂.toList do
    if let .axiomInfo _ := ci then
      if n != ``sorryAx then out := n :: out
  return out

/-- The profile used for a session query. -/
def sessionProfile : CoreM Profile := do
  return .projectRelative (← sessionAxioms)

def outcomeMessage (o : Outcome) : MetaM MessageData := do
  match o with
  | .verified cands l =>
    let mut md := m!"{cands.size} candidate(s) [rules {l.ruleApplications}, proofs {l.proofAttempts}]"
    let mut i : Nat := 1
    for c in cands do
      let tag := if c.classical then " (classical)" else ""
      let axs := if c.axioms.isEmpty then "" else s!" axioms: {c.axioms.toList}"
      md := md ++ m!"\n  it{i}  {← Presentation.programMessage c.program}{tag}{axs}"
      i := i + 1
    return md
  | .refutedAll n _ => return m!"{n} program(s) of the type proposed, none passed the contract"
  | .negative .impossible (some cert) _ => return m!"provably uninhabited: {cert.program}"
  | .negative .impossible none _ => return m!"provably uninhabited"
  | .negative .contractImpossible _ _ => return m!"provably no program satisfies the contract"
  | .negative .grammarExhausted _ _ => return m!"no term found within the search bounds"
  | .negative .budgetExhausted _ _ => return m!"budget exhausted"
  | .preflightError s => return m!"error: {s}"

register_option leant2.budgetMs : Nat := {
  defValue := 20000
  descr := "leant2: wall-clock budget per query, in milliseconds"
}

def runQueryFromSyntax (nameStx : Option Syntax) (tyStx : Syntax) (whereStx : Option Syntax) :
    TermElabM Outcome := do
  let budgetMs := leant2.budgetMs.get (← getOptions)
  let (t, c) ← elabQuery nameStx tyStx whereStx
  let provs := curatedProviders ++ (← sessionConstants)
  let start ← IO.monoMsNow
  let o ← runQuery { target := t, contract := c, providers := provs, budgetMs,
                     profile := ← sessionProfile }
  let elapsed := (← IO.monoMsNow) - start
  logInfo m!"leant2: {elapsed} ms"
  return o

syntax (name := leant2Cmd) "#leant2 " (atomic(ident " : "))? term (" where " term)? : command
syntax (name := leant2Check) "#leant2_check " (atomic(ident " : "))? term (" where " term)? : command
syntax (name := leant2None) "#leant2_none " (atomic(ident " : "))? term (" where " term)? : command
/-- List the session declarations that act as providers, one per line. -/
syntax (name := leant2Providers) "#leant2_providers" : command

private def getParts (stx : Syntax) : Option Syntax × Syntax × Option Syntax :=
  let name? := if stx[1].getNumArgs > 0 then some stx[1][0] else none
  let ty := stx[2]
  let wh? := if stx[3].getNumArgs > 0 then some stx[3][1] else none
  (name?, ty, wh?)

@[command_elab leant2Cmd] def elabLeant2 : CommandElab := fun stx => do
  let (n, t, w) := getParts stx
  let o ← liftTermElabM <| runQueryFromSyntax n t w
  if let .verified cands _ := o then bindIts cands else clearCandidateBindings
  liftTermElabM do logInfo (← outcomeMessage o)

/-- REPL expression evaluation, retaining the certified expression as bare `it`.
The expression is elaborated and certified once; its immutable definition is
evaluated once here. An IO action is retained as an action, not its runtime
result. Failed evaluation leaves earlier result aliases unchanged. -/
syntax (name := leant2Eval) "#leant2_eval " term : command

@[command_elab leant2Eval] def elabLeant2Eval : CommandElab := fun stx => do
  let saved ← get
  set { saved with messages := {} }
  try
    let candidate ← liftTermElabM <| withoutErrToSorry do
      let value ← elabTerm stx[1] none
      synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      match ← gate (← sessionProfile) value (← inferType value) none with
      | .ok candidate => pure candidate
      | .error _ => throwError "leant2: evaluation result did not pass the acceptance gate"
    let name ← freshResultName
    discard <| Presentation.publish name candidate
    -- Reject a known name collision before evaluation can perform IO. The
    -- saved command state also rolls this binding back if evaluation fails.
    bindEvaluatedResult name
    elabCommand (← `(command| #eval $(mkIdent name)))
    if (← get).messages.hasErrors then
      let messages := (← get).messages
      set { saved with messages := saved.messages ++ messages }
    else
      modify fun state => { state with messages := saved.messages ++ state.messages }
  catch ex =>
    set saved
    throw ex

@[command_elab leant2Check] def elabLeant2Check : CommandElab := fun stx => do
  let (n, t, w) := getParts stx
  liftTermElabM do
    let o ← runQueryFromSyntax n t w
    match o with
    | .verified .. => logInfo (← outcomeMessage o)
    | _ => throwError "leant2_check failed: {← outcomeMessage o}"

@[command_elab leant2None] def elabLeant2None : CommandElab := fun stx => do
  let (n, t, w) := getParts stx
  liftTermElabM do
    let o ← runQueryFromSyntax n t w
    match o with
    | .verified .. => throwError "leant2_none failed: {← outcomeMessage o}"
    | _ => logInfo (← outcomeMessage o)

@[command_elab leant2Providers] def elabLeant2Providers : CommandElab := fun _ => do
  let names ← liftCoreM sessionConstants
  let names := names.qsort (fun a b => a.toString < b.toString)
  logInfo m!"providers: {names.toList}"

end Leant2
