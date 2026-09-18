import Lean
import Leant2.Engine
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
    if n.isInternal then continue
    -- session bindings `it1`, `it2`, ... are results, not providers
    if let .str .anonymous s := n then
      if s.startsWith "it" && (s.drop 2).all Char.isDigit && s.length > 2 then continue
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
      md := md ++ m!"\n  it{i}  {c.program}{tag}{axs}"
      i := i + 1
    return md
  | .refutedAll n _ => return m!"{n} candidate(s) proposed, none passed the contract"
  | .negative .impossible (some cert) _ => return m!"provably uninhabited: {cert.program}"
  | .negative .impossible none _ => return m!"provably uninhabited"
  | .negative .grammarExhausted _ _ => return m!"no term found within the search bounds"
  | .negative .budgetExhausted _ _ => return m!"budget exhausted"
  | .preflightError s => return m!"error: {s}"

def runQueryFromSyntax (nameStx : Option Syntax) (tyStx : Syntax) (whereStx : Option Syntax)
    (budgetMs : Nat := 20000) : TermElabM Outcome := do
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

private def getParts (stx : Syntax) : Option Syntax × Syntax × Option Syntax :=
  let name? := if stx[1].getNumArgs > 0 then some stx[1][0] else none
  let ty := stx[2]
  let wh? := if stx[3].getNumArgs > 0 then some stx[3][1] else none
  (name?, ty, wh?)

@[command_elab leant2Cmd] def elabLeant2 : CommandElab := fun stx => do
  let (n, t, w) := getParts stx
  liftTermElabM do
    let o ← runQueryFromSyntax n t w
    logInfo (← outcomeMessage o)

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

end Leant2
