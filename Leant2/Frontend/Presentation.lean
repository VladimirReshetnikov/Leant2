import Lean
import Leant2.Accept.Gate
/-!
# Compiling certified results

The kernel term remains the value of the published declaration. When it uses a
primitive recursor, generate a structurally recursive implementation from the
kernel's reduction rules and prove the two recursors equal. Lean's `csimp`
attribute then supplies the compiler with this checked implementation.

Unsupported recursors and genuinely noncomputable providers retain their
certified definitions; a failed compilation never invalidates acceptance.
-/
namespace Leant2

open Lean Elab Command Term Meta

namespace Presentation

/-- Generated adapters, their equations, and their proof lemmas are compiler
support, not additional session providers. -/
def isAuxiliaryName (name : Name) : Bool :=
  (name.toString.splitOn ".").any (·.startsWith "_leant2_compiled")

private def syntaxOptions (opts : Options) : Options :=
  opts.setBool `pp.explicit true |>.setBool `pp.universes true |>.setBool `pp.fullNames true

private def delab (e : Expr) : MetaM (TSyntax `term) :=
  withOptions syntaxOptions <| PrettyPrinter.delab e

/-- Open a telescope with deterministic, collision-free binder names. -/
private partial def openBinders (e : Expr) (count : Nat) (namePrefix : String)
    (k : Array Expr → Expr → MetaM α) (xs : Array Expr := #[]) : MetaM α := do
  if count == 0 then return ← k xs e
  match e with
  | .forallE _ ty body bi | .lam _ ty body bi =>
    let name := (← getLCtx).getUnusedName (Name.mkSimple s!"{namePrefix}{xs.size}")
    withLocalDecl name bi ty fun x =>
      openBinders (body.instantiate1 x) (count - 1) namePrefix k (xs.push x)
  | _ => throwError "leant2 presentation: malformed recursor telescope"

private def identOf (x : Expr) : MetaM Ident :=
  return mkIdent (← x.fvarId!.getUserName)

private def matchAlt := Parser.Term.matchAlt (rhsParser := Parser.termParser)

/-- Render primitive recursion using the very same constructor reduction rules
used by the compiler adapter. The display is supplementary: the stored and
audited object is always the original expression. -/
partial def programSyntax (e : Expr) : MetaM (TSyntax `term) := do
  let fn := e.getAppFn
  if let .const recName _ := fn then
    if isCasesOnRecursor (← getEnv) recName then
      if let some unfolded ← unfoldDefinition? e then
        return ← programSyntax unfolded
    if let some (.recInfo info) := (← getEnv).find? recName then
      if info.all.length == 1 && info.numIndices == 0 && info.numMotives == 1 &&
          e.getAppNumArgs > info.getMajorIdx then
        let args := e.getAppArgs
        let fixed := args.extract 0 info.getMajorIdx
        let goType ← inferType (mkAppN fn fixed)
        let fresh ← mkFreshId
        let goName := (← getLCtx).getUnusedName <| Name.mkSimple <|
          match fresh with
          | .num _ i => s!"loop{i}"
          | _ => s!"loop{fresh.hash}"
        return ← withLocalDeclD goName goType fun go =>
          openBinders goType 1 "value" fun majors _ => do
            let major := majors[0]!
            let mut recursive := false
            let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
            for rule in info.rules do
              let rhs := rule.rhs.instantiateLevelParams info.levelParams fn.constLevels!
              let rhs := (mkAppN rhs fixed).headBeta
              let (alt, usesRec) ← openBinders rhs rule.nfields "field" fun fields rhs => do
                let rhs := rhs.headBeta
                let rhs := rhs.replace fun sub =>
                  if sub.getAppFn == fn && sub.getAppNumArgs > info.getMajorIdx &&
                      sub.getAppArgs.extract 0 info.getMajorIdx == fixed then
                    some (mkAppN go (sub.getAppArgs.extract info.getMajorIdx sub.getAppNumArgs))
                  else none
                let usesRec := rhs.containsFVar go.fvarId!
                let rhs ← programSyntax rhs
                let fieldIds ← fields.mapM identOf
                let params ← (List.range info.numParams).toArray.mapM fun _ => `(term| _)
                let pat ← `(term| @$(mkIdent rule.ctor) $params* $fieldIds*)
                let alt ← `(matchAlt| | $pat => $rhs)
                return ((⟨alt.raw⟩ : TSyntax ``Parser.Term.matchAlt), usesRec)
              alts := alts.push alt
              recursive := recursive || usesRec
            let value ← programSyntax args[info.getMajorIdx]!
            let result ← if recursive then do
              let majorId ← identOf major
              let goId ← identOf go
              let goType ← PrettyPrinter.delab goType
              `(term| let rec $goId:ident : $goType := fun $majorId =>
                (match $majorId:term with $alts:matchAlt*); $goId $value)
            else
              `(term| match $value:term with $alts:matchAlt*)
            let rest ← (args.extract (info.getMajorIdx + 1) args.size).mapM programSyntax
            if rest.isEmpty then return result
            `(term| ($result) $rest*)
  match e with
  | .lam n ty body bi =>
    let n := (← getLCtx).getUnusedName (if n.isAnonymous then `arg else n)
    withLocalDecl n bi ty fun x => do
      let id := mkIdent n
      let ty ← PrettyPrinter.delab ty
      let body ← programSyntax (body.instantiate1 x)
      match bi with
      | .implicit => `(term| fun {$id : $ty} => $body)
      | .strictImplicit => `(term| fun ⦃$id : $ty⦄ => $body)
      | .instImplicit => `(term| fun [$id : $ty] => $body)
      | .default => `(term| fun ($id : $ty) => $body)
  | .app .. =>
    let env ← getEnv
    let hasRecursor := e.foldConsts (init := false) fun n found =>
      found || isCasesOnRecursor env n || (env.find? n matches some (.recInfo _))
    if hasRecursor then
      let head ← match e.getAppFn with
        | .const n _ => pure (⟨(mkIdent n).raw⟩ : TSyntax `term)
        | fn => programSyntax fn
      let args ← e.getAppArgs.mapM programSyntax
      `(term| (@$head $args*))
    else PrettyPrinter.delab e
  | .letE n ty value body _ =>
    let n := (← getLCtx).getUnusedName n
    let tyStx ← PrettyPrinter.delab ty
    let value ← programSyntax value
    withLocalDeclD n ty fun x => do
      let body ← programSyntax (body.instantiate1 x)
      `(term| let $(mkIdent n):ident : $tyStx := $value; $body)
  | .mdata _ body => programSyntax body
  | _ => PrettyPrinter.delab e

def programMessage (e : Expr) : MetaM MessageData := do
  try
    return .ofFormat (← PrettyPrinter.ppTerm (← programSyntax e))
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
    return m!"{e}"

private def recursorCommands (info : RecursorVal) (implName proofName : Name) :
    MetaM (Syntax × Syntax) := do
  unless info.all.length == 1 && info.numIndices == 0 && info.numMotives == 1 do
    throwError "leant2 presentation: indexed and mutual recursors are not supported"
  let levels := info.levelParams.toArray.map mkIdent
  let declId ← `(declId| $(mkIdent implName).{$levels,*})
  let proofId ← `(declId| $(mkIdent proofName).{$levels,*})
  let type ← delab info.type
  let (body, ids) ← withLocalDeclD implName info.type fun self =>
    openBinders info.type (info.getMajorIdx + 1) "arg" fun xs _ => do
      let ids ← xs.mapM identOf
      let major := ids.back!
      let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
      for rule in info.rules do
        let rhs := (mkAppN rule.rhs (xs.extract 0 info.getMajorIdx)).headBeta
        let alt ← openBinders rhs rule.nfields "field" fun fields rhs => do
          let fieldIds ← fields.mapM identOf
          let params ← (List.range info.numParams).toArray.mapM fun _ => `(term| _)
          let rhs := rhs.replace fun e =>
            if e.isConstOf info.name then some self else none
          let rhs ← delab rhs
          let pat ← `(term| @$(mkIdent rule.ctor) $params* $fieldIds*)
          let alt ← `(matchAlt| | $pat => $rhs)
          return (⟨alt.raw⟩ : TSyntax ``Parser.Term.matchAlt)
        alts := alts.push alt
      let body ← `(term| @fun $ids* => match $major:term with $alts:matchAlt*)
      return (body, ids)
  let defCmd ← `(command| def $declId:declId : $type := $body)
  let us := info.levelParams.map Level.param
  let eqType ← withoutModifyingEnv do
    addDecl <| .axiomDecl {
      name := implName, levelParams := info.levelParams, type := info.type, isUnsafe := false }
    delab (← mkEq (mkConst info.name us) (mkConst implName us))
  let major := ids.back!
  let proofCmd ← `(command| theorem $proofId:declId : $eqType := by
    funext $ids*
    induction $major:term <;> simp_all only [$(mkIdent implName):term])
  return (defCmd, proofCmd)

/-- Add a compiler adapter only after its equality theorem is checked. All
declarations and diagnostics from an unsuccessful attempt are rolled back. -/
def ensureRecursor (recName : Name) : CommandElabM Bool := do
  if (Compiler.CSimp.ext.getState (← getEnv)).map.contains recName then return true
  let some (.recInfo info) := (← getEnv).find? recName | return false
  let saved ← get
  try
    withScope (fun s => { s with
        currNamespace := .anonymous, levelNames := [], opts := s.opts.setBool `Elab.async false
          |>.setBool `debug.skipKernelTC false }) do
      let implName ← liftCoreM <| mkFreshUserName (recName ++ `_leant2_compiled)
      let proofName ← liftCoreM <| mkFreshUserName (recName ++ `_leant2_compiled_eq)
      let (defCmd, proofCmd) ← liftTermElabM <| recursorCommands info implName proofName
      elabCommand defCmd
      elabCommand proofCmd
      if (← get).messages.hasErrors then throwError "leant2 presentation: elaboration failed"
      let ci ← liftCoreM <| getConstInfo proofName
      if ci.type.hasSorry || (ci.value? (allowOpaque := true) |>.map (·.hasSorry)).getD true then
        throwError "leant2 presentation: incomplete equality proof"
      let checked ← liftTermElabM <| kernelCheckAndAudit proofName
        (ci.value! (allowOpaque := true)) ci.type ci.levelParams true
      match checked with
      | .error _ => throwError "leant2 presentation: equality failed the kernel check"
      | .ok axioms =>
        unless axioms.all Profile.standard.allowedAxioms.contains do
          throwError "leant2 presentation: equality depends on an unsupported axiom"
      liftCoreM <| Compiler.CSimp.add proofName .global
      return true
  catch ex =>
    let messages := (← get).messages
    set saved
    if ex.isInterrupt || ex.isRuntime then throw ex
    if leant2.trace.get (← getOptions) then
      logInfo m!"leant2 presentation: {ex.toMessageData}"
      for msg in messages.toList do
        if msg.severity == .error then logInfo msg.data
    return false

/-- Compile a result, retaining its exact certified kernel value. Returns
whether executable code was produced. -/
def publish (name : Name) (c : Accepted) : CommandElabM Bool := do
  let decl : Declaration := .defnDecl {
    name, levelParams := c.levelParams, type := c.programType, value := c.program,
    hints := .abbrev, safety := .safe }
  withScope (fun s => { s with opts := s.opts.setBool `Elab.async false }) do
    liftCoreM <| addDecl decl
    let env ← getEnv
    let recursors := c.program.foldConsts (init := #[]) fun n acc =>
      if env.find? n matches some (.recInfo _) then acc.push n else acc
    for n in recursors do discard <| ensureRecursor n
    try
      liftCoreM <| compileDecl decl
    catch ex =>
      if ex.isInterrupt || ex.isRuntime then throw ex
    liftTermElabM <| saveEqnAffectingOptions name
    liftCoreM <| enableRealizationsForConst name
    return !isNoncomputable (← getEnv) name

end Presentation
end Leant2
