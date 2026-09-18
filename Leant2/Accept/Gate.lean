import Lean
import Leant2.Core.Types
/-!
# The acceptance gate (unified proposal, Sections 13 and 20)

The only constructor of an accepted result. A candidate is a closed program
expression (and, when there is a contract, a closed proof). The gate:
instantiates and rejects remaining holes and escaped locals; generalizes the
remaining universe metavariables to parameters; adds the declarations
through the synchronous kernel-checked path (the `Except` result is the
positive signal that the checker ran); audits the transitive axiom closure
against the profile.
-/
namespace Leant2

open Lean Meta

inductive GateFailure where
  | unresolvedHole
  | escapedLocal
  | kernelRejected (msg : String)
  | axiomViolation (bad : List Name)
  deriving Repr

/-- Replace level metavariables in `l` using `f`. -/
partial def replaceLevelMVars (f : LMVarId → Level) : Level → Level
  | .mvar id => f id
  | .succ l => .succ (replaceLevelMVars f l)
  | .max a b => .max (replaceLevelMVars f a) (replaceLevelMVars f b)
  | .imax a b => .imax (replaceLevelMVars f a) (replaceLevelMVars f b)
  | l => l

/-- Replace level metavariables in every sort and constant of `e`. -/
def replaceExprLevelMVars (f : LMVarId → Level) (e : Expr) : Expr :=
  e.replace fun
    | .sort l => some (.sort (replaceLevelMVars f l))
    | .const n ls => some (.const n (ls.map (replaceLevelMVars f)))
    | _ => none

/-- Collect the level metavariables of `e` in order of first occurrence. -/
def collectLevelMVarIds (e : Expr) : Array LMVarId := Id.run do
  let mut out : Array LMVarId := #[]
  let rec goL (l : Level) (out : Array LMVarId) : Array LMVarId :=
    match l with
    | .mvar id => if out.contains id then out else out.push id
    | .succ l => goL l out
    | .max a b | .imax a b => goL b (goL a out)
    | _ => out
  let mut stack : List Expr := [e]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | x :: rest =>
      stack := rest
      match x with
      | .sort l => out := goL l out
      | .const _ ls => for l in ls do out := goL l out
      | .app f a => stack := f :: a :: stack
      | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
      | .letE _ t v b _ => stack := t :: v :: b :: stack
      | .mdata _ b | .proj _ _ b => stack := b :: stack
      | _ => pure ()
  return out

/-- Generalize the remaining level metavariables of `es` to fresh universe
parameters `u_1, u_2, ...` (after the existing parameters). Returns the
rewritten expressions and the full parameter list. -/
def generalizeLevels (es : List Expr) : MetaM (List Expr × List Name) := do
  let es ← es.mapM fun e => do instantiateMVars e
  let existing := es.foldl (fun acc e => (collectLevelParams acc e)) {} |>.params.toList
  let ids := es.foldl (fun acc e => acc ++ (collectLevelMVarIds e).filter (!acc.contains ·)) #[]
  let mut names : List Name := []
  let mut i := existing.length + 1
  let mut map : Array (LMVarId × Level) := #[]
  for id in ids do
    let mut n := Name.mkSimple s!"u_{i}"
    while existing.contains n || names.contains n do
      i := i + 1
      n := Name.mkSimple s!"u_{i}"
    names := names ++ [n]
    map := map.push (id, .param n)
    i := i + 1
  let f : LMVarId → Level := fun id => (map.find? (·.1 == id)).map (·.2) |>.getD (.mvar id)
  return (es.map (replaceExprLevelMVars f), existing ++ names)

/-- Kernel-check `e : ty` as a fresh declaration in a scratch environment and
return the transitive axiom closure. The environment is not modified. The
inputs must already be free of level metavariables. -/
def kernelCheckAndAudit (baseName : Name) (e ty : Expr) (lps : List Name) (isProof : Bool) :
    MetaM (Except GateFailure (Array Name)) := do
  if e.hasMVar || ty.hasMVar || e.hasLevelMVar || ty.hasLevelMVar then
    return .error .unresolvedHole
  if e.hasFVar || ty.hasFVar then return .error .escapedLocal
  -- inside an asynchronous elaboration the environment only accepts names under a prefix
  let prefixName := match (← getEnv).asyncPrefix? with
    | some p => p
    | none => baseName
  let name := prefixName ++ (`_leant2_cand).appendIndexAfter (← IO.monoNanosNow)
  let decl : Declaration :=
    if isProof then
      .thmDecl { name := name, levelParams := lps, type := ty, value := e }
    else
      .defnDecl { name := name, levelParams := lps, type := ty, value := e, hints := .abbrev,
                  safety := .safe }
  -- Synchronous kernel check: the `Except` result is the positive signal that the
  -- checker ran (Section 13.1). `doCheck := true` bypasses `debug.skipKernelTC`.
  let opts ← getOptions
  let env ← getEnv
  match env.addDeclCore (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize
      decl none (doCheck := true) with
  | .error ex =>
    let md := ex.toMessageData opts
    return .error (.kernelRejected (← md.toString))
  | .ok env' =>
    withoutModifyingEnv do
      setEnv env'
      let axs ← collectAxioms name
      return .ok axs

/-- Run the gate on a program and an optional contract proof. -/
def gate (profile : Profile) (program programTy : Expr) (proof? : Option (Expr × Expr)) :
    MetaM (Except GateFailure Accepted) := do
  let program ← instantiateMVars program
  let programTy ← instantiateMVars programTy
  -- expression holes are fatal; level metavariables are generalized below
  if program.hasExprMVar || programTy.hasExprMVar then return .error .unresolvedHole
  -- generalize universe metavariables jointly across program, type, proof, and proof type
  let all := [program, programTy] ++ (match proof? with | some (p, pty) => [p, pty] | none => [])
  let (gen, lps) ← generalizeLevels all
  let (program, programTy) := (gen[0]!, gen[1]!)
  let axsP ← kernelCheckAndAudit `Leant2 program programTy lps false
  let axsP ← match axsP with | .ok a => pure a | .error f => return .error f
  let mut axs := axsP
  let mut proofE := mkConst ``True.intro
  if proof?.isSome then
    let (p, pty) := (gen[2]!, gen[3]!)
    match ← kernelCheckAndAudit `Leant2 p pty lps true with
    | .ok a => axs := axs ++ a; proofE := p
    | .error f => return .error f
  let allowed := profile.allowedAxioms
  let bad := axs.toList.filter (fun a => !allowed.contains a)
  if !bad.isEmpty then return .error (.axiomViolation bad)
  let classical := axs.contains ``Classical.choice
  return .ok { program := program, programType := programTy, levelParams := lps,
               proof := proofE, axioms := axs.toList.eraseDups.toArray, classical := classical }

end Leant2
