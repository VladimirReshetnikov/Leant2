import Lean
import Leant2.Core.Types
/-!
# The acceptance gate (unified proposal, Sections 13 and 20)

The only constructor of an accepted result. A candidate is a closed program
expression (and, when there is a contract, a closed proof). The gate:
instantiates and rejects remaining holes and escaped locals; adds the
declarations through the kernel-checked path with `debug.skipKernelTC` pinned
off; audits the transitive axiom closure against the profile.
-/
namespace Leant2

open Lean Meta

inductive GateFailure where
  | unresolvedHole
  | escapedLocal
  | kernelRejected (msg : String)
  | axiomViolation (bad : List Name)
  deriving Repr

/-- Kernel-check `e : ty` as a fresh definition in a scratch environment and
return the transitive axiom closure. The environment is not modified. -/
def kernelCheckAndAudit (baseName : Name) (e ty : Expr) (isProof : Bool) :
    MetaM (Except GateFailure (Array Name)) := do
  let e ← instantiateMVars e
  let ty ← instantiateMVars ty
  if e.hasMVar || ty.hasMVar || e.hasLevelMVar then return .error .unresolvedHole
  if e.hasFVar || ty.hasFVar then return .error .escapedLocal
  -- inside an asynchronous elaboration the environment only accepts names under a prefix
  let prefixName := match (← getEnv).asyncPrefix? with
    | some p => p
    | none => baseName
  let name := prefixName ++ (`_leant2_cand).appendIndexAfter (← IO.monoNanosNow)
  let lps := ((collectLevelParams {} ty).params ++ (collectLevelParams {} e).params).toList.eraseDups
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
  let axsP ← kernelCheckAndAudit `Leant2 program programTy false
  let axsP ← match axsP with | .ok a => pure a | .error f => return .error f
  let mut axs := axsP
  let mut proofE := mkConst ``True.intro
  if let some (p, pty) := proof? then
    match ← kernelCheckAndAudit `Leant2 p pty true with
    | .ok a => axs := axs ++ a; proofE := p
    | .error f => return .error f
  let allowed := profile.allowedAxioms
  let bad := axs.toList.filter (fun a => !allowed.contains a)
  if !bad.isEmpty then return .error (.axiomViolation bad)
  let classical := axs.contains ``Classical.choice
  return .ok { program := program, proof := proofE, axioms := axs.toList.eraseDups.toArray,
               classical := classical }

end Leant2
