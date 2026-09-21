import Leant2.Frontend.Presentation

/-! Session result names are replaceable aliases to immutable kernel declarations.
The alias state is intentionally not exported to importing modules. Environment
snapshots preserve it, so REPL undo/reset restore result names as well. -/
namespace Leant2

open Lean Elab Command

structure ResultBinding where
  name : Name
  target : Name
  aliases : Array Name
  deriving Inhabited

initialize resultBindingsExt : EnvExtension (Array ResultBinding) ←
  registerEnvExtension (pure #[])

/-- The current session result, independent of ordinary name resolution. -/
def resultBinding? (env : Environment) (name : Name) : Option Name :=
  (resultBindingsExt.getState env).findSome? fun b =>
    if b.name == name || b.aliases.contains name then some b.target else none

def isResultName (name : Name) : Bool := (`_leant2_result).isPrefixOf name

private def removeResultAliases (env : Environment) : Environment :=
  let bindings := resultBindingsExt.getState env
  SimplePersistentEnvExtension.modifyState aliasExtension env fun aliases =>
    bindings.foldl (init := aliases) fun aliases b =>
      b.aliases.foldl (init := aliases) fun aliases name =>
        aliases.insert name ((aliases.find? name).getD [] |>.filter (· != b.target))

/-- Replace only our aliases. A user declaration or unrelated alias is never
overwritten; collisions are reported before any new aliases are installed. -/
private def installResultBindings (bindings : Array ResultBinding) : CommandElabM Unit := do
  let env := removeResultAliases (← getEnv)
  for b in bindings do
    for name in b.aliases do
      if env.contains name || !(getAliases env name false).isEmpty then
        throwError "leant2: result name '{name}' conflicts with a user declaration or alias"
  let env := SimplePersistentEnvExtension.modifyState aliasExtension env fun aliases =>
    bindings.foldl (init := aliases) fun aliases b =>
      b.aliases.foldl (init := aliases) fun aliases name => aliases.insert name [b.target]
  setEnv (resultBindingsExt.setState env bindings)

private def mkResultBinding (name target : Name) : CommandElabM ResultBinding := do
  let qualified := (← getCurrNamespace) ++ name
  -- Lean strips `_root_` for real constants but not for transient aliases.
  let aliases := [name, qualified, rootNamespace ++ name, rootNamespace ++ qualified]
  return { name, target, aliases := aliases.eraseDups.toArray }

/-- A new immutable declaration; generation also checks imported names. -/
def freshResultName : CommandElabM Name := do
  let mut name ← liftCoreM <| mkFreshUserName `_leant2_result.value
  while (← getEnv).contains name do
    name ← liftCoreM <| mkFreshUserName `_leant2_result.value
  return name

/-- An unsuccessful, well-formed query has no numbered result. Bare `it`
continues to denote the most recent successfully published/evaluated value. -/
def clearCandidateBindings : CommandElabM Unit := do
  installResultBindings ((resultBindingsExt.getState (← getEnv)).filter (·.name == `it))

/-- Publish the whole candidate batch atomically. Old definitions remain
immutable; numbered aliases refer only to this batch, including when it shrinks. -/
def bindIts (cands : Array Accepted) : CommandElabM Unit := do
  let saved ← get
  set { saved with messages := {} }
  try
    let mut bindings := #[]
    let mut noncomputableNames : Array Name := #[]
    for i in [:cands.size] do
      let publicName := Name.mkSimple s!"it{i + 1}"
      let actualName ← freshResultName
      unless ← Presentation.publish actualName cands[i]! do
        noncomputableNames := noncomputableNames.push publicName
      bindings := bindings.push (← mkResultBinding publicName actualName)
    if let some first := bindings[0]? then
      bindings := bindings.push (← mkResultBinding `it first.target)
    installResultBindings bindings
    for name in noncomputableNames do
      logInfo m!"leant2: {name} is noncomputable; its certified kernel definition is available"
    modify fun state => { state with messages := saved.messages ++ state.messages }
  catch ex =>
    set saved
    throw ex

/-- Record a successfully evaluated value without replacing the synthesis batch. -/
def bindEvaluatedResult (name : Name) : CommandElabM Unit := do
  let bindings := (resultBindingsExt.getState (← getEnv)).filter (·.name != `it)
  installResultBindings (bindings.push (← mkResultBinding `it name))

end Leant2
