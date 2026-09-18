import Lean
import Leant2
/-!
# `leant2`: the compatibility REPL (unified proposal, Section 14.2)

Reads a Leant-style transcript from standard input. Session declarations are
elaborated into the session environment; `:synth T` and
`:synth f : T where P` run the engine; every `:set` line is accepted and
ignored (Decision 1.1); `:reset` starts a fresh environment; `:quit` exits.
Lines that are neither commands nor declarations are evaluated as terms.

Output is outcome-oriented: each query prints one of
`  itN  <term>` lines, `provably uninhabited`, `no term found within the
search bounds`, `budget exhausted`, or `error: ...`.
-/

open Lean Elab Meta Leant2

structure Session where
  env : Environment
  opts : Options
  budgetMs : Nat
  itCounter : Nat := 0
  /-- Statement of the current `:prove`, if any. A bare `:synth` inside prove
  mode synthesizes the whole statement (the outcome category is the same as
  synthesizing the goal after the user's tactics). -/
  proving : Option String := none

def leanKeywords : List String :=
  ["def", "theorem", "lemma", "inductive", "structure", "class", "instance", "axiom", "opaque",
   "abbrev", "universe", "namespace", "end", "open", "set_option", "#eval", "#check", "#print",
   "#reduce", "example", "variable", "section", "noncomputable", "private", "protected",
   "deriving", "attribute", "mutual", "@[", "/-", "--", "unsafe", "partial", "macro", "syntax",
   "elab", "notation", "infix", "prefix", "postfix"]

def startsWithKeyword (s : String) : Bool :=
  let t := s.trimLeft
  leanKeywords.any fun k => t.startsWith k && (t.length == k.length || !(t.get ⟨k.length⟩).isAlphanum)

/-- Elaborate a chunk of Lean commands in the session environment, printing
messages. -/
def elabChunk (s : Session) (src : String) : IO Session := do
  let inputCtx := Parser.mkInputContext src "<repl>"
  let cmdState := Command.mkState s.env {} s.opts
  let st ← IO.processCommands inputCtx {} cmdState
  for msg in st.commandState.messages.toList do
    let str ← msg.toString
    IO.println str.trimRight
  return { s with env := st.commandState.env }

def runMeta (s : Session) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<repl>", fileMap := default, options := s.opts,
                              maxHeartbeats := 0 }
  let (a, _) ← (x.run' {} {}).toIO ctx { env := s.env }
  return a

def runTerm (s : Session) (x : Term.TermElabM α) : IO α :=
  runMeta s (x.run' {} {})

/-- Split `:synth` arguments into (name?, type, where?). -/
def splitSynth (arg : String) : Option String × String × Option String :=
  let arg := arg.trim
  match arg.splitOn " where " with
  | [ty] => (none, ty, none)
  | ty :: rest =>
    let wh := " where ".intercalate rest
    -- named form: `f : T`
    let parts := ty.splitOn " : "
    match parts with
    | n :: tyParts =>
      if tyParts.length ≥ 1 && n.trim.all (fun c => c.isAlphanum || c == '_' || c == '\'') then
        (some n.trim, " : ".intercalate tyParts, some wh)
      else (none, ty, some wh)
    | _ => (none, ty, some wh)
  | _ => (none, arg, none)

def parseTerm (env : Environment) (src : String) : Except String Syntax :=
  Parser.runParserCategory env `term src "<synth>"

def bindIts (s : Session) (cands : Array Accepted) : IO Session := do
  let mut s := s
  let mut i := 1
  for c in cands do
    let name := Name.mkSimple s!"it{i}"
    if !(s.env.contains name) then
      let decl : Declaration := .defnDecl {
        name := name, levelParams := c.levelParams, type := c.programType, value := c.program,
        hints := .abbrev, safety := .safe }
      match s.env.addDeclCore 0 512 decl none true with
      | .ok env' => s := { s with env := env' }
      | .error _ => pure ()
    i := i + 1
  return s

def doSynth (s : Session) (arg : String) : IO Session := do
  let (name?, tyStr, wh?) := splitSynth arg
  let tyStx ← match parseTerm s.env tyStr with
    | .ok stx => pure stx
    | .error e => IO.println s!"error: {e}"; return s
  let whStx? ← match wh? with
    | none => pure none
    | some w => match parseTerm s.env w with
      | .ok stx => pure (some stx)
      | .error e => IO.println s!"error: {e}"; return s
  let nameStx := name?.map fun n => mkIdent (Name.mkSimple n)
  let r ← try
      runTerm s do
        let (t, c) ← elabQuery nameStx tyStx whStx?
        let provs := curatedProviders ++ (← sessionConstants)
        let start ← IO.monoMsNow
        let o ← runQuery { target := t, contract := c, providers := provs, budgetMs := s.budgetMs,
                           profile := ← sessionProfile }
        let elapsed := (← IO.monoMsNow) - start
        let msg ← addMessageContextFull (← outcomeMessage o)
        let str ← msg.toString
        let cands := match o with | .verified cs _ => cs | _ => #[]
        return (str, elapsed, cands)
    catch e =>
      let str : String := toString e
      IO.println s!"error: {(str.splitOn "\n").headD str}"
      return s
  let (str, elapsed, cands) := r
  -- drop the leading "N candidate(s) [...]" line; keep the itN lines
  let lines := str.splitOn "\n"
  for l in lines do
    if l.startsWith "  it" || !(l.contains '[') then IO.println l
  IO.println s!"-- {elapsed} ms"
  bindIts s cands

partial def loop (s : Session) (lines : List String) (chunk : List String) : IO Unit := do
  let flush (s : Session) : IO Session := do
    if chunk.isEmpty then return s
    let src := "\n".intercalate chunk.reverse
    let src := if startsWithKeyword src then src else s!"#eval ({src.trim})"
    elabChunk s src
  match lines with
  | [] => let _ ← flush s; pure ()
  | l :: rest =>
    let t := l.trimRight
    if t.startsWith ":" then
      let s ← flush s
      IO.println s!"λ> {t}"
      let body : String := (t.drop 1).toString
      let cmd : String := (body.takeWhile (· != ' ')).toString
      let arg : String := ((body.dropWhile (· != ' ')).toString).trim
      match cmd with
      | "quit" => pure ()
      | "set" => loop s rest []
      | "reset" =>
        let s' ← freshSession s.budgetMs
        loop s' rest []
      | "prove" =>
        IO.println "entering prove mode (leant2: tactic lines are ignored)"
        loop { s with proving := some arg } rest []
      | "qed" | "abort" => loop { s with proving := none } rest []
      | "synth" =>
        let arg := if arg.isEmpty then s.proving.getD "" else arg
        let s ← doSynth s arg
        loop s rest []
      | "type" =>
        let s ← elabChunk s s!"#check ({arg})"
        loop s rest []
      | _ => IO.println s!"(ignored :{cmd})"; loop s rest []
    else if t.isEmpty then
      let s ← flush s
      loop s rest []
    else if s.proving.isSome then
      -- tactic lines inside prove mode
      loop s rest []
    else if (l.get 0).isWhitespace || l.startsWith "|" then
      loop s rest (l :: chunk)
    else
      let s ← flush s
      loop s rest [l]
where
  freshSession (budgetMs : Nat) : IO Session := do
    let env ← importModules #[{ module := `Init }] {} 0 (loadExts := true)
    return { env, opts := {}, budgetMs }

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let budget := (args.find? (·.startsWith "--budget=")).bind (fun a => (a.drop 9).toString.toNat?) |>.getD 10000
  -- `loadExts` is required for the notation tokens of `Init` to be available to the parser
  let env ← importModules #[{ module := `Init }] {} 0 (loadExts := true)
  let opts : Options := {}
  let opts := opts.setBool `autoImplicit true
  let s : Session := { env, opts, budgetMs := budget }
  let input ← (← IO.getStdin).readToEnd
  let lines := (input.splitOn "\n").map (·.trimRight)
  loop s lines []
