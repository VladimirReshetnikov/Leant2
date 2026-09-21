import Lean
import Leant2
/-!
# `leant2`: the compatibility REPL (unified proposal, Section 14.2)

Reads a Leant-style transcript from standard input and drives everything
through Lean's command frontend with one persistent command state, so that
namespaces, `open`, and session declarations behave as in a file:

* declarations and `#eval`/`#check` chunks are elaborated as commands;
* `:synth ARGS` becomes the `#leant2 ARGS` command, whose output is printed;
* every `:set` line is accepted and ignored (Decision 1.1);
* `:reset` restores the initial environment; `:undo` drops the last chunk;
  `:{` ... `:}` delimit a multi-line block; `:providers` lists the session
  declarations that act as providers; `:quit` exits;
* `:prove T` enters a minimal prove mode in which a bare `:synth`
  synthesizes `T` and tactic lines are ignored;
* other non-command lines are evaluated as terms.
-/

open Lean Elab Meta Leant2

structure Session where
  base : Command.State
  st : Command.State
  budgetMs : Nat
  /-- Machine boundary for the category-only baseline harness. -/
  queryMarkers : Bool := false
  proving : Option String := none
  /-- Command states before each accepted chunk, for `:undo`. -/
  history : List Command.State := []

def leanKeywords : List String :=
  ["def", "theorem", "lemma", "inductive", "structure", "class", "instance", "axiom", "opaque",
   "abbrev", "universe", "namespace", "end", "open", "set_option", "#eval", "#check", "#print",
   "#reduce", "#leant2", "example", "variable", "section", "noncomputable", "private", "protected",
   "deriving", "attribute", "mutual", "@[", "/-", "--", "unsafe", "partial", "macro", "syntax",
   "elab", "notation", "infix", "prefix", "postfix"]

def startsWithKeyword (s : String) : Bool :=
  let t := s.trimLeft
  leanKeywords.any fun k => t.startsWith k && (t.length == k.length || !(t.get ⟨k.length⟩).isAlphanum)

/-- Elaborate a chunk of Lean commands in the session, printing messages. The
`#leant2` header line "N candidate(s) [...]" is dropped from the printout. -/
def elabChunk (s : Session) (src : String) (record : Bool := true) : IO Session := do
  let inputCtx := Parser.mkInputContext src "<repl>"
  let st0 := { s.st with messages := {} }
  let st ← IO.processCommands inputCtx {} st0
  for msg in st.commandState.messages.toList do
    let str ← msg.toString
    for l in str.splitOn "\n" do
      let l := l.trimRight
      if l.isEmpty then continue
      -- strip the position prefix of REPL messages
      let l := if l.startsWith "<repl>:" then
          ((l.splitOn ": ").drop 1 |> ": ".intercalate) else l
      if l.startsWith "info: " then
        let body := l.drop 6 |>.toString
        if body.startsWith "leant2: " || body.contains '[' then IO.println s!"-- {body}"
        else IO.println body
      else IO.println l
  -- only user chunks (declarations) enter the `:undo` history; queries do not
  return { s with st := st.commandState, history := if record then s.st :: s.history else s.history }

/-- Translate `:synth ARGS` into a `#leant2` command. -/
def synthCommand (arg : String) : String :=
  let arg := arg.trim
  match arg.splitOn " where " with
  | [_] => s!"#leant2 {arg}"
  | ty :: rest =>
    let wh := " where ".intercalate rest
    let parts := ty.splitOn " : "
    match parts with
    | n :: tyParts =>
      if tyParts.length ≥ 1 && n.trim.all (fun c => c.isAlphanum || c == '_' || c == '\'') then
        s!"#leant2 {n.trim} : {" : ".intercalate tyParts} where {wh}"
      else s!"#leant2 {ty} where {wh}"
    | _ => s!"#leant2 {ty} where {wh}"
  | _ => s!"#leant2 {arg}"

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
    if t == ":{" then
      -- a block: everything up to `:}` is one chunk of Lean commands
      let s ← flush s
      let body := rest.takeWhile (· != ":}")
      let rest := (rest.dropWhile (· != ":}")).drop 1
      IO.println "λ> :{"
      let s ← elabChunk s ("
".intercalate body)
      IO.println "λ> :}"
      loop s rest []
    else if t.startsWith ":" then
      let s ← flush s
      IO.println s!"λ> {t}"
      let body : String := (t.drop 1).toString
      let cmd : String := (body.takeWhile (· != ' ')).toString
      let arg : String := ((body.dropWhile (· != ' ')).toString).trim
      match cmd with
      | "quit" => pure ()
      | "set" => loop s rest []
      | "reset" =>
        IO.println "session reset"
        loop { s with st := s.base, proving := none, history := [] } rest []
      | "undo" =>
        match s.history with
        | prev :: hist =>
          IO.println "undone"
          loop { s with st := prev, history := hist } rest []
        | [] =>
          IO.println "nothing to undo"
          loop s rest []
      | "providers" =>
        let s ← elabChunk s "#leant2_providers" (record := false)
        loop s rest []
      | "prove" =>
        IO.println "entering prove mode (leant2: tactic lines are ignored)"
        loop { s with proving := some arg } rest []
      | "qed" | "abort" => loop { s with proving := none } rest []
      | "synth" =>
        let arg := if arg.isEmpty then s.proving.getD "" else arg
        let s ← elabChunk s (synthCommand arg) (record := false)
        if s.queryMarkers then IO.println "-- leant2-query-end"
        loop s rest []
      | "type" =>
        let s ← elabChunk s s!"#check ({arg})" (record := false)
        loop s rest []
      | _ => IO.println s!"(ignored :{cmd})"; loop s rest []
    else if t.isEmpty then
      let s ← flush s
      loop s rest []
    else if s.proving.isSome then
      loop s rest []
    else if (l.get 0).isWhitespace || l.startsWith "|" then
      loop s rest (l :: chunk)
    else
      let s ← flush s
      loop s rest [l]

unsafe def main (args : List String) : IO Unit := do
  -- the Leant2 library lives next to the executable: <root>/.lake/build/lib/lean
  let exe ← IO.appPath
  let libDir := exe.parent.bind (·.parent) |>.map (· / "lib" / "lean")
  let sp : SearchPath := match libDir with | some d => [d] | none => []
  initSearchPath (← findSysroot) sp
  enableInitializersExecution
  let budget := (args.find? (·.startsWith "--budget=")).bind (fun a => (a.drop 9).toString.toNat?) |>.getD 10000
  -- `loadExts` is required for the notation tokens of `Init` and the `#leant2` command
  let env ← importModules #[{ module := `Init }, { module := `Leant2 }] {} 0 (loadExts := true)
  let opts : Options := {}
  let opts := opts.setBool `autoImplicit true
  let opts := opts.set `leant2.budgetMs budget
  let base := Command.mkState env {} opts
  let s : Session := {
    base, st := base, budgetMs := budget
    queryMarkers := args.contains "--query-markers" }
  let input ← (← IO.getStdin).readToEnd
  let lines := (input.splitOn "\n").map (·.trimRight)
  loop s lines []
