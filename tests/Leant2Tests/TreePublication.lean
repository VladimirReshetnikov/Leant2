import Leant2.Frontend.Command

/-!
This unit test starts from a native binary-tree recursor certified by the
strict gate. It isolates publication and independent printed-text replay from
search scheduling. It does not claim that search found the supplied term.
-/

open Lean Meta Elab Term Command Leant2

namespace TreePublication

inductive Tree (A : Type) where
  | leaf : Tree A
  | node : Tree A → A → Tree A → Tree A

end TreePublication

elab "#tree_publish " n:ident " := " value:term : command => do
  let accepted ← liftTermElabM <| withoutErrToSorry do
    let value ← elabTerm value none
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    let type ← instantiateMVars (← inferType value)
    unless (value.find? fun e => e.isConstOf ``TreePublication.Tree.rec).isSome do
      throwError "tree publication fixture did not retain the native recursive term"
    match ← gate .strictConstructive value type none with
    | .ok accepted =>
      unless accepted.axioms.isEmpty do throwError "native tree term introduced an axiom"
      return accepted
    | .error _ => throwError "native tree term failed strict kernel acceptance"
  unless ← Presentation.publish n.getId accepted do
    throwError "accepted native tree recursor did not compile"
  let ci ← liftCoreM <| getConstInfo n.getId
  unless ci.value! == accepted.program && ci.type == accepted.programType do
    throwError "tree publication changed the exact certified value or type"
  if isNoncomputable (← getEnv) n.getId then
    throwError "native tree publication was marked noncomputable"
  let providers ← liftCoreM sessionConstants
  if providers.any Presentation.isAuxiliaryName then
    throwError "tree compiler auxiliaries leaked into session providers"

#tree_publish TreePublication.accepted := fun tree : TreePublication.Tree Nat =>
  TreePublication.Tree.rec (motive := fun _ => List Nat) []
    (fun _left label _right fromLeft fromRight => List.append fromLeft (label :: fromRight)) tree

-- Arbitrary-constructor equations for the exact accepted expression, not just
-- the finite sample trees used below. These must remain kernel-definitional.
example : TreePublication.accepted .leaf = [] := rfl

example (left right : TreePublication.Tree Nat) (label : Nat) :
    TreePublication.accepted (.node left label right) =
      TreePublication.accepted left ++ (label :: TreePublication.accepted right) := rfl

/-- info: ([], [0], [8, 5, 3, 13]) -/
#guard_msgs in
#eval (TreePublication.accepted .leaf,
  TreePublication.accepted (.node .leaf 0 .leaf),
  TreePublication.accepted
    (.node (.node .leaf 8 (.node .leaf 5 .leaf)) 3 (.node .leaf 13 .leaf)))

-- Print text, discard the original syntax metadata, parse the text, and compile
-- a new declaration. This is independent source replay rather than reusing a
-- previously elaborated Expr or the compiler adapter's implementation constant.
run_cmd do
  let displayName := `TreePublication.printed
  let cmd ← liftTermElabM do
    let ci ← getConstInfo ``TreePublication.accepted
    let stx ← Presentation.programSyntax ci.value!
    let text := (← PrettyPrinter.ppTerm stx).pretty
    unless (text.splitOn "match").length > 1 && (text.splitOn ".rec").length == 1 do
      throwError "tree printed source did not replace the recursor with executable matches: {text}"
    let parsed ← match Parser.runParserCategory (← getEnv) `term text with
      | .ok stx => pure (⟨stx⟩ : TSyntax `term)
      | .error error => throwError "printed tree source is invalid: {error}"
    let type ← PrettyPrinter.delab ci.type
    `(command| def $(mkIdent displayName) : $type := $parsed)
  elabCommand cmd
  let ci ← liftCoreM <| getConstInfo displayName
  if ci.value!.hasMVar || ci.value!.hasSorry ||
      isNoncomputable (← getEnv) displayName then
    throwError "reparsed tree source did not elaborate and compile completely"
  liftTermElabM do
    match ← gate .strictConstructive ci.value! ci.type none with
    | .ok accepted =>
      unless accepted.axioms.isEmpty do throwError "reparsed tree source introduced an axiom"
    | .error _ => throwError "reparsed tree source failed independent strict kernel acceptance"

-- Discover generated let-rec auxiliaries from the parsed declaration rather
-- than depending on the presentation's fresh loop counter. Separate universal
-- leaf/node equations and whole-tree equality protect both recursive children.
run_cmd do
  let names ← liftCoreM do
    let ci ← getConstInfo ``TreePublication.printed
    return #[``TreePublication.printed, ``TreePublication.accepted] ++
      ci.value!.getUsedConstants.filter (``TreePublication.printed).isPrefixOf
  let unfoldTerms ← names.mapM fun name => `(Parser.Tactic.simpLemma| $(mkIdent name):term)
  elabCommand (← `(example : TreePublication.printed .leaf = [] := by
    simp [$unfoldTerms,*]))
  elabCommand (← `(example (left right : TreePublication.Tree Nat) (label : Nat) :
      TreePublication.printed (.node left label right) =
        TreePublication.printed left ++ (label :: TreePublication.printed right) := by
    simp [$unfoldTerms,*]))
  elabCommand (← `(example : ∀ tree : TreePublication.Tree Nat,
      TreePublication.printed tree = TreePublication.accepted tree := by
    intro tree
    induction tree with
    | leaf => simp [$unfoldTerms,*]
    | node left label right fromLeft fromRight => simp_all [$unfoldTerms,*]))

/-- info: ([], [0], [8, 5, 3, 13]) -/
#guard_msgs in
#eval (TreePublication.printed .leaf,
  TreePublication.printed (.node .leaf 0 .leaf),
  TreePublication.printed
    (.node (.node .leaf 8 (.node .leaf 5 .leaf)) 3 (.node .leaf 13 .leaf)))
