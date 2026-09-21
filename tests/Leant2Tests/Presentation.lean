import Leant2.Frontend.Command

/-! Executable presentations preserve the accepted kernel term. These tests
cover primitive recursion, user-defined types, polymorphism, nesting, and
noncomputable provider fallback independently of search heuristics. -/

open Lean Elab Command Term Meta Leant2

universe u

-- Fully end-to-end, before any test definitions can become providers.
set_option leant2.budgetMs 20000 in
#leant2 f : List Nat → Nat where f [] = 0 ∧ f [1, 2, 3] = 6 ∧ f [4, 5] = 9

/-- info: 6 -/
#guard_msgs in
#eval it1 [1, 2, 3]

elab "#publish_computable " n:ident " := " t:term : command => do
  let accepted ← liftTermElabM do
    let p ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let p ← instantiateMVars p
    match ← gate (← sessionProfile) p (← inferType p) none with
    | .ok c => return c
    | .error _ => throwError "presentation test: candidate was not accepted"
  unless ← Presentation.publish n.getId accepted do
    throwError "presentation test: expected a computable result"
  let value := (← getEnv).find? n.getId |>.bind (·.value?)
  unless value == some accepted.program do
    throwError "presentation test: publishing changed the certified kernel value"
  let providers ← liftCoreM sessionConstants
  if providers.any Presentation.isAuxiliaryName then
    throwError "presentation test: compiler auxiliaries leaked into providers"

#publish_computable presentationSum :=
  fun xs : List Nat => List.rec (motive := fun _ => Nat) 0 (fun head _ ih => head + ih) xs

/-- info: 6 -/
#guard_msgs in
#eval presentationSum [1, 2, 3]

example : presentationSum [1, 2, 3] = 6 := rfl
example : presentationSum [1, 2, 3] = 6 := by simp [presentationSum]

inductive PresentationTree where
  | leaf
  | node : PresentationTree → PresentationTree → PresentationTree

#publish_computable presentationLeaves := fun t : PresentationTree =>
  PresentationTree.rec (motive := fun _ => Nat) 1 (fun _ _ left right => left + right) t

/-- info: 3 -/
#guard_msgs in
#eval presentationLeaves (.node (.node .leaf .leaf) .leaf)

#publish_computable presentationMap := fun (α β : Type) (f : α → β) (xs : List α) =>
  List.rec (motive := fun _ => List β) [] (fun a _ ih => f a :: ih) xs

/-- info: [2, 3, 4] -/
#guard_msgs in
#eval presentationMap Nat Nat (· + 1) [1, 2, 3]

#publish_computable presentationNested := fun xs : List Nat =>
  (List.rec (motive := fun _ => Nat) 0 (fun a _ ih => a + ih) xs,
   Nat.rec (motive := fun _ => Nat) 1 (fun _ ih => ih + 1) 4)

/-- info: (6, 5) -/
#guard_msgs in
#eval presentationNested [1, 2, 3]

-- Constructor binders must not capture an outer variable with the same name.
#publish_computable presentationCaptured := fun (field0 : Nat) (xs : List Nat) =>
  List.rec (motive := fun _ => Nat) field0 (fun _ _ ih => field0 + ih) xs

-- The second recursor is inside a branch of the first, under addition.
#publish_computable presentationBranchRecursion := fun xs : List (List Nat) =>
  List.rec (motive := fun _ => Nat) 0
    (fun row _ outer =>
      List.rec (motive := fun _ => Nat) 0 (fun head _ inner => head + inner) row + outer) xs

/-- info: (12, 10) -/
#guard_msgs in
#eval (presentationCaptured 3 [1, 2, 3], presentationBranchRecursion [[1, 2], [3, 4]])

#publish_computable presentationId := fun (α : Sort u) (x : α) => x
example (α : Sort u) (x : α) : presentationId α x = x := rfl

/-- info: 12 -/
#guard_msgs in
#eval presentationId Nat 12

axiom presentationOpaque : Nat → Nat

run_cmd do
  let accepted ← liftTermElabM do
    let p := Lean.mkConst ``presentationOpaque
    match ← gate (← sessionProfile) p (← inferType p) none with
    | .ok c => return c
    | .error _ => throwError "presentation test: axiom provider was not accepted"
  if ← Presentation.publish `presentationNoncomputable accepted then
    throwError "presentation test: an axiom provider unexpectedly compiled"
  unless isNoncomputable (← getEnv) `presentationNoncomputable do
    throwError "presentation test: missing noncomputable metadata"

example : presentationNoncomputable = presentationOpaque := rfl

-- The printed source itself must be valid Lean, including nested matches.
run_cmd do
  for name in [``presentationSum, ``presentationLeaves, ``presentationMap, ``presentationNested,
      ``presentationCaptured, ``presentationBranchRecursion] do
    let displayName := name ++ `_leant2_compiled_display
    let cmd ← liftTermElabM do
      let ci ← getConstInfo name
      let stx ← Presentation.programSyntax ci.value!
      let text := (← PrettyPrinter.ppTerm stx).pretty
      unless (text.splitOn "match").length > 1 && (text.splitOn ".rec").length == 1 do
        throwError "presentation test: expected match syntax, got {text}"
      let stx ← match Parser.runParserCategory (← getEnv) `term text with
        | .ok stx => pure (⟨stx⟩ : TSyntax `term)
        | .error error => throwError "presentation test: printed source is not parseable: {error}"
      let ty ← PrettyPrinter.delab ci.type
      `(command| def $(mkIdent displayName) : $ty := $stx)
    elabCommand cmd
    let ci ← liftCoreM <| getConstInfo displayName
    if ci.value!.hasMVar || ci.value!.hasSorry then
      throwError "presentation test: displayed source for {name} did not elaborate completely"

/-- info: 6 -/
#guard_msgs in
#eval presentationSum._leant2_compiled_display [1, 2, 3]

/-- info: (6, 5) -/
#guard_msgs in
#eval presentationNested._leant2_compiled_display [1, 2, 3]

/-- info: (12, 10) -/
#guard_msgs in
#eval (presentationCaptured._leant2_compiled_display 3 [1, 2, 3],
  presentationBranchRecursion._leant2_compiled_display [[1, 2], [3, 4]])

example : presentationCaptured._leant2_compiled_display 3 [1, 2, 3] =
    presentationCaptured 3 [1, 2, 3] := rfl

example : presentationBranchRecursion._leant2_compiled_display [[1, 2], [3, 4]] =
    presentationBranchRecursion [[1, 2], [3, 4]] := rfl
