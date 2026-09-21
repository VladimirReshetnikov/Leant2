import Leant2.Frontend.Presentation

/-! Indexed publication is tested independently of search: every source term
passes the acceptance gate, its exact kernel expression is retained, and the
printed text is parsed and compiled again in a fresh definition. -/

open Lean Elab Command Term Meta Leant2

universe u v

namespace IndexedPresentation

inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons {n : Nat} : A → Vec A n → Vec A (n + 1)

def Vec.toList {A : Type u} {n : Nat} : Vec A n → List A
  | .nil => []
  | .cons a xs => a :: xs.toList

-- Two changing indices ensure publication does not assume one Nat index.
inductive Grid (A : Type u) : Nat → Nat → Type u where
  | origin : Grid A 0 0
  | step {n m : Nat} : A → Grid A n m → Grid A (n + 1) (m + 1)

def Grid.toList {A : Type u} {n m : Nat} : Grid A n m → List A
  | .origin => []
  | .step a rest => a :: rest.toList

mutual
  inductive EvenTree : Nat → Type where
    | zero : EvenTree 0
    | next {n} : OddTree n → EvenTree (n + 1)
  inductive OddTree : Nat → Type where
    | next {n} : EvenTree n → OddTree (n + 1)
end

-- Lean represents this declared single family using auxiliary nested recursors.
inductive NestedTree : Type where
  | leaf : NestedTree
  | node : List NestedTree → NestedTree

end IndexedPresentation

elab "#indexed_publish " n:ident " : " ty:term " := " t:term : command => do
  let accepted ← liftTermElabM <| withoutErrToSorry do
    let target ← elabType ty
    let p ← elabTerm t (some target)
    synthesizeSyntheticMVarsNoPostponing
    let p ← instantiateMVars p
    match ← gate .strictConstructive p target none with
    | .ok c => return c
    | .error _ => throwError "indexed presentation: candidate failed the gate"
  unless ← Presentation.publish n.getId accepted do
    throwError "indexed presentation: expected executable code"
  let ci ← liftCoreM <| getConstInfo n.getId
  unless ci.value! == accepted.program && ci.type == accepted.programType do
    throwError "indexed presentation: publication changed the certified term"

#indexed_publish indexedPresentationMap :
    (A : Type u) → (B : Type v) → (A → B) → (n : Nat) →
      IndexedPresentation.Vec A n → IndexedPresentation.Vec B n :=
  fun _A B f _n xs =>
    IndexedPresentation.Vec.rec (motive := fun n _ => IndexedPresentation.Vec B n)
      .nil (fun a _rest ih => .cons (f a) ih) xs

example (A : Type u) (B : Type v) (f : A → B) :
    indexedPresentationMap A B f 0 .nil = .nil := rfl

example (A : Type u) (B : Type v) (f : A → B) (n : Nat)
    (a : A) (xs : IndexedPresentation.Vec A n) :
    indexedPresentationMap A B f (n + 1) (.cons a xs) =
      .cons (f a) (indexedPresentationMap A B f n xs) := rfl

/-- info: [false, true] -/
#guard_msgs in
#eval (indexedPresentationMap Nat Bool (· == 3) 2 (.cons 1 (.cons 3 .nil))).toList

/-- info: [1, 0] -/
#guard_msgs in
#eval (indexedPresentationMap Bool Nat (fun b => if b then 1 else 0) 2
  (.cons true (.cons false .nil))).toList

/-- info: [] -/
#guard_msgs in
#eval (indexedPresentationMap Nat Bool (· == 3) 0 .nil).toList

-- A motive depending on both the index and the actual major premise.
#indexed_publish indexedPresentationCopy :
    (A : Type u) → (n : Nat) → (xs : IndexedPresentation.Vec A n) →
      {ys : IndexedPresentation.Vec A n // ys = xs} :=
  fun A _n xs => IndexedPresentation.Vec.rec
    (motive := fun n xs => {ys : IndexedPresentation.Vec A n // ys = xs})
    ⟨.nil, rfl⟩
    (fun a _rest ih => ⟨.cons a ih.val, congrArg (IndexedPresentation.Vec.cons a) ih.property⟩) xs

/-- info: [4, 7] -/
#guard_msgs in
#eval (indexedPresentationCopy Nat 2 (.cons 4 (.cons 7 .nil))).val.toList

example (A : Type u) (n : Nat) (xs : IndexedPresentation.Vec A n) :
    (indexedPresentationCopy A n xs).val = xs :=
  (indexedPresentationCopy A n xs).property

#indexed_publish indexedPresentationGridMap :
    (A : Type u) → (B : Type v) → (A → B) → (n m : Nat) →
      IndexedPresentation.Grid A n m → IndexedPresentation.Grid B n m :=
  fun _A B f _n _m xs => IndexedPresentation.Grid.rec
    (motive := fun n m _ => IndexedPresentation.Grid B n m)
    .origin (fun a _rest ih => .step (f a) ih) xs

/-- info: [5, 8] -/
#guard_msgs in
#eval (indexedPresentationGridMap Nat Nat Nat.succ 2 2 (.step 4 (.step 7 .origin))).toList

-- A conflicting outer name and two sibling indexed loops must survive printing.
#indexed_publish indexedPresentationPair :
    Nat → (n : Nat) → IndexedPresentation.Vec Nat n →
      IndexedPresentation.Vec Nat n × IndexedPresentation.Vec Nat n :=
  fun field0 _n xs =>
    (IndexedPresentation.Vec.rec (motive := fun n _ => IndexedPresentation.Vec Nat n)
      .nil (fun a _rest ih => .cons (a + field0) ih) xs,
     IndexedPresentation.Vec.rec (motive := fun n _ => IndexedPresentation.Vec Nat n)
      .nil (fun a _rest ih => .cons (a + 1) ih) xs)

-- Check the generic rewrite, including its transitive axiom inventory.
run_cmd liftTermElabM do
  for recName in [``IndexedPresentation.Vec.rec, ``IndexedPresentation.Grid.rec] do
    let some entry := (Compiler.CSimp.ext.getState (← getEnv)).map.find? recName
      | throwError "indexed presentation: missing checked compiler rewrite"
    let ci ← getConstInfo entry.thmName
    unless ci.type.isAppOfArity ``Eq 3 do
      throwError "indexed presentation: missing equality theorem"
    let axioms ← collectAxioms entry.thmName
    unless axioms.all Profile.standard.allowedAxioms.contains do
      throwError "indexed presentation: unsupported axiom in compiler equality"

-- Unsupported mutually recursive and nested recursors leave no partial adapter.
run_cmd do
  for recName in [``IndexedPresentation.EvenTree.rec, ``IndexedPresentation.NestedTree.rec] do
    let before := (← getEnv).constants.map₂.toList.length
    if ← Presentation.ensureRecursor recName then
      throwError "indexed presentation: unsupported recursor unexpectedly admitted"
    unless (← getEnv).constants.map₂.toList.length == before do
      throwError "indexed presentation: unsuccessful adapter leaked declarations"
    if (Compiler.CSimp.ext.getState (← getEnv)).map.contains recName then
      throwError "indexed presentation: unsupported recursor gained a rewrite"
    let accepted ← liftTermElabM do
      let ci ← getConstInfo recName
      let term := Lean.mkConst recName (ci.levelParams.map Level.param)
      match ← gate .strictConstructive term ci.type none with
      | .ok c => return c
      | .error _ => throwError "indexed presentation: unsupported recursor failed acceptance"
    let name := recName ++ `_leant2_compiled_fallback
    if ← Presentation.publish name accepted then
      throwError "indexed presentation: unsupported recursor unexpectedly compiled"
    let ci ← liftCoreM <| getConstInfo name
    unless ci.value! == accepted.program && ci.type == accepted.programType do
      throwError "indexed presentation: fallback changed the certified term"

-- Reparse actual text: retaining hidden Syntax metadata is not a source round trip.
run_cmd do
  for name in [``indexedPresentationMap, ``indexedPresentationCopy,
      ``indexedPresentationGridMap, ``indexedPresentationPair] do
    let displayName := name ++ `_leant2_compiled_display
    let cmd ← liftTermElabM do
      let ci ← getConstInfo name
      let stx ← Presentation.programSyntax ci.value!
      let text := (← PrettyPrinter.ppTerm stx).pretty
      unless (text.splitOn "match").length > 1 && (text.splitOn ".rec").length == 1 do
        throwError "indexed presentation: recursor remained in printed source: {text}"
      let stx ← match Parser.runParserCategory (← getEnv) `term text with
        | .ok stx => pure (⟨stx⟩ : TSyntax `term)
        | .error error => throwError "indexed presentation: printed source is invalid: {error}"
      let levels := ci.levelParams.toArray.map mkIdent
      let declId ← `(declId| $(mkIdent displayName).{$levels,*})
      let type ← PrettyPrinter.delab ci.type
      `(command| def $declId:declId : $type := $stx)
    withScope (fun s => { s with levelNames := [] }) <| elabCommand cmd
    let ci ← liftCoreM <| getConstInfo displayName
    if ci.value!.hasMVar || ci.value!.hasSorry || isNoncomputable (← getEnv) displayName then
      throwError "indexed presentation: printed source did not compile completely"

/-- info: [false, true] -/
#guard_msgs in
#eval (indexedPresentationMap._leant2_compiled_display Nat Bool (· == 3) 2
  (.cons 1 (.cons 3 .nil))).toList

/-- info: [4, 7] -/
#guard_msgs in
#eval (indexedPresentationCopy._leant2_compiled_display Nat 2 (.cons 4 (.cons 7 .nil))).val.toList

/-- info: [5, 8] -/
#guard_msgs in
#eval (indexedPresentationGridMap._leant2_compiled_display Nat Nat Nat.succ 2 2
  (.step 4 (.step 7 .origin))).toList

/-- info: ([11, 13], [2, 4]) -/
#guard_msgs in
#eval let p := indexedPresentationPair._leant2_compiled_display 10 2 (.cons 1 (.cons 3 .nil))
  (p.1.toList, p.2.toList)

example (A : Type u) (B : Type v) (f : A → B) (n : Nat)
    (xs : IndexedPresentation.Vec A n) :
    indexedPresentationMap._leant2_compiled_display A B f n xs =
      indexedPresentationMap A B f n xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [indexedPresentationMap._leant2_compiled_display,
      indexedPresentationMap] at ih ⊢
    exact congrArg (IndexedPresentation.Vec.cons (f a)) ih
