import Leant2.Frontend.Command

/-! Real public queries must expose their own values, without changing any
definition elaborated against an older batch. Native aliases also preserve
local-variable binding, ordinary projections, and polymorphic elaboration. -/
open Lean Elab Command Term Meta Leant2

#leant2 value : Nat where value = 0
def savedNatResult : Nat := it1

#leant2 value : Bool where value = true
example : it1 = true := rfl
example : it = true := rfl
example : savedNatResult = 0 := rfl

/-- info: true -/
#guard_msgs in
#eval it1

/-- info: 42 -/
#guard_msgs in
#eval (fun it1 : Nat => it1 + 1) 41

/-- info: 4 -/
#guard_msgs in
#leant2_eval 2 + 2

/-- info: 40 -/
#guard_msgs in
#leant2_eval it * 10

example : it = 40 := rfl
example : it1 = true := rfl
example : it.succ = 41 := rfl

-- Exercise a shrinking batch deterministically, independently of search rank.
elab "#results_fixture " terms:term,* : command => do
  let candidates ← liftTermElabM <| terms.getElems.mapM fun term => do
    let value ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    match ← gate (← sessionProfile) value (← inferType value) none with
    | .ok candidate => pure candidate
    | .error _ => throwError "result fixture did not pass the gate"
  bindIts candidates

#results_fixture (3 : Nat), (7 : Nat)
example : it1 = 3 ∧ it2 = 7 := ⟨rfl, rfl⟩
def savedSecondResult : Nat := it2
#results_fixture (fun (A : Type) (a : A) => a)
example : it1 Nat 12 = 12 := rfl
example : savedSecondResult = 7 := rfl
run_cmd do
  if (resultBinding? (← getEnv) `it2).isSome then
    throwError "old second candidate survived a smaller batch"
  unless (getAliases (← getEnv) `it2 false).isEmpty do
    throwError "old second alias survived a smaller batch"
  if (← liftCoreM sessionConstants).any isResultName then
    throwError "generated result leaked into provider inventory"

namespace NestedResultScope
#results_fixture (some 5 : Option Nat)
example : it1 = some 5 := rfl
example : _root_.it1 = some 5 := rfl
example : _root_.NestedResultScope.it1 = some 5 := rfl
example : it1.isSome = true := rfl
end NestedResultScope
example : it1 = some 5 := rfl

-- A well-formed unsuccessful query clears numbered candidates, while `it`
-- remains the most recent successful value. Invalid syntax/preflight does
-- not silently turn an earlier candidate into the current query's result.
#leant2 value : Nat where False
run_cmd do
  if (resultBinding? (← getEnv) `it1).isSome then
    throwError "failed query retained a numbered candidate"
example : it = some 5 := rfl

-- Environment rollback restores both active aliases and immutable values.
run_cmd do
  let saved ← get
  let previous := resultBinding? saved.env `it
  try
    elabCommand (← `(command| #results_fixture (true : Bool)))
    if resultBinding? (← getEnv) `it == previous then
      throwError "publication did not allocate an immutable declaration"
  finally
    set saved
  unless resultBinding? (← getEnv) `it == previous do
    throwError "rollback lost the old result binding"

-- A known result-name collision must be rejected before an IO action runs.
-- Use an imported process-local reference, restoring it even if this test fails.
run_cmd do
  let saved ← get
  let timers ← profTimers.get
  try
    elabCommand (← `(command| def $(mkIdent `it) : Nat := 17))
    let previous := resultBinding? (← getEnv) `it
    let before := (← getEnv).constants.map₂.toList.length
    profTimers.set #[("results-preflight", 0)]
    let mut rejected := false
    try
      elabLeant2Eval (← `(command| #leant2_eval
        (Leant2.profTimers.set #[("results-effect", 1)] : IO Unit)))
    catch ex =>
      if ex.isInterrupt || ex.isRuntime then throw ex
      rejected := true
    unless rejected do throwError "evaluation accepted a user-name collision"
    unless (← profTimers.get) == #[("results-preflight", 0)] do
      throwError "evaluation performed IO before rejecting a result-name collision"
    unless resultBinding? (← getEnv) `it == previous do
      throwError "evaluation collision changed the previous result binding"
    unless (← getEnv).constants.map₂.toList.length == before do
      throwError "evaluation collision leaked a generated declaration"
  finally
    profTimers.set timers
    set saved

-- A runtime evaluation failure restores aliases provisionally installed for
-- collision preflight, along with the newly published kernel declaration.
run_cmd do
  let saved ← get
  try
    let previous := resultBinding? saved.env `it
    let aliases := getAliases saved.env `it false
    let before := saved.env.constants.map₂.toList.length
    set { saved with messages := {} }
    elabCommand (← `(command| #leant2_eval
      (throw (IO.userError "results-runtime-failure") : IO Unit)))
    let mut expectedError := false
    for message in (← get).messages.toList do
      if message.severity == .error then
        let text ← message.toString
        if (text.splitOn "results-runtime-failure").length > 1 then
          expectedError := true
    unless expectedError do throwError "evaluation did not report the expected runtime failure"
    unless resultBinding? (← getEnv) `it == previous &&
        getAliases (← getEnv) `it false == aliases do
      throwError "failed evaluation retained its provisional result alias"
    unless (← getEnv).constants.map₂.toList.length == before do
      throwError "failed evaluation leaked a generated declaration"
  finally
    set saved

-- User constants are not replaced to force a result name to resolve.
run_cmd do
  let saved ← get
  try
    elabCommand (← `(command| def $(mkIdent `it1) : String := "user value"))
    let original ← liftCoreM <| getConstInfo `it1
    let candidate ← liftTermElabM do
      let value := mkNatLit 13
      match ← gate (← sessionProfile) value (Lean.mkConst ``Nat) none with
      | .ok candidate => pure candidate
      | .error _ => throwError "collision fixture failed the gate"
    let mut rejected := false
    try
      bindIts #[candidate]
    catch _ => rejected := true
    unless rejected do throwError "result publication overwrote a user name"
    unless (← liftCoreM <| getConstInfo `it1).value? == original.value? do
      throwError "result publication mutated a user declaration"
  finally
    set saved
