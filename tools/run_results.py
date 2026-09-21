#!/usr/bin/env python3
"""Check result aliases through independent REPL sessions and retain raw evidence.

This suite is separate from the six provider-identity sessions. Kernel examples,
executable markers, query boundaries, inventories, and narrowly expected errors
must all agree; a printed candidate or a zero process exit alone never passes.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

import repl_protocol
from run_extended import runtime_env

ROOT = Path(__file__).resolve().parents[1]
TYPE_ERROR = r"(?im)^\s*error(?:\([^)]*\))?:\s*(?:Application type mismatch|Type mismatch)"


def block(source: str) -> str:
    return ":{\n" + source.strip() + "\n:}\n"


def marker(name: str) -> str:
    return f'#eval ("RESULTS_{name}_OK" : String)'


FIXTURE = r"""
open Lean Elab Command Term Meta Leant2
elab "#results_fixture " terms:term,* : command => do
  let candidates ← liftTermElabM <| terms.getElems.mapM fun term => do
    let value ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    match ← gate (← sessionProfile) value (← inferType value) none with
    | .ok candidate => pure candidate
    | .error _ => throwError "result fixture failed the gate"
  bindIts candidates
"""


@dataclass
class Case:
    name: str
    source: str
    queries: list[str] = field(default_factory=list)
    markers: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    inventories: list[list[str]] | None = None


def cases() -> list[Case]:
    return [
        Case("bare-eval", "2 + 2\nit * 10\n" + block("""
example : it = 40 := rfl
example : (it : Nat).succ = 41 := rfl
""" + marker("bare_eval")) + ":providers\n", markers=["bare_eval"], inventories=[[]]),
        Case("type-refresh", ":synth value : Nat where value = 0\n" +
             "def savedNat : Nat := it1\n:synth value : Bool where value = true\n" + block("""
example : it1 = true := rfl
example : it = true := rfl
example : savedNat = 0 := rfl
""" + marker("type_refresh")) + ":providers\n", queries=["candidate", "candidate"],
             markers=["type_refresh"], inventories=[["savedNat"]]),
        Case("batch-shrink", block(FIXTURE + r"""
#results_fixture (3 : Nat), (7 : Nat)
example : it1 = 3 ∧ it2 = 7 := ⟨rfl, rfl⟩
def savedSecond : Nat := it2
#results_fixture (fun (A : Type) (a : A) => a)
example : it1 Nat 12 = 12 := rfl
example : savedSecond = 7 := rfl
run_cmd do
  if (resultBinding? (← getEnv) `it2).isSome then
    throwError "stale numbered result"
  unless (getAliases (← getEnv) `it2 false).isEmpty do
    throwError "stale numbered alias"
  if (← liftCoreM sessionConstants).any isResultName then
    throwError "generated result leaked into providers"
""" + marker("batch_shrink")), markers=["batch_shrink"]),
        Case("query-failure", ":synth value : Nat where value = 0\n"
             ":synth value : Nat where False\n" + block(r"""
open Lean Elab Command Leant2
run_cmd do
  if (resultBinding? (← getEnv) `it1).isSome then
    throwError "failed query retained a candidate"
  unless (getAliases (← getEnv) `it1 false).isEmpty do
    throwError "failed query retained a candidate alias"
example : it = 0 := rfl
""" + marker("query_failure")), queries=["candidate", "false"], markers=["query_failure"]),
        Case("preflight-failure", ":synth value : Bool where value = true\n" +
             block("""
#leant2 value : Nat where value true = 0
example : it1 = true := rfl
example : it = true := rfl
""" + marker("preflight_failure")), queries=["candidate"],
             markers=["preflight_failure"], errors=[r"(?im)^\s*error(?:\([^)]*\))?:\s*Function expected"]),
        Case("eval-failure", "17\n" + block("""
#leant2_eval (true : Nat)
example : it = 17 := rfl
""" + marker("eval_failure")), markers=["eval_failure"], errors=[TYPE_ERROR]),
        Case("prior-error", block("""
#check (true : Nat)
#leant2_eval 7
example : it = 7 := rfl
""" + marker("prior_error")), markers=["prior_error"], errors=[TYPE_ERROR]),
        Case("undo-reset", "11\ndef savedBeforeUndo : Nat := it\nit + 1\n:undo\n" + block("""
example : it = 11 := rfl
example : savedBeforeUndo = 11 := rfl
""" + marker("undo")) + ":reset\n" + block(r"""
open Lean Elab Command Leant2
run_cmd do
  if (resultBinding? (← getEnv) `it).isSome || (resultBinding? (← getEnv) `it1).isSome then
    throwError "reset retained result aliases"
  if (← getEnv).contains `savedBeforeUndo then
    throwError "reset retained a user declaration"
""" + marker("reset")) + ":providers\n", markers=["undo", "reset"], inventories=[[]]),
        Case("namespace-hygiene", "namespace ResultScope\n"
             ":synth value : Nat where value = 0\n" + block("""
example : ResultScope.it1 = 0 := rfl
example : _root_.it1 = 0 := rfl
example : (fun it1 : Nat => it1 + 1) 41 = 42 := rfl
example : it1.succ = 1 := rfl
-- it1 and ResultScope.it1 inside comments are inert.
/- it1 := false; :synth not_a_command -/
#eval if ("it it1 ResultScope.it1" : String).length == 22 then "RESULTS_string_OK" else "RESULTS_string_FALSE"
""" + marker("namespace")) + "end ResultScope\n"
             ":synth value : Bool where value = true\n" + block(r"""
open Lean Elab Command Leant2
example : it1 = true := rfl
run_cmd do
  unless (getAliases (← getEnv) `ResultScope.it1 false).isEmpty do
    throwError "old namespace alias survived refresh"
""" + marker("namespace_refresh")), queries=["candidate", "candidate"],
             markers=["string", "namespace", "namespace_refresh"]),
        Case("user-collision", block(r"""
open Lean Elab Command Term Meta Leant2
def it1 : String := "user value"
run_cmd do
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
  unless rejected do throwError "publication did not reject the user-name collision"
  unless (← liftCoreM <| getConstInfo `it1).value? == original.value? do
    throwError "publication mutated the user declaration"
  if (resultBinding? (← getEnv) `it1).isSome then
    throwError "failed publication installed aliases"
example : it1 = "user value" := rfl
""" + marker("collision")), markers=["collision"]),
    ]


def check(case: Case, session: repl_protocol.SessionResult) -> list[str]:
    problems = list(session.problems)
    if len(session.queries) != len(case.queries):
        problems.append(f"expected {len(case.queries)} scored queries, got {len(session.queries)}")
    for index, expectation in enumerate(case.queries):
        if not repl_protocol.passes(session.query(index), expectation):
            problems.append(f"query {index + 1} did not satisfy {expectation}")
    expected_markers = [f'"RESULTS_{name}_OK"' for name in case.markers]
    actual_markers = re.findall(r'(?m)^"RESULTS_[A-Za-z_]+_(?:OK|FALSE)"$', session.stdout)
    if actual_markers != expected_markers:
        problems.append(f"executable markers differ: {actual_markers}")
    for pattern in case.errors:
        if len(re.findall(pattern, session.stdout)) != 1:
            problems.append(f"expected diagnostic did not match exactly once: {pattern}")
    inventories = [sorted(re.findall(r"`?([A-Za-z_][\w.]*)`?", match))
                   for match in re.findall(r"providers: \[([^\]]*)\]", session.stdout)]
    if case.inventories is not None and inventories != [sorted(x) for x in case.inventories]:
        problems.append(f"provider inventories differ: {inventories}")
    if any(name.startswith("_leant2_result.") for inventory in inventories for name in inventory):
        problems.append("generated result leaked into provider inventory")
    return problems


def main() -> int:
    import os
    import sys
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, default=ROOT / ".lake/build/bin/leant2.exe")
    parser.add_argument("--budget", type=int, default=10000)
    parser.add_argument("--out", type=Path, default=ROOT / "baseline-out/results")
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    selected = cases()
    if args.case:
        unknown = set(args.case) - {case.name for case in selected}
        if unknown:
            parser.error("unknown cases: " + ", ".join(sorted(unknown)))
        selected = [case for case in selected if case.name in args.case]
    if args.list:
        for case in selected:
            print(case.name)
        return 0
    if args.budget <= 0 or not args.exe.is_file():
        parser.error("a positive budget and existing executable are required")
    exe = args.exe.resolve()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    os.environ.update(runtime_env())
    executable_hash = hashlib.sha256(exe.read_bytes()).hexdigest()
    rows = []
    for case in selected:
        source = case.source + ":quit\n"
        start = time.monotonic()
        session = repl_protocol.run(str(exe), args.budget, source, out / f"{case.name}.out",
                                    allowed_outside_errors=len(case.errors))
        problems = check(case, session)
        rows.append({"id": case.name, "passed": not problems, "problems": problems,
                     "wall_elapsed_ms": round((time.monotonic() - start) * 1000),
                     "queries": [asdict(query) for query in session.queries],
                     "expected_diagnostics": len(case.errors), "transcript": source,
                     "stdout": session.stdout, "stderr": session.stderr})
        print(f"{'PASS' if not problems else 'FAIL'} {case.name}", flush=True)
        for problem in problems:
            print(f"  {problem}", flush=True)
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True)
    dirty = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT, capture_output=True, text=True)
    changed = hashlib.sha256(exe.read_bytes()).hexdigest() != executable_hash
    failures = [row["id"] for row in rows if not row["passed"]]
    if changed:
        failures.append("executable_changed_during_run")
    receipt = {"schema_version": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
               "revision": revision.stdout.strip(), "working_tree_dirty": bool(dirty.stdout.strip()),
               "executable": str(exe), "executable_sha256": executable_hash,
               "executable_changed_during_run": changed, "budget_ms": args.budget,
               "harness_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "passed": sum(row["passed"] for row in rows), "total": len(rows),
               "failures": failures, "success": not failures, "results": rows}
    receipt_path = out / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"TOTAL {receipt['passed']}/{receipt['total']}")
    print(f"RECEIPT {receipt_path}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
