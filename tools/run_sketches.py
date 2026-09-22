#!/usr/bin/env python3
"""Fresh-process public sketch gates and independent emitted-source replay.

Every logical case requires all its subprocess stages. The separate reference
process is a prerequisite, not an additional scored case. This runner never
builds: it requires the public frontend modules to have been built beforehand.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/sketches"
sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location("sketch_shared_frontend", ROOT / "tools/run_frontends.py")
FRONT = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(FRONT)

SOURCE_PREFIX = "leant2 sketch source:\n"
PREP_PREFIX = "leant2 sketch: preparation failed:"
OUTCOME_PREFIX = "leant2 sketch: "
VALUE = '"SKETCH_VALUE_OK"'
ABSENT = "SKETCH_NO_RESULT_OK"
REJECTED = re.compile(r"[1-9]\d* program\(s\) of the type proposed, none passed the contract\Z")


def load_cases(folder=FIXTURES):
    payload = json.loads((folder / "cases.json").read_text(encoding="utf-8"))
    cases = payload["cases"]
    if (payload["schema_version"] != 1 or not isinstance(cases, list) or not cases or
            len({c["id"] for c in cases}) != len(cases)):
        raise ValueError("invalid sketch fixture inventory")
    for case in cases:
        if not re.fullmatch(r"[a-z][a-z0-9-]*", case["id"]):
            raise ValueError("invalid case identity")
        if case["expect"] not in ("candidate", "rejected", "contract_impossible", "preflight"):
            raise ValueError("invalid expected outcome")
        if case["replay"] != (case["expect"] == "candidate"):
            raise ValueError("every positive case must replay its emitted source")
        if case["replay"]:
            if Path(case["checks"]).name != case["checks"]:
                raise ValueError("checks must be a simple filename")
            (folder / case["checks"]).read_text(encoding="utf-8")
    return cases


def declaration_audit(case):
    return FRONT.audit_source({**case, "declarations": ["completed", "originalContract", "heldOut"]})


def absent_check():
    return f'''
open Lean Elab Command in
run_cmd do
  for name in [`it, `it1] do
    if (Leant2.resultBinding? (← getEnv) name).isSome ||
        !(getAliases (← getEnv) name false).isEmpty then
      throwError "sketch negative retained a result alias: {{name}}"
  logInfo "{ABSENT}"
'''


def source(case, budget, completed=None):
    """Use actual emitted term verbatim, changing only embedding indentation."""
    if completed is not None:
        header = "import Lean\nset_option linter.unusedVariables false\n"
        body = "  " + completed.replace("\n", "\n  ")
        text = header + f'def completed : {case["target"]} :=\n{body}\n'
        locations = []
    else:
        header = (f"import Leant2\nset_option leant2.budgetMs {budget}\n"
                  "set_option linter.unusedVariables false\n#leant2_providers\n")
        query = (f'#leant2_sketch f : {case["target"]} :=\n'
                 f'  {case["sketch"]}\nwhere\n  {case["contract"]}\n')
        start = len(header.splitlines()) + 1
        locations = list(range(start, start + len(query.splitlines())))
        text = header + query
        if case["expect"] == "candidate":
            text += f'def completed : {case["target"]} := it1\n'
        else:
            return text + absent_check(), locations
    return text + (FIXTURES / case["checks"]).read_text(encoding="utf-8") + declaration_audit(case), locations


def classify(case, stage, stdout, stderr, returncode, locations):
    parsed, problems = FRONT.messages(stdout)
    if stage not in ("original", "replay"):
        problems.append("unknown public process stage")
    errors = [m for m in parsed if m["severity"] == "error"]
    warnings = [m for m in parsed if m["severity"] == "warning"]
    infos = [m for m in parsed if m["severity"] == "information"]
    texts = [m["data"] for m in infos]
    emitted = [m for m in infos if m["data"].startswith(SOURCE_PREFIX)]
    prepared = [m for m in infos if re.fullmatch(r"leant2 sketch: prepared \d+ hole\(s\)", m["data"])]
    outcomes = [m for m in infos if m["data"].startswith(OUTCOME_PREFIX) and m not in prepared]
    completed = None
    preflight = stage == "original" and case["expect"] == "preflight"
    if stderr:
        problems.append("nonempty subprocess stderr")
    if returncode != (1 if preflight else 0):
        problems.append("incorrect native process exit")
    if warnings:
        problems.append("unexpected warning")
    if preflight:
        if len(errors) != 1 or not errors[0]["data"].startswith(PREP_PREFIX) or errors[0]["pos"].get("line") not in locations:
            problems.append("missing or unrelated preparation error")
        if emitted or prepared or outcomes:
            problems.append("malformed input advertised a search/preparation success")
    elif errors:
        problems.append("unexpected error")
    if stage == "replay":
        if emitted or prepared or outcomes:
            problems.append("replay unexpectedly invokes sketch synthesis")
    else:
        if texts.count("providers: []") != 1:
            problems.append("fresh public process unexpectedly has session providers")
        if not preflight:
            expected = f'leant2 sketch: prepared {case["holes"]} hole(s)'
            if len(prepared) != 1 or prepared[0]["data"] != expected or prepared[0]["pos"].get("line") not in locations:
                problems.append("wrong owned-hole preparation record")
            if len(outcomes) != 1 or outcomes[0]["pos"].get("line") not in locations:
                problems.append("missing or duplicate sketch outcome")
            else:
                outcome = outcomes[0]["data"][len(OUTCOME_PREFIX):]
                if case["expect"] == "candidate":
                    if not re.match(r"[1-9]\d* candidate\(s\)\s", outcome):
                        problems.append("positive case did not report accepted candidates")
                elif case["expect"] == "contract_impossible":
                    if outcome != "provably no program satisfies the contract":
                        problems.append("False control requires a certified contract-negative outcome")
                elif not REJECTED.fullmatch(outcome):
                    problems.append("wrong supplied body needs a positive rejected-program count, not exhaustion or impossibility")
        if case["expect"] == "candidate":
            if len(emitted) != 1 or emitted[0]["pos"].get("line") not in locations:
                problems.append("missing or duplicate actual completed-source diagnostic")
            else:
                completed = emitted[0]["data"][len(SOURCE_PREFIX):]
                if not completed.strip() or FRONT.FORBIDDEN.search(completed) or "?" in completed:
                    problems.append("completed source is empty, unresolved, or depends on synthesis helpers")
        elif emitted:
            problems.append("negative case advertised completed source")
    if case["expect"] == "candidate":
        if texts.count(FRONT.audit_marker(case)) != 1 or texts.count(VALUE) != 1:
            problems.append("missing independent declaration/execution check")
    elif texts.count(ABSENT) != 1:
        problems.append("negative case did not verify absence of a published alias")
    return {"passed": not problems, "problems": problems, "completed_source": completed,
            "diagnostics": {"errors": len(errors), "warnings": len(warnings), "information": len(infos)}}


def process(text, stage, folder, lean, environment, timeout):
    path = folder / f"{stage}.lean"
    path.write_text(text, encoding="utf-8", newline="\n")
    command = [str(lean), "--json", str(path)]
    start = time.monotonic()
    timeout_hit = False
    try:
        result = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, timeout=timeout, check=False)
        stdout, stderr, exitcode = result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired as ex:
        stdout, stderr, exitcode = ex.stdout or b"", ex.stderr or b"", None
        timeout_hit = True
    except OSError as ex:
        stdout, stderr, exitcode = b"", str(ex).encode("utf-8"), None
    (folder / f"{stage}.stdout.jsonl").write_bytes(stdout)
    (folder / f"{stage}.stderr").write_bytes(stderr)
    invalid_utf8 = False
    try:
        outtext, errtext = stdout.decode("utf-8"), stderr.decode("utf-8")
    except UnicodeError:
        invalid_utf8 = True
        outtext, errtext = stdout.decode("utf-8", errors="replace"), stderr.decode("utf-8", errors="replace")
    return {"stage": stage, "command": command, "source_sha256": FRONT.sha(path),
            "stdout": outtext, "stderr": errtext, "returncode": exitcode,
            "elapsed_ms": round((time.monotonic() - start) * 1000),
            "timed_out": timeout_hit, "invalid_utf8": invalid_utf8}


def run_stage(case, stage, text, locations, folder, lean, environment, timeout):
    raw = process(text, stage, folder, lean, environment, timeout)
    audit = classify(case, stage, raw["stdout"], raw["stderr"], raw["returncode"], locations)
    for key in ("timed_out", "invalid_utf8"):
        if raw[key]:
            audit["passed"] = False
            audit["problems"].append(key)
    return {**raw, **audit}


def case_passed(case, stages):
    expected = ["original"] + (["replay"] if case["replay"] else [])
    return ([stage["stage"] for stage in stages] == expected and
            all(stage["passed"] and not stage["timed_out"] and not stage["invalid_utf8"]
                for stage in stages))


def classify_reference(stage):
    messages, problems = FRONT.messages(stage["stdout"])
    if stage["stderr"] or stage["returncode"] != 0:
        problems.append("reference process failed or wrote stderr")
    if stage["timed_out"] or stage["invalid_utf8"]:
        problems.append("reference process timed out or emitted invalid UTF-8")
    if any(message["severity"] != "information" for message in messages):
        problems.append("reference process reported an error or warning")
    if sum(message["data"] == '"SKETCH_REFERENCES_OK"' for message in messages) != 1:
        problems.append("missing or duplicate reference completion marker")
    return {"passed": not problems, "problems": problems}


def fingerprints(lean):
    return {"lean_executable_sha256": FRONT.sha(lean), "module_sha256": FRONT.module_hashes(),
            "source_sha256": FRONT.source_hashes(), "harness_sha256": FRONT.sha(Path(__file__)),
            "shared_runner_sha256": FRONT.sha(Path(FRONT.__file__)),
            "fixture_sha256": {path.name: FRONT.sha(path) for path in sorted(FIXTURES.iterdir()) if path.is_file()},
            "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--budget", "--budget-ms", dest="budget", type=int, default=5000)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--lean", type=Path)
    args = parser.parse_args()
    if min(args.budget, args.timeout_seconds) <= 0 or args.out.exists():
        parser.error("positive budgets and a fresh output directory are required")
    cases = load_cases()
    lean = args.lean or Path(subprocess.check_output(["elan", "which", "lean"], cwd=ROOT, text=True, timeout=15).strip())
    lean = lean.resolve()
    before = fingerprints(lean)
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).strip())
    setup = subprocess.run(["lake", "env", sys.executable, "-c", "import json,os; print(json.dumps(dict(os.environ)))"],
                           cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=True, timeout=30)
    environment = json.loads(setup.stdout)
    if setup.stderr or not isinstance(environment, dict) or not environment.get("LEAN_PATH"):
        parser.error("could not obtain a clean runtime environment")
    # The runtime environment may contain secrets; never print or retain it.
    out = args.out.resolve()
    out.mkdir(parents=True)
    ref = process((FIXTURES / "reference-controls.lean").read_text(encoding="utf-8"), "references", out, lean,
                  environment, args.timeout_seconds)
    ref.update(classify_reference(ref))
    results = []
    for case in cases:
        folder = out / case["id"]
        folder.mkdir()
        text, locations = source(case, args.budget)
        stages = [run_stage(case, "original", text, locations, folder, lean, environment, args.timeout_seconds)]
        if case["replay"] and stages[0]["passed"]:
            completed = stages[0]["completed_source"]
            (folder / "completed-source.txt").write_text(completed, encoding="utf-8", newline="")
            text, locations = source(case, args.budget, completed)
            stages.append(run_stage(case, "replay", text, locations, folder, lean, environment, args.timeout_seconds))
        passed = case_passed(case, stages)
        results.append({"id": case["id"], "expectation": case["expect"], "passed": passed, "stages": stages})
        print(f'{"PASS" if passed else "FAIL"} {case["id"]}', flush=True)
    after = fingerprints(lean)
    final_revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    failures = [r["id"] for r in results if not r["passed"]]
    if not ref["passed"]:
        failures.append("independent reference controls")
    if before != after or revision != final_revision:
        failures.append("inputs changed during run")
    receipt = {"schema_version": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
               "revision": revision, "working_tree_dirty": dirty, "budget_ms": args.budget,
               "lean_executable": str(lean), "inputs_before": before, "inputs_after": after,
               "build_performed": False, "build_verification": "Not performed; fingerprints are not a rebuild.",
               "reference_processes": 1, "reference": ref, "required_cases": len(cases),
               "expected_public_processes": sum(1 + c["replay"] for c in cases),
               "actual_public_processes": sum(len(r["stages"]) for r in results),
               "passed": sum(r["passed"] for r in results), "total": len(cases),
               "success": not failures, "failures": failures, "results": results}
    (out / "receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f'TOTAL {receipt["passed"]}/{len(cases)}', flush=True)
    raise SystemExit(bool(failures))


if __name__ == "__main__":
    main()
