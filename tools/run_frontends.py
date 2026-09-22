#!/usr/bin/env python3
"""Fresh-process public synth%/leant2 gates and independent printed-text replay.

Each logical case passes only when all its subprocess stages pass. This runner
never builds. It requires already-built public frontend modules. The default
eight-case inventory is a set of acceptance obligations, not a prior pass claim.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import textwrap
import time

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/benchmarks/frontend-fixtures"
HOLE = "__FRONTEND__"
FAILURE_PREFIX = "leant2: synthesis failed:"
VALUE_MARKER = '"FRONTEND_VALUE_OK"'
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|leant2|Leant2)\b|synth%|_leant2")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_cases(folder=FIXTURES):
    payload = json.loads((folder / "cases.json").read_text(encoding="utf-8"))
    if payload["schema_version"] != 1:
        raise ValueError("unsupported frontend fixture schema")
    cases = payload["cases"]
    if len({case["id"] for case in cases}) != len(cases):
        raise ValueError("duplicate frontend case identity")
    for case in cases:
        if not re.fullmatch(r"[a-z][a-z0-9-]*", case["id"]) or case["frontend"] not in ("synth%", "leant2"):
            raise ValueError("invalid frontend case identity/syntax")
        if Path(case["file"]).name != case["file"]:
            raise ValueError("fixture must be a simple filename")
        template = (folder / case["file"]).read_text(encoding="utf-8")
        if HOLE not in template or "import " in template:
            raise ValueError(f"{case['id']}: template must have a hole and no imports")
        if case.get("suggestion_replay") and (case["frontend"] != "leant2" or template.count(HOLE) != 1):
            raise ValueError("suggestion fixtures need exactly one tactic hole")
        if not case["declarations"] or any(not re.fullmatch(r"[A-Za-z_][\w.]*", n) for n in case["declarations"]):
            raise ValueError("invalid declaration audit inventory")
    return cases


def audit_marker(case):
    return f"FRONTEND_AUDIT_{case['id']}_OK"


def audit_source(case):
    names = ", ".join(f"``{name}" for name in case["declarations"])
    return f'''
open Lean Elab Command in
run_cmd do
  for name in [{names}] do
    let ci ← getConstInfo name
    let some value := ci.value? (allowOpaque := true) | throwError "frontend result has no checked value"
    if ci.type.hasMVar || ci.type.hasLevelMVar || ci.type.hasFVar || ci.type.hasSorry ||
        value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasSorry then
      throwError "frontend result contains a hole, free variable, or sorry"
    for axiomName in (← collectAxioms name) do
      unless axiomName ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "frontend result uses a nonstandard axiom: {{axiomName}}"
  logInfo "{audit_marker(case)}"
'''


def insert_text(template, replacement):
    """Only indent emitted text; never re-delaborate, substitute names, or repair it."""
    lines = []
    for line in template.splitlines():
        if HOLE in line:
            column = line.index(HOLE)
            line = line.replace(HOLE, replacement.replace("\n", "\n" + " " * column))
        lines.append(line)
    return "\n".join(lines) + "\n"


def source(case, budget, suggestion=None, folder=FIXTURES):
    template = (folder / case["file"]).read_text(encoding="utf-8")
    header = "import Lean\n" if suggestion is not None else f"import Leant2\nset_option leant2.budgetMs {budget}\n"
    header += "set_option linter.unusedVariables false\n"
    original = header + template
    locations = [index for index, line in enumerate(original.splitlines(), 1) if HOLE in line]
    replacement = case["frontend"] if suggestion is None else suggestion
    return header + insert_text(template, replacement) + audit_source(case), locations


def negative_source(case, budget):
    value = "synth%" if case["frontend"] == "synth%" else "by leant2"
    result = (f"import Leant2\nset_option leant2.budgetMs {budget}\n"
              f"def deliberatelyRejected : False := {value}\n")
    return result, [3]


def messages(stdout):
    parsed, problems = [], []
    for line in stdout.splitlines():
        if not line.strip():
            continue
        try:
            message = json.loads(line)
            if (not isinstance(message, dict) or message.get("severity") not in ("information", "warning", "error")
                    or not isinstance(message.get("data"), str) or not isinstance(message.get("pos"), dict)):
                raise ValueError("not a Lean serialized message")
            parsed.append(message)
        except (ValueError, TypeError):
            problems.append("non-JSON or malformed Lean diagnostic")
    return parsed, problems


def extract_suggestion(parsed, locations, recursive=False):
    suggestions = [message for message in parsed if message["severity"] == "information" and
                   message["data"].lstrip().startswith("Try this:")]
    if len(suggestions) != 1:
        raise ValueError("expected exactly one actual Try this info diagnostic")
    message = suggestions[0]
    if message["pos"].get("line") not in locations:
        raise ValueError("suggestion is not attached to the frontend invocation")
    text = textwrap.dedent(message["data"].lstrip()[len("Try this:"):]).strip()
    # Lean 4.34 Hint.mkSuggestionsMessage prints this widget fallback label
    # before the tactic (Lean/Meta/Hint.lean:467-480). It is not Lean syntax.
    # Remove that exact label/separator only; unknown decorations remain errors.
    if text.startswith("[apply] "):
        text = text[len("[apply] "):]
    if not re.match(r"^exact\s", text) or FORBIDDEN.search(text):
        raise ValueError("suggestion is not an independent complete exact tactic")
    if recursive and (not re.search(r"\bmatch\b|\blet\s+rec\b", text) or re.search(r"\.rec\b", text)):
        raise ValueError("recursive suggestion did not display executable match/let-rec source")
    return text


def classify(case, stage, stdout, stderr, returncode, locations):
    parsed, problems = messages(stdout)
    if stderr:
        problems.append("nonempty subprocess stderr")
    errors = [m for m in parsed if m["severity"] == "error"]
    warnings = [m for m in parsed if m["severity"] == "warning"]
    infos = [m["data"] for m in parsed if m["severity"] == "information"]
    suggestion = None
    if stage == "negative-error":
        if returncode != 1:
            problems.append("expected Lean's ordinary error exit 1")
        if len(errors) != 1 or not errors[0]["data"].startswith(FAILURE_PREFIX) or errors[0]["pos"].get("line") not in locations:
            problems.append("missing or unrelated frontend failure diagnostic")
        if len(warnings) > 1 or any("declaration uses 'sorry'" not in m["data"] or
                                   m["pos"].get("line") not in locations for m in warnings):
            problems.append("unexpected diagnostic in failing declaration")
        if any(text.lstrip().startswith("Try this:") for text in infos):
            problems.append("failed query advertised a suggestion")
    else:
        if returncode != 0:
            problems.append("subprocess did not exit successfully")
        if errors or warnings:
            problems.append("unexpected error or warning")
        if infos.count(audit_marker(case)) != 1:
            problems.append("missing or duplicate checked-declaration completion marker")
        if case.get("observations") and infos.count(VALUE_MARKER) != 1:
            problems.append("missing or failed executable observations")
        if stage == "original" and case.get("suggestion_replay"):
            try:
                suggestion = extract_suggestion(parsed, locations, case.get("recursive_display", False))
            except ValueError as error:
                problems.append(str(error))
        elif any(text.lstrip().startswith("Try this:") for text in infos):
            problems.append("unexpected suggestion in non-synthesis replay/negative stage")
    return {"passed": not problems, "problems": problems, "suggestion": suggestion,
            "diagnostics": {"errors": len(errors), "warnings": len(warnings), "information": len(infos)}}


def run_stage(case, stage, text, locations, folder, lean, timeout, environment):
    filename = folder / f"{stage}.lean"
    filename.write_text(text, encoding="utf-8", newline="\n")
    # Invoke Lean directly after obtaining Lake's environment once. Killing a
    # timed-out Lake wrapper could otherwise leave its native child running.
    command = [str(lean), "--json", str(filename)]
    start = time.monotonic()
    timed_out = False
    invalid_utf8 = False
    raw_stdout, raw_stderr = b"", b""
    try:
        process = subprocess.run(command, cwd=ROOT, capture_output=True, env=environment,
                                 timeout=timeout, check=False)
        raw_stdout, raw_stderr, returncode = process.stdout, process.stderr, process.returncode
    except subprocess.TimeoutExpired as error:
        raw_stdout, raw_stderr, returncode = error.stdout or b"", error.stderr or b"", None
        timed_out = True
    except OSError as error:
        raw_stderr, returncode = str(error).encode("utf-8"), None
    try:
        stdout, stderr = raw_stdout.decode("utf-8"), raw_stderr.decode("utf-8")
    except UnicodeError:
        stdout, stderr = raw_stdout.decode("utf-8", errors="replace"), raw_stderr.decode("utf-8", errors="replace")
        invalid_utf8 = True
    elapsed = round((time.monotonic() - start) * 1000)
    (folder / f"{stage}.stdout.jsonl").write_bytes(raw_stdout)
    (folder / f"{stage}.stderr").write_bytes(raw_stderr)
    result = classify(case, stage, stdout, stderr, returncode, locations)
    if timed_out:
        result["problems"].append("subprocess timeout")
        result["passed"] = False
    if invalid_utf8:
        result["problems"].append("subprocess output is not valid UTF-8")
        result["passed"] = False
    return {"stage": stage, "command": command, "source": text, "source_sha256": sha(filename),
            "stdout": stdout, "stderr": stderr, "returncode": returncode,
            "elapsed_ms": elapsed, "timed_out": timed_out, **result}


def module_hashes():
    return {path.relative_to(ROOT).as_posix(): sha(path)
            for path in sorted((ROOT / ".lake/build/lib/lean").rglob("*"))
            if path.is_file() and path.name.endswith((".olean", ".olean.private", ".olean.server", ".ir"))}


def source_hashes():
    # Include new/untracked implementation modules in dirty development runs;
    # git ls-files alone could omit exactly the frontend being evaluated.
    paths = set(ROOT.glob("*.lean"))
    for directory in (ROOT / "Leant2", ROOT / "tests"):
        paths.update(directory.rglob("*.lean"))
    paths.update(ROOT / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
                 if (ROOT / name).is_file())
    return {path.relative_to(ROOT).as_posix(): sha(path) for path in sorted(paths) if path.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--budget-ms", "--budget", dest="budget_ms", type=int, default=5000)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("--out", type=Path, default=ROOT / "baseline-out/frontends")
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--only", nargs="*")
    args = parser.parse_args()
    if args.budget_ms <= 0 or args.timeout_seconds <= 0:
        parser.error("budgets/timeouts must be positive")
    cases = load_cases()
    if args.only is not None:
        unknown = set(args.only) - {case["id"] for case in cases}
        if unknown or not args.only:
            parser.error(f"unknown or empty case selection: {sorted(unknown)}")
        cases = [case for case in cases if case["id"] in args.only]
    lean = args.lean
    if lean is None:
        lookup = subprocess.run(["elan", "which", "lean"], cwd=ROOT, capture_output=True, text=True,
                                encoding="utf-8", check=True, timeout=15)
        lean = Path(lookup.stdout.strip())
    lean = lean.resolve()
    if not lean.is_file():
        parser.error(f"Lean executable does not exist: {lean}")
    out = args.out.resolve()
    if out.exists():
        parser.error(f"refusing to overwrite raw output directory: {out}")
    def fingerprints():
        return {"lean_executable_sha256": sha(lean), "module_sha256": module_hashes(),
                "source_sha256": source_hashes(), "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
                "harness_sha256": sha(Path(__file__)),
                "fixture_sha256": {path.name: sha(path) for path in sorted(FIXTURES.iterdir()) if path.is_file()}}
    before = fingerprints()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).strip())
    # Never print or archive the environment: it can contain unrelated secrets.
    setup = subprocess.run(["lake", "env", sys.executable, "-c", "import json,os; print(json.dumps(dict(os.environ)))"],
                           cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=True, timeout=30)
    environment = json.loads(setup.stdout)
    if setup.stderr or not isinstance(environment, dict) or not environment.get("LEAN_PATH"):
        parser.error("could not obtain a clean Lake runtime environment")
    out.mkdir(parents=True)
    results = []
    for case in cases:
        folder = out / case["id"]
        folder.mkdir()
        text, locations = source(case, args.budget_ms)
        stages = [run_stage(case, "original", text, locations, folder, lean, args.timeout_seconds, environment)]
        if case.get("suggestion_replay") and stages[0]["passed"]:
            suggestion = stages[0]["suggestion"]
            suggestion_message = next(m["data"] for m in messages(stages[0]["stdout"])[0]
                                      if m["data"].lstrip().startswith("Try this:"))
            (folder / "suggestion-message.txt").write_text(suggestion_message, encoding="utf-8", newline="")
            (folder / "suggestion.txt").write_text(suggestion, encoding="utf-8", newline="\n")
            text, locations = source(case, args.budget_ms, suggestion)
            stages.append(run_stage(case, "suggestion-replay", text, locations, folder, lean, args.timeout_seconds, environment))
        if case.get("negative"):
            text, locations = negative_source(case, args.budget_ms)
            stages.append(run_stage(case, "negative-error", text, locations, folder, lean, args.timeout_seconds, environment))
        expected_stages = 1 + bool(case.get("suggestion_replay")) + bool(case.get("negative"))
        passed = len(stages) == expected_stages and all(stage["passed"] for stage in stages)
        result = {"id": case["id"], "passed": passed, "stages": stages}
        results.append(result)
        print(f"{'PASS' if passed else 'FAIL'} {case['id']} [{sum(s['elapsed_ms'] for s in stages)} ms]", flush=True)
    after = fingerprints()
    passed = sum(result["passed"] for result in results)
    failures = [result["id"] for result in results if not result["passed"]]
    if before != after:
        failures.append("Lean executable, compiled artifacts, sources, toolchain, harness, or fixtures changed during the run")
    final_revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if final_revision != revision:
        failures.append("repository revision changed during the run")
    receipt = {"schema_version": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
               "revision": revision, "working_tree_dirty": dirty, "budget_ms": args.budget_ms,
               "lean_executable": str(lean), **before, "inputs_changed_during_run": before != after,
               "build_performed": False,
               "build_verification": "Not performed by this runner; source and prebuilt artifacts are fingerprinted, not rebuilt.",
               "passed": passed, "total": len(cases), "success": not failures, "failures": failures,
               "results": results}
    (out / "receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"TOTAL {passed}/{len(cases)}", flush=True)
    raise SystemExit(0 if not failures else 1)


if __name__ == "__main__":
    main()
