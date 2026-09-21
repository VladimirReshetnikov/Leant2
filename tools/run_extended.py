#!/usr/bin/env python3
"""Run independently replayed E8 probes; print TOTAL and write a JSON receipt.

Every query uses a fresh process. Known open searches are reported separately;
errors, missing output, false-positive controls, and unusable candidates always
fail the run. This is an initial local suite, not an import of Myth or Smyth.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tests/benchmarks/extended.json"
REPLAY_OK = '"EXTENDED_REPLAY_OK"'
REPLAY_FALSE = '"EXTENDED_REPLAY_FALSE"'
ERROR = re.compile(r"(?im)(?:^|\s)(?:error(?:\([^)]*\))?:|PANIC|uncaught exception)|declaration uses ['`]sorry")
CANDIDATE = re.compile(r"(?m)^  it1(?:\s|$)")
NO_CANDIDATE = {
    "refuted": "program(s) of the type proposed, none passed the contract",
    "contract_impossible": "provably no program satisfies the contract",
    "uninhabited": "provably uninhabited",
    "search_exhausted": "no term found within the search bounds",
    "budget_exhausted": "budget exhausted",
}


def load_cases(path: Path = MANIFEST) -> list[dict]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    cases = payload["cases"]
    names = [c["id"] for c in cases]
    if len(set(names)) != len(names) or not cases:
        raise ValueError("benchmark ids must be unique and nonempty")
    for c in cases:
        if not re.fullmatch(r"[a-z][a-z0-9_]*", c["id"]):
            raise ValueError(f"invalid benchmark id: {c['id']}")
        if c["expect"] not in ("candidate", "open", "none"):
            raise ValueError(f"invalid expectation: {c['id']}")
        if c["expect"] == "none" and c.get("contract") != "False":
            raise ValueError(f"negative controls must have the False contract: {c['id']}")
        if c["expect"] != "none" and not c.get("reference"):
            raise ValueError(f"positive fixture needs a checked reference: {c['id']}")
        forbidden = c.get("forbidden_providers", [])
        if not isinstance(forbidden, list) or any(
                not isinstance(name, str) or
                not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", name)
                for name in forbidden):
            raise ValueError(f"forbidden_providers require declaration names: {c['id']}")
        checks = c.get("kernel_checks", [])
        if not isinstance(checks, list) or any(
                not isinstance(check, dict) or
                not isinstance(check.get("type"), str) or not check["type"].strip() or
                not isinstance(check.get("proof"), str) or not check["proof"].strip() or
                ("reference_proof" in check and
                 (not isinstance(check["reference_proof"], str) or
                  not check["reference_proof"].strip())) for check in checks):
            raise ValueError(f"kernel_checks require nonempty type/proof strings: {c['id']}")
    return cases


def replay_commands(case: dict, name: str = "it1") -> list[str]:
    commands = [f"example : {case['type']} := {name}"]
    for check in case.get("kernel_checks", []):
        proposition = check["type"].replace("{f}", name)
        proof = check["proof"].replace("{f}", name)
        commands.append(f"example : {proposition} := {proof}")
    if case.get("replay_proof"):
        predicate = case["contract"].replace("{f}", name)
        proof = case["replay_proof"].replace("{f}", name)
        commands.append(f"example : {predicate} := {proof}")
    observation = case.get("replay") or case.get("contract")
    if observation:
        observation = observation.replace("{f}", name)
        commands.append(f'#eval if decide ({observation}) then {REPLAY_OK} else {REPLAY_FALSE}')
    else:
        # Proof-valued targets have already been checked at their exact type.
        commands.append(f"#eval ({REPLAY_OK} : String)")
    return commands


def transcript(case: dict) -> str:
    lines = []
    if case.get("prelude"):
        lines += [":{", case["prelude"], ":}"]
    if case.get("forbidden_providers"):
        lines += [":{", "open Lean Elab Command in", "run_cmd do",
                  "  let providers := (← liftCoreM Leant2.sessionConstants) ++ Leant2.curatedProviders"]
        for name in case["forbidden_providers"]:
            lines.append(f'  if providers.contains `{name} then throwError "benchmark forbids synthesis provider {name}"')
        lines.append(":}")
    query = f":synth extended_candidate : {case['type']}"
    if case.get("contract"):
        query += " where " + case["contract"].replace("{f}", "extended_candidate")
    lines.append(query)
    # Do not elaborate references in the synthesis environment. Replay is
    # guarded so a legitimate open result does not produce unknown-it1 errors.
    lines += [":{", "open Lean Elab Command in", "run_cmd do",
              "  if (Leant2.resultBinding? (← getEnv) `it1).isSome then"]
    for command in replay_commands(case):
        lines.append(f"    elabCommand (← `({command}))")
    lines += [":}", ":quit", ""]
    return "\n".join(lines)


def classify(case: dict, stdout: str, stderr: str, returncode: int) -> dict:
    has_candidate = bool(CANDIDATE.search(stdout))
    times = re.findall(r"(?m)^(?:-- )?leant2: (\d+) ms$", stdout)
    result = {
        "candidate": has_candidate,
        "candidate_text": next((line.strip() for line in stdout.splitlines()
                                if CANDIDATE.fullmatch(line) or line.startswith("  it1 ")), None),
        "query_elapsed_ms": int(times[0]) if len(times) == 1 else None,
        "replayed": REPLAY_OK in stdout,
        "time_to_first_candidate_ms": None,
        "reference_rank": None,
    }
    if returncode != 0:
        outcome, reason = "process_error", f"process exited {returncode}"
    elif ERROR.search(stdout) or stderr.strip():
        outcome, reason = "error", "Lean diagnostic or stderr output"
    elif stdout.count("λ> :synth ") != 1 or len(times) != 1:
        outcome, reason = "protocol_error", "expected one completed query and one timing record"
    elif has_candidate:
        if case["expect"] == "none":
            outcome, reason = "false_positive", "accepted an impossible contract"
        elif REPLAY_FALSE in stdout:
            outcome, reason = "false_positive", "bound candidate failed executable observations"
        elif stdout.count(REPLAY_OK) != 1:
            outcome, reason = "replay_error", "candidate lacked successful typed/executable replay"
        else:
            outcome, reason = "solved", "candidate replayed"
    else:
        categories = [name for name, message in NO_CANDIDATE.items() if message in stdout]
        if len(categories) != 1 or REPLAY_OK in stdout or REPLAY_FALSE in stdout:
            outcome, reason = "protocol_error", "unrecognized or contradictory outcome"
        else:
            outcome, reason = categories[0], "no candidate"
    # References establish that every open case has a solution. A claimed
    # impossibility is therefore a soundness failure, not an expected miss.
    nonfatal_open = outcome in ("refuted", "search_exhausted", "budget_exhausted", "solved")
    passed = (outcome == "solved" if case["expect"] == "candidate" else
              outcome == "contract_impossible" if case["expect"] == "none" else nonfatal_open)
    result.update(outcome=outcome, reason=reason, passed=passed)
    return result


def runtime_env() -> dict[str, str]:
    env = dict(os.environ)
    try:
        proc = subprocess.run(["elan", "which", "lean"], cwd=ROOT, capture_output=True,
                              text=True, encoding="utf-8", timeout=15)
        if proc.returncode == 0 and proc.stdout.strip():
            env["PATH"] = str(Path(proc.stdout.strip()).parent) + os.pathsep + env.get("PATH", "")
    except (OSError, subprocess.TimeoutExpired):
        pass
    return env


def fixture_source(cases: list[dict]) -> str:
    """Validate setup, reference types, observations, and universal contracts.

    These references are only supplied to the fixture-validation Lean process;
    they never become synthesis providers or candidate replay helpers.
    """
    lines = ["import Lean"]
    for c in cases:
        if c["expect"] == "none":
            continue
        lines += [f"namespace Fixture_{c['id']}", c.get("prelude", ""),
                  f"def reference : {c['type']} := {c['reference']}"]
        if c.get("contract"):
            pred = c["contract"].replace("{f}", "reference")
            proof = c.get("reference_proof", "by decide").replace("{f}", "reference")
            lines.append(f"example : {pred} := {proof}")
        for check in c.get("kernel_checks", []):
            proposition = check["type"].replace("{f}", "reference")
            proof = check.get("reference_proof", check["proof"]).replace("{f}", "reference")
            lines.append(f"example : {proposition} := {proof}")
        observation = c.get("replay")
        if observation:
            lines.append(f"example : {observation.replace('{f}', 'reference')} := by decide")
        lines += [f"end Fixture_{c['id']}", ""]
    return "\n".join(lines)


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--exe", default=str(ROOT / ".lake/build/bin/leant2.exe"))
    ap.add_argument("--manifest", type=Path, default=MANIFEST,
                    help="benchmark manifest (default: tests/benchmarks/extended.json)")
    ap.add_argument("--budget", type=int, default=10000)
    ap.add_argument("--case", action="append", default=[], help="exact case id; may repeat")
    ap.add_argument("--out", default=str(ROOT / "baseline-out/extended.json"))
    ap.add_argument("--timeout", type=float, help="process wall timeout in seconds (default: budget + 30)")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--validate-fixtures", action="store_true", help="check references with Lean, without synthesis")
    args = ap.parse_args()
    manifest = args.manifest.resolve()
    cases = load_cases(manifest)
    if args.budget <= 0 or (args.timeout is not None and args.timeout <= 0):
        ap.error("budget and timeout must be positive")
    if args.case:
        unknown = set(args.case) - {c["id"] for c in cases}
        if unknown:
            ap.error("unknown cases: " + ", ".join(sorted(unknown)))
        cases = [c for c in cases if c["id"] in args.case]
    if args.list:
        for c in cases:
            print(f"{c['id']:30} {c['expect']:10} {c['title']}")
        return 0
    out_path = Path(args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    if args.validate_fixtures:
        source = out_path.with_suffix(".fixtures.lean")
        source.write_text(fixture_source(cases), encoding="utf-8")
        proc = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT,
                              capture_output=True, text=True, encoding="utf-8", errors="replace",
                              timeout=120)
        print(proc.stdout, end="")
        print(proc.stderr, end="", file=sys.stderr)
        count = sum(c["expect"] != "none" for c in cases)
        print(f"FIXTURES {'PASS' if proc.returncode == 0 else 'FAIL'} {count} positive references: {source}")
        return 0 if proc.returncode == 0 else 1
    exe = Path(args.exe).resolve()
    if not exe.is_file():
        ap.error(f"executable does not exist: {exe}; build with lake build leant2")
    env = runtime_env()
    executable_sha256 = hashlib.sha256(exe.read_bytes()).hexdigest()
    rows = []
    for c in cases:
        src = transcript(c)
        start = time.monotonic()
        try:
            proc = subprocess.run([str(exe), f"--budget={args.budget}"], input=src,
                                  cwd=ROOT, env=env, capture_output=True, text=True,
                                  encoding="utf-8", errors="replace",
                                  timeout=args.timeout or args.budget / 1000 + 30)
            stdout, stderr = proc.stdout, proc.stderr
            result = classify(c, stdout, stderr, proc.returncode)
            result["returncode"] = proc.returncode
        except (OSError, subprocess.TimeoutExpired) as error:
            stdout = getattr(error, "stdout", "") or ""
            stderr = getattr(error, "stderr", "") or ""
            stdout = stdout.decode("utf-8", "replace") if isinstance(stdout, bytes) else stdout
            stderr = stderr.decode("utf-8", "replace") if isinstance(stderr, bytes) else stderr
            result = {"outcome": "process_timeout" if isinstance(error, subprocess.TimeoutExpired) else "process_error",
                      "reason": str(error), "passed": False, "candidate": False, "replayed": False,
                      "query_elapsed_ms": None, "time_to_first_candidate_ms": None, "reference_rank": None,
                      "returncode": None}
        result.update(id=c["id"], title=c["title"], group=c["group"], expectation=c["expect"],
                      wall_elapsed_ms=round((time.monotonic() - start) * 1000),
                      source=c["source"], transcript=src, stdout=stdout, stderr=stderr)
        rows.append(result)
        status = "PASS" if result["passed"] else "FAIL"
        if c["expect"] == "open" and result["passed"]:
            status = "OPEN-SOLVED" if result["outcome"] == "solved" else "OPEN"
        print(f"{status} {c['id']} {result['outcome']} [{result['query_elapsed_ms']} ms]", flush=True)
    scored = [r for r in rows if r["expectation"] != "open"]
    open_rows = [r for r in rows if r["expectation"] == "open"]
    failures = [r["id"] for r in rows if not r["passed"]]
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True)
    dirty = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT, capture_output=True, text=True)
    executable_changed = hashlib.sha256(exe.read_bytes()).hexdigest() != executable_sha256
    if executable_changed:
        failures.append("executable_changed_during_run")
    receipt = {"schema_version": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
               "revision": revision.stdout.strip(), "working_tree_dirty": bool(dirty.stdout.strip()),
               "executable": str(exe), "executable_sha256": executable_sha256,
               "executable_changed_during_run": executable_changed,
               "manifest": str(manifest),
               "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(), "budget_ms": args.budget,
               "capabilities_and_controls": {"passed": sum(r["passed"] for r in scored), "total": len(scored)},
               "open": {"solved": sum(r["outcome"] == "solved" for r in open_rows), "total": len(open_rows)},
               "failures": failures, "success": not failures, "results": rows}
    out_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"OPEN {receipt['open']['solved']}/{len(open_rows)} solved")
    print(f"TOTAL {sum(r['passed'] for r in scored)}/{len(scored)}")
    print(f"RECEIPT {out_path}")
    # Open cases do not inflate TOTAL, but their errors still fail the process.
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
