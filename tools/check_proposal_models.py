"""Rerun the nine preserved finite-model suites without changing their receipts.

Each suite runs in a fresh copied directory. Original scripts, JSON evidence,
stdout/stderr and process results are bound by SHA-256. These are Python model
checks, not Lean tests, synthesis measurements, or proofs of general theorems.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "docs/proposals/11-further-improvements/evidence"
CASES = [
    ("N1", "checks/check_models.py", "checks/results.json", True),
    ("N2", "experiments/check_claims.py", "experiments/results.json", True),
    ("N3", "validate_models.py", "model_results.json", True),
    ("N4", "experiments/model_checks.py", "experiments/results.json", True),
    ("N5", "checks/check_design_examples.py", "checks/results.json", False),
    ("N6", "semantic_checks.py", "semantic_results.json", False),
    ("N7", "sanity_checks.py", "sanity_results.json", True),
    ("N8", "model_checks.py", "model_checks.json", True),
    ("N9", "experiments/check_constructions.py", "experiments/results.json", True),
]


def fingerprint(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def inventory(directory):
    return {p.relative_to(directory).as_posix(): fingerprint(p)
            for p in sorted(directory.rglob("*")) if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    assert out.is_relative_to(ROOT / "baseline-out") and not out.exists()
    out.mkdir(parents=True)
    before = inventory(EVIDENCE)
    rows = []
    for ident, script, result, accepts_output in CASES:
        target = out / ident
        shutil.copytree(EVIDENCE / ident, target)
        expected = json.loads((target / result).read_text(encoding="utf-8"))
        command = [sys.executable, "-B", str(target / script)]
        if accepts_output:
            command += ["--output", str(target / result)]
        started = time.monotonic()
        try:
            process = subprocess.run(command, cwd=target, capture_output=True, timeout=180)
            (target / "stdout.bin").write_bytes(process.stdout)
            (target / "stderr.bin").write_bytes(process.stderr)
            actual = json.loads((target / result).read_text(encoding="utf-8"))
            row = {"id": ident, "command": command, "returncode": process.returncode,
                   "empty_stderr": not process.stderr, "matches_archived_result": actual == expected,
                   "elapsed_seconds": round(time.monotonic() - started, 3),
                   "script": fingerprint(target / script), "result": fingerprint(target / result),
                   "stdout": fingerprint(target / "stdout.bin"), "stderr": fingerprint(target / "stderr.bin")}
            row["passed"] = process.returncode == 0 and not process.stderr and actual == expected
        except subprocess.TimeoutExpired as error:
            (target / "stdout.bin").write_bytes(error.stdout or b"")
            (target / "stderr.bin").write_bytes(error.stderr or b"")
            row = {"id": ident, "passed": False, "timed_out": True, "timeout_seconds": 180}
        rows.append(row)
        print(f"{'PASS' if row['passed'] else 'FAIL'} {ident}: archived finite-model result", flush=True)
    after = inventory(EVIDENCE)
    passed = before == after and all(row["passed"] for row in rows)
    receipt = {"scope": "Nine preserved Python finite-model suites only; no Lean or synthesis claim.",
               "python": {"path": sys.executable, **fingerprint(Path(sys.executable))},
               "evidence_before": before, "evidence_after": after,
               "evidence_unchanged": before == after, "runs": rows, "passed": passed}
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
