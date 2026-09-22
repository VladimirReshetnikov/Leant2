#!/usr/bin/env python3
"""Run frozen foldr1 controls and both budgets; never build or rewrite sources.

Exit 0: controls passed and both budgets accepted. Exit 2: a valid experiment
contains a bounded miss. Exit 1: invalid inputs, native failure, or input drift.
Runtime environment mappings/values are never printed or persisted.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BUDGETS = (5000, 10000)
MODULE_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
CONTROL_EXTRA = ["Foldr1CarrierControl.carrierReference",
                 "Foldr1CarrierControl.carrierReference_passes",
                 "Foldr1CarrierControl.carrierReference_enc"]
WORK_FIELDS = ("ruleApplications", "unifications", "proofAttempts", "candidates", "rejected")
MARKERS = {
    "PROBE_BEGIN", "PROBE_ELAPSED_MS", "PROBE_PREPARATION", "PROBE_OUTCOME", "PROBE_LEDGER",
    "PROBE_CANDIDATE", "PROBE_PROGRAM_TYPE", "PROBE_PROGRAM", "PROBE_PROGRAM_CONSTANTS",
    "PROBE_PROGRAM_DEPENDENCIES_REVIEWED", "PROBE_ACCEPTED", "PROBE_NOT_ACCEPTED",
    "PROBE_NEGATIVE_STATEMENT", "PROBE_NEGATIVE_CERTIFICATE",
}
MULTILINE = {"PROBE_PREPARATION", "PROBE_LEDGER", "PROBE_PROGRAM_TYPE", "PROBE_PROGRAM",
             "PROBE_PROGRAM_CONSTANTS", "PROBE_NEGATIVE_STATEMENT", "PROBE_NEGATIVE_CERTIFICATE"}


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def inventory(paths, base: Path):
    return {path.relative_to(base).as_posix(): {"size_bytes": path.stat().st_size, "sha256": sha(path)}
            for path in sorted(set(paths)) if path.is_file()}


def write_json(path: Path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write("\n")


def original_provenance():
    manifest = json.loads((HERE / "provenance.json").read_text(encoding="utf-8"))
    required = {
        "source_case_id": "church_case_039", "operation": "foldr1", "source_line": 295,
        "observation_count": 36, "profile": "strictConstructive", "explicit_query_providers": [],
        "carrier": "Option A", "open_holes_in_source_order": ["step", "init", "finish"],
        "budgets_ms": list(BUDGETS),
    }
    for key, expected in required.items():
        if manifest.get(key) != expected:
            raise ValueError(f"unexpected frozen provenance field: {key}")
    observations = manifest.get("observations", [])
    if len(observations) != 36 or len({row["id"] for row in observations}) != 36:
        raise ValueError("the original 36 distinct observations are required")
    for filename, field in [("Probe.lean", "probe_sha256"), ("Controls.lean", "controls_sha256"),
                            ("Probe.body.lean.in", "template_sha256")]:
        if sha(HERE / filename) != manifest[field]:
            raise ValueError(f"frozen source does not match provenance: {filename}")
    spec = Path(manifest["spec_path"]).resolve()
    if sha(spec) != manifest["spec_sha256_bytes"]:
        raise ValueError("original specification bytes changed")
    corpus_manifest = spec.parent / "manifest.json"
    corpus = json.loads(corpus_manifest.read_text(encoding="utf-8"))
    church = (spec.parent.parent / corpus["source"]).resolve()
    # Identical to the specification: UTF-8 without BOM, universal newlines.
    normalized = hashlib.sha256(church.read_text(encoding="utf-8-sig").encode("utf-8")).hexdigest()
    if normalized != manifest["source_sha256_normalized"] or normalized != corpus["source_sha256"]:
        raise ValueError("original Church source provenance changed")
    return manifest, spec, corpus_manifest, church, normalized


def fingerprints(lean: Path, provenance_paths):
    toolchain = lean.parent.parent
    sources = set(ROOT.glob("*.lean"))
    for folder in (ROOT / "Leant2", ROOT / "tests"):
        sources.update(folder.rglob("*.lean"))
    sources.update(ROOT / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"))
    local_modules = [p for p in (ROOT / ".lake/build/lib/lean").rglob("*")
                     if p.name.endswith(MODULE_SUFFIXES)]
    toolchain_modules = [p for p in (toolchain / "lib/lean").rglob("*")
                         if p.name.endswith(MODULE_SUFFIXES)]
    native = [p for p in (toolchain / "bin").iterdir() if p.suffix.lower() in (".exe", ".dll", ".so", ".dylib")]
    native.extend(p for p in (toolchain / "lib").rglob("*")
                  if p.suffix.lower() in (".dll", ".so", ".dylib"))
    frozen = [HERE / name for name in ("Probe.lean", "Controls.lean", "Probe.body.lean.in",
                                      "provenance.json", "prepare.py", "run_probe.py")]
    external = {str(path): {"size_bytes": path.stat().st_size, "sha256": sha(path)}
                for path in sorted(set(provenance_paths))}
    if not local_modules or not toolchain_modules or not native:
        raise ValueError("missing prebuilt local modules or toolchain artifacts")
    return {
        "declared_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_executable": {"path": str(lean), "sha256": sha(lean)},
        "python_executable": {"path": sys.executable, "sha256": sha(Path(sys.executable)), "version": sys.version},
        "source_files": inventory(sources, ROOT),
        "local_module_files": inventory(local_modules, ROOT),
        "toolchain_module_files": inventory(toolchain_modules, toolchain),
        "toolchain_native_files": inventory(native, toolchain),
        "frozen_probe_files": inventory(frozen, HERE),
        "original_provenance_files": external,
    }


def parse_output(stdout: str):
    diagnostics, blocks, problems = [], [], []
    for line in stdout.splitlines():
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except ValueError:
            value = None
        if isinstance(value, dict) and "severity" in value:
            if value.get("severity") not in ("information", "warning", "error") or not isinstance(value.get("data"), str):
                problems.append("malformed Lean JSON diagnostic")
            else:
                diagnostics.append(value)
            continue
        match = re.match(r"^(PROBE_[A-Z_]+)(?: (.*))?$", line)
        if match:
            key, text = match[1], match[2] or ""
            if key not in MARKERS:
                problems.append(f"unknown probe marker: {key}")
            blocks.append([key, text])
        elif blocks and blocks[-1][0] in MULTILINE:
            blocks[-1][1] += "\n" + line
        else:
            problems.append("unexpected non-JSON/non-marker stdout")
    return diagnostics, blocks, problems


def is_probe_transcript_envelope(message):
    """Lean captures run_elab's IO.println into this exact information span."""
    source = HERE / "Probe.lean"
    starts = [n for n, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1)
              if line == "run_elab do"]
    if len(starts) != 1:
        return False
    try:
        same_file = Path(message.get("fileName", "")).resolve() == source.resolve()
    except (OSError, ValueError, TypeError):
        return False
    return (same_file and message.get("severity") == "information" and
            message.get("pos") == {"line": starts[0], "column": 0} and
            message.get("endPos") == {"line": starts[0], "column": len("run_elab")} and
            message.get("caption", "") == "")


def classify(raw, controls: list[str] | None = None, budget: int | None = None):
    problems = []
    if raw["returncode"] != 0:
        problems.append("native process did not exit zero")
    if raw["timed_out"]:
        problems.append("external process timeout")
    if raw["launch_error"]:
        problems.append("native process launch failed")
    if raw.get("interrupted"):
        problems.append("execution wrapper interrupted")
    if raw["stderr"]:
        problems.append("native process wrote stderr")
    try:
        stdout = raw["stdout"].decode("utf-8")
        raw["stderr"].decode("utf-8")
    except UnicodeDecodeError:
        return {"classification": "failure", "problems": problems + ["invalid UTF-8 native output"]}
    diagnostics, blocks, parse_problems = parse_output(stdout)
    problems += parse_problems
    if any(d["severity"] != "information" for d in diagnostics):
        problems.append("native error or warning diagnostic")
    if controls is not None:
        if blocks:
            problems.append("probe output occurred in the independent controls process")
        expected = {f"'{name}' does not depend on any axioms" for name in controls}
        actual = [d["data"].strip() for d in diagnostics]
        if len(actual) != len(expected) or set(actual) != expected:
            problems.append("missing, duplicate, unexpected, or non-axiom-free control audit")
        return {"classification": "failure" if problems else "controls_passed", "problems": problems,
                "audited_control_declarations": controls, "diagnostic_count": len(diagnostics)}
    transport = "stdout_markers"
    if diagnostics:
        # A single envelope at the frozen source's run_elab span is expected.
        # Extra diagnostics, raw marker mixtures, nested diagnostic payloads,
        # and transcripts from any other location remain failures.
        if (len(diagnostics) == 1 and not blocks and not parse_problems and
                is_probe_transcript_envelope(diagnostics[0])):
            nested, blocks, inner_problems = parse_output(diagnostics[0]["data"])
            problems += inner_problems
            if nested:
                problems.append("nested Lean diagnostics inside the probe transcript")
            transport = "lean_information_envelope"
        else:
            problems.append("unexpected Lean diagnostic/envelope in synthesis probe")
    grouped = {}
    for key, value in blocks:
        grouped.setdefault(key, []).append(value)

    def one(key):
        values = grouped.get(key, [])
        if len(values) != 1:
            problems.append(f"expected exactly one {key}")
            return ""
        return values[0]

    begin = f"case=church_case_039 operation=foldr1 observations=36 providers=0 profile=strictConstructive budgetMs={budget}"
    if one("PROBE_BEGIN") != begin:
        problems.append("probe identity/budget differs from frozen contract")
    elapsed = one("PROBE_ELAPSED_MS")
    if not elapsed.isdecimal():
        problems.append("invalid reported API elapsed time")
    if not one("PROBE_PREPARATION"):
        problems.append("missing preparation report")
    work_text = one("PROBE_LEDGER")
    work = {}
    for field in WORK_FIELDS:
        values = re.findall(rf"\b{field}\s*:=\s*(\d+)", work_text)
        if len(values) != 1:
            problems.append(f"missing/duplicate ledger field {field}")
        else:
            work[field] = int(values[0])
    outcome = one("PROBE_OUTCOME")
    classification = "failure"
    terminal = ""
    candidate_keys = {"PROBE_CANDIDATE", "PROBE_PROGRAM_TYPE", "PROBE_PROGRAM",
                      "PROBE_PROGRAM_CONSTANTS", "PROBE_PROGRAM_DEPENDENCIES_REVIEWED"}
    if outcome == "verified candidates=1":
        terminal = "PROBE_ACCEPTED"
        if one(terminal) != "exact_type_and_all_36_observations_replayed":
            problems.append("missing exact original-query acceptance marker")
        if one("PROBE_CANDIDATE") != "0 original_type_replayed=true original_observations_replayed=36 strict_axioms=0":
            problems.append("missing strict original-query candidate replay")
        for key in candidate_keys - {"PROBE_CANDIDATE"}:
            if not one(key):
                problems.append(f"empty {key}")
        if "PROBE_NOT_ACCEPTED" in grouped:
            problems.append("contradictory miss marker after verified result")
        if work.get("candidates", 0) < 1:
            problems.append("accepted result has no charged candidate")
        reviewed = grouped.get("PROBE_PROGRAM_DEPENDENCIES_REVIEWED", [])
        if len(reviewed) != 1 or not reviewed[0].isdecimal():
            problems.append("invalid program dependency audit count")
        classification = "accepted"
    elif re.fullmatch(r"refutedAll rejected=[1-9]\d*", outcome):
        terminal = "PROBE_NOT_ACCEPTED"
        if one(terminal) != "bounded_proposals_failed_no_impossibility_claim":
            problems.append("missing bounded-refutation marker")
        if work.get("rejected") != int(outcome.rsplit("=", 1)[1]):
            problems.append("rejected outcome disagrees with its ledger")
        classification = "bounded_miss"
    elif re.fullmatch(r"negative kind=Leant2\.NegativeKind\.(grammarExhausted|budgetExhausted) certificate=false", outcome):
        terminal = "PROBE_NOT_ACCEPTED"
        if one(terminal) != "inspect_negative_kind_and_certificate":
            problems.append("missing bounded-negative marker")
        classification = "bounded_miss"
    else:
        problems.append("unexpected/malformed outcome; semantic negatives contradict the independent witness")
    if classification != "accepted" and (candidate_keys & grouped.keys() or "PROBE_ACCEPTED" in grouped):
        problems.append("candidate/acceptance marker in a non-verified outcome")
    if "PROBE_NEGATIVE_STATEMENT" in grouped or "PROBE_NEGATIVE_CERTIFICATE" in grouped:
        problems.append("unexpected semantic certificate")
    if not blocks or blocks[0][0] != "PROBE_BEGIN" or blocks[-1][0] != terminal:
        problems.append("missing or misplaced terminal probe marker")
    return {"classification": "failure" if problems else classification, "problems": problems,
            "actual_outcome": outcome, "ledger": work,
            "api_elapsed_ms": int(elapsed) if elapsed.isdecimal() else None,
            "preparation_report": grouped.get("PROBE_PREPARATION", []),
            "diagnostic_count": len(diagnostics), "transcript_transport": transport}


def runtime_environment(lean: Path, budget: int | None):
    # This mapping exists only in memory and is passed directly to Popen.
    # Never print, serialize, or attach it to exceptions/receipts.
    environment = os.environ.copy()
    environment["PATH"] = str(lean.parent) + os.pathsep + environment.get("PATH", "")
    environment["LEAN_SYSROOT"] = str(lean.parent.parent)
    environment["LEAN_PATH"] = (str(lean.parent.parent / "lib/lean") if budget is None
                                else str(ROOT / ".lake/build/lib/lean"))
    if budget is None:
        environment.pop("LEANT2_SKETCH_PROBE_BUDGET_MS", None)
    else:
        environment["LEANT2_SKETCH_PROBE_BUDGET_MS"] = str(budget)
    return environment


def run_native(lean: Path, source: Path, folder: Path, timeout: int, budget: int | None):
    folder.mkdir()
    command = [str(lean), "--json", str(source)]
    timed_out, interrupted, launch_error, returncode, cleanup = False, False, False, None, None
    source_before, executable_before = sha(source), sha(lean)
    start = time.monotonic()
    with (folder / "stdout.bin").open("xb") as stdout, (folder / "stderr.bin").open("xb") as stderr:
        options = {"creationflags": subprocess.CREATE_NO_WINDOW} if os.name == "nt" else {"start_new_session": True}
        try:
            process = subprocess.Popen(command, cwd=ROOT, env=runtime_environment(lean, budget),
                                       stdout=stdout, stderr=stderr, **options)
        except OSError:
            # Do not persist an exception containing a runtime environment.
            launch_error = True
        else:
            try:
                returncode = process.wait(timeout=timeout)
            except (subprocess.TimeoutExpired, KeyboardInterrupt) as stopped:
                timed_out = isinstance(stopped, subprocess.TimeoutExpired)
                interrupted = isinstance(stopped, KeyboardInterrupt)
                if process.poll() is not None:
                    cleanup = {"tree_cleanup_attempted": False, "already_exited": True}
                elif os.name == "nt":
                    taskkill = shutil.which("taskkill.exe")
                    if taskkill:
                        try:
                            stopped = subprocess.run([taskkill, "/PID", str(process.pid), "/T", "/F"],
                                                     capture_output=True, timeout=10,
                                                     creationflags=subprocess.CREATE_NO_WINDOW)
                            cleanup = {"tree_cleanup_attempted": True, "returncode": stopped.returncode,
                                       "executable": str(Path(taskkill).resolve()), "sha256": sha(Path(taskkill))}
                        except (OSError, subprocess.TimeoutExpired):
                            cleanup = {"tree_cleanup_attempted": True, "failed": True}
                    else:
                        cleanup = {"tree_cleanup_attempted": False}
                    if process.poll() is None:
                        process.kill()
                else:
                    os.killpg(process.pid, signal.SIGKILL)
                    cleanup = {"tree_cleanup_attempted": True}
                returncode = process.wait(timeout=10)
    elapsed = round((time.monotonic() - start) * 1000)
    raw = {"stdout": (folder / "stdout.bin").read_bytes(), "stderr": (folder / "stderr.bin").read_bytes(),
           "returncode": returncode, "timed_out": timed_out, "interrupted": interrupted, "launch_error": launch_error}
    public = {key: value for key, value in raw.items() if key not in ("stdout", "stderr")}
    public.update({"command": command, "process_timeout_seconds": timeout, "process_elapsed_ms": elapsed,
                   "cleanup": cleanup, "source_sha256_before": source_before, "source_sha256_after": sha(source),
                   "lean_sha256_before": executable_before, "lean_sha256_after": sha(lean),
                   "artifact_paths_relative_to": "top-level receipt directory",
                   "stdout": {"file": f"{folder.name}/stdout.bin", "bytes": len(raw["stdout"]), "sha256": sha(folder / "stdout.bin")},
                   "stderr": {"file": f"{folder.name}/stderr.bin", "bytes": len(raw["stderr"]), "sha256": sha(folder / "stderr.bin")}})
    return raw, public


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True, help="explicit matching prebuilt lean.exe")
    parser.add_argument("--out", type=Path, required=True, help="fresh evidence directory; never overwritten")
    parser.add_argument("--controls-timeout-seconds", type=int, default=120)
    parser.add_argument("--probe-timeout-seconds", type=int, default=120)
    args = parser.parse_args()
    lean, out = args.lean.resolve(), args.out.resolve()
    if not lean.is_file() or out.exists() or min(args.controls_timeout_seconds, args.probe_timeout_seconds) <= 0:
        parser.error("an existing Lean executable, positive timeouts, and fresh output directory are required")
    if json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8")).get("packages") != []:
        parser.error("manual isolated runtime setup requires this project's zero-dependency manifest")
    manifest, spec, corpus_manifest, church, normalized = original_provenance()
    controls = manifest["control_declarations"] + CONTROL_EXTRA
    if len(controls) != 11 or len(set(controls)) != 11:
        parser.error("expected the original eight and three carrier control audits")
    original_paths = [spec, corpus_manifest, church, *spec.parent.glob("behavior*.py")]
    out.mkdir(parents=True)
    (out / "source-provenance.json").write_bytes((HERE / "provenance.json").read_bytes())
    (out / "original-corpus-manifest.json").write_bytes(corpus_manifest.read_bytes())
    receipt = {
        "schema_version": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
        "status": "running", "controls": None, "probes": [], "failures": [],
        "source_case_id": "church_case_039", "observation_count": 36, "budgets_ms": list(BUDGETS),
        "original_church_sha256_normalized": normalized, "original_spec_sha256": sha(spec),
        "build_performed": False, "build_verification": "Not performed; exact source/artifact fingerprints are not a rebuild.",
        "environment_values_persisted": False,
        "runtime_setup": "Direct pinned Lean; isolated Lean-only controls; only local prebuilt modules for probe; no package dependencies.",
        "source_mutation_performed": False,
    }
    before = None
    try:
        before = fingerprints(lean, original_paths)
        write_json(out / "inputs-before.json", before)
        raw, process = run_native(lean, HERE / "Controls.lean", out / "controls", args.controls_timeout_seconds, None)
        audit = classify(raw, controls=controls)
        receipt["controls"] = {**process, **audit}
        write_json(out / "controls/result.json", receipt["controls"])
        if audit["classification"] != "controls_passed":
            receipt["failures"].append("independent reference controls failed; synthesis not run")
        else:
            for budget in BUDGETS:
                raw, process = run_native(lean, HERE / "Probe.lean", out / f"probe-{budget}", args.probe_timeout_seconds, budget)
                audit = classify(raw, budget=budget)
                result = {"budget_ms": budget, **process, **audit}
                receipt["probes"].append(result)
                write_json(out / f"probe-{budget}/result.json", result)
                print(f"{budget} ms: {audit['classification']}", flush=True)
                if audit["classification"] == "failure":
                    receipt["failures"].append(f"probe at {budget} ms failed")
                    break
    except Exception as error:
        # Class/type only: no accidental exception payload/environment capture.
        receipt["failures"].append(f"wrapper failure ({type(error).__name__}); inspect available raw evidence")
    finally:
        try:
            after = fingerprints(lean, original_paths)
            write_json(out / "inputs-after.json", after)
            receipt["inputs_unchanged"] = before is not None and before == after
            if not receipt["inputs_unchanged"]:
                receipt["failures"].append("source/module/native/provenance fingerprints changed or are incomplete")
        except Exception as error:
            receipt["inputs_unchanged"] = False
            receipt["failures"].append(f"final fingerprint failure ({type(error).__name__})")
        for result in [receipt["controls"], *receipt["probes"]]:
            if result and (result["source_sha256_before"] != result["source_sha256_after"] or
                           result["lean_sha256_before"] != result["lean_sha256_after"]):
                receipt["failures"].append("source or native executable changed during a process")
        classifications = [result["classification"] for result in receipt["probes"]]
        receipt["skipped_budgets_ms"] = [b for b in BUDGETS if b not in [p["budget_ms"] for p in receipt["probes"]]]
        valid = not receipt["failures"] and len(classifications) == 2
        receipt["experiment_valid"] = valid
        receipt["all_budgets_accepted"] = valid and classifications == ["accepted", "accepted"]
        receipt["status"] = "failure" if not valid else ("accepted_both_budgets" if receipt["all_budgets_accepted"] else "bounded_miss")
        receipt["exit_code"] = 1 if not valid else (0 if receipt["all_budgets_accepted"] else 2)
        receipt["completed_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(out / "receipt.json", receipt)
    print(f"{receipt['status']}: {out / 'receipt.json'}", flush=True)
    return receipt["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
