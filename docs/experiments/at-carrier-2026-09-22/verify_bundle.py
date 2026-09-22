#!/usr/bin/env python3
"""Read-only byte/receipt/raw-classification audit. Never starts native tools.

The archived original classifier is unchanged. Its envelope path is rebound in
memory only for the exact recorded path and byte-identical historical source.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import sys
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
EXPERIMENT = "sketch-at-experiment-01"
RECORDED_PROBE = r"C:\Users\vresh\.codex\worktrees\52df\Leant2\scratch\next-sketch\at-probe\Probe.lean"
FROZEN = ("Probe.lean", "Controls.lean", "Probe.body.lean.in", "prepare.py", "provenance.json", "run_probe.py")
PINS = {
    "Probe.lean": "15af484e366bd054403c319c8b6a2ff4f2814ad727a81dda1010f3555b8c956e",
    "Controls.lean": "7803ea6cb985b6b5cc6949b558ff0f0359bdaf3f39c823178f7be986ce8bf8e3",
    "run_probe.py": "b4a78c52a9fbb9014cac2f799a486f7cf15fcf80962641e0b7da42d32ac5a61f",
    "source-replay/replay_carrier_sources.py.txt": "91a1f1c62aaec923660a64424ac087d81f7470f902d606ab744c0bdfcfeafdc2",
}
RUN_FILES = {"receipt.json", "inputs-before.json", "inputs-after.json", "source-provenance.json",
             "original-corpus-manifest.json"} | {
    f"{folder}/{name}" for folder in ("controls", "probe-5000", "probe-10000")
    for name in ("result.json", "stdout.bin", "stderr.bin")}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def metadata(data, size_key="bytes"):
    return {size_key: len(data), "sha256": digest(data)}


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bind_historical_envelope(runner):
    require(digest((HERE / "Probe.lean").read_bytes()) == PINS["Probe.lean"], "historical Probe bytes changed")
    original = runner.is_probe_transcript_envelope

    def check(message):
        recorded = message.get("fileName")
        if not isinstance(recorded, str) or PureWindowsPath(recorded) != PureWindowsPath(RECORDED_PROBE):
            return False
        # Keep the original severity, span, caption, and transcript checks.
        # Neither archived sources nor retained raw bytes are modified.
        return original({**message, "fileName": str(HERE / "Probe.lean")})

    runner.is_probe_transcript_envelope = check


def safe_relative(name):
    path = PurePosixPath(name)
    return (bool(name) and not path.is_absolute() and ".." not in path.parts and
            "." not in path.parts and "\\" not in name and ":" not in name and str(path) == name)


def verify_manifest():
    manifest = json.loads((HERE / "SHA256.json").read_bytes())
    actual = {p.relative_to(HERE).as_posix() for p in HERE.rglob("*")
              if p.is_file() and p != HERE / "SHA256.json" and "__pycache__" not in p.parts}
    require(actual == set(manifest["files"]), "bundle file inventory differs")
    for name, expected in manifest["files"].items():
        require(safe_relative(name), "unsafe bundle member")
        require(metadata((HERE / name).read_bytes()) == expected, "bundle hash mismatch: " + name)
    for name, expected in PINS.items():
        require(digest((HERE / name).read_bytes()) == expected, "frozen source pin differs: " + name)
    with zipfile.ZipFile(HERE / "evidence.zip") as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)), "duplicate ZIP member")
        require(set(names) == {EXPERIMENT + "/" + name for name in RUN_FILES}, "ZIP experiment inventory differs")
        require(set(names) == set(manifest["zip_members"]), "ZIP manifest inventory differs")
        for name in names:
            require(safe_relative(name), "unsafe ZIP member")
            # ZipFile.read independently checks each member's CRC as well.
            require(metadata(archive.read(name)) == manifest["zip_members"][name], "ZIP member hash mismatch: " + name)
    return manifest


def audit_experiment(read, runner, receipt_bytes=None):
    """Reclassify the retained bytes; read takes a ZIP-style relative name."""
    def get(path):
        return read(EXPERIMENT + "/" + path)

    provenance = json.loads((HERE / "provenance.json").read_bytes())
    require(provenance["source_case_id"] == "church_case_033" and provenance["operation"] == "at" and
            provenance["source_line"] == 270 and provenance["observation_count"] == 168 and
            len(provenance["observations"]) == len({r["id"] for r in provenance["observations"]}) == 168 and
            provenance["profile"] == "strictConstructive" and
            provenance["explicit_query_providers"] == ["BehaviorPartialNumeric.intCase"] and
            provenance["carrier"] == "Int → A" and provenance["open_holes_in_source_order"] == ["step", "init"] and
            provenance["hole_local_context"] == ["A : Type", "d : A"] and
            provenance["budgets_ms"] == [5000, 10000] and provenance["max_candidates"] == 1 and
            provenance["grace_ms"] == 0, "original query inventory changed")
    controls = provenance["control_declarations"]
    require(len(controls) == len(set(controls)) == 11, "control inventory differs")
    require(get("source-provenance.json") == (HERE / "provenance.json").read_bytes(), "source provenance bytes differ")
    corpus = get("original-corpus-manifest.json")
    require(digest(corpus) == provenance["manifest_sha256_bytes"] and
            json.loads(corpus)["source_sha256"] == provenance["source_sha256_normalized"], "corpus identity differs")
    receipt_bytes = receipt_bytes if receipt_bytes is not None else (HERE / (EXPERIMENT + ".receipt.json")).read_bytes()
    require(get("receipt.json") == receipt_bytes, "compact receipt differs from ZIP bytes")
    receipt = json.loads(receipt_bytes)
    require(receipt["source_case_id"] == "church_case_033" and receipt["observation_count"] == 168 and
            receipt["experiment_valid"] is True and receipt["inputs_unchanged"] is True and
            receipt["all_budgets_accepted"] is True and receipt["status"] == "accepted_both_budgets" and
            receipt["exit_code"] == 0 and receipt["failures"] == [] and receipt["skipped_budgets_ms"] == [] and
            receipt["budgets_ms"] == [5000, 10000] and len(receipt["probes"]) == 2 and
            receipt["build_performed"] is False and receipt["source_mutation_performed"] is False and
            receipt["environment_values_persisted"] is False, "invalid/incomplete experiment")
    require(receipt["original_church_sha256_normalized"] == provenance["source_sha256_normalized"] and
            receipt["original_spec_sha256"] == provenance["spec_sha256_bytes"], "receipt source identity differs")
    before, after = [json.loads(get("inputs-" + side + ".json")) for side in ("before", "after")]
    require(before == after, "experiment input drift")
    require(set(before["frozen_probe_files"]) == set(FROZEN), "frozen file inventory differs")
    for name in FROZEN:
        require(before["frozen_probe_files"][name] == metadata((HERE / name).read_bytes(), "size_bytes"),
                "frozen input differs: " + name)
    source_state = json.loads((HERE / "source-state.json").read_bytes())
    require(source_state["recorded_sources_equal_working_tree_at_packaging"] is True and
            source_state["recorded_source_files"] == before["source_files"], "source-state inventory differs")
    for path, expected in ((provenance["spec_path"], provenance["spec_sha256_bytes"]),
                           (str(PureWindowsPath(provenance["spec_path"]).with_name("manifest.json")), digest(corpus))):
        found = [entry for key, entry in before["original_provenance_files"].items()
                 if PureWindowsPath(key) == PureWindowsPath(path)]
        require(len(found) == 1 and found[0]["sha256"] == expected, "original input fingerprint differs")
    results, programs, printed_types = [], [], []
    stdout_bytes = 0
    stages = [("controls", receipt["controls"], None)] + [
        (f"probe-{budget}", result, budget) for budget, result in zip((5000, 10000), receipt["probes"])]
    for folder, recorded, budget in stages:
        require(recorded == json.loads(get(folder + "/result.json")), "per-process receipt differs")
        require(type(recorded["returncode"]) is int and recorded["returncode"] == 0 and
                not any(recorded[key] for key in ("timed_out", "interrupted", "launch_error")) and
                recorded["cleanup"] is None and recorded["process_timeout_seconds"] == 120 and
                type(recorded["process_elapsed_ms"]) is int and recorded["process_elapsed_ms"] >= 0,
                "native process metadata differs")
        source = "Controls.lean" if budget is None else "Probe.lean"
        require(recorded["source_sha256_before"] == recorded["source_sha256_after"] ==
                digest((HERE / source).read_bytes()), "per-process source differs")
        require(recorded["lean_sha256_before"] == recorded["lean_sha256_after"] ==
                before["lean_executable"]["sha256"], "per-process Lean executable differs")
        require(recorded["command"] == [before["lean_executable"]["path"], "--json",
                str(PureWindowsPath(RECORDED_PROBE).with_name(source))], "native command differs")
        raw = {key: recorded[key] for key in ("returncode", "timed_out", "interrupted", "launch_error")}
        for channel in ("stdout", "stderr"):
            path = folder + "/" + channel + ".bin"
            data = get(path)
            require(recorded[channel] == {"file": path, **metadata(data)}, "raw byte/hash mismatch: " + path)
            raw[channel] = data
        stdout_bytes += len(raw["stdout"])
        classified = runner.classify(raw, controls=controls if budget is None else None, budget=budget)
        require(classified["classification"] == ("controls_passed" if budget is None else "accepted") and
                not classified["problems"], "raw classification failed: " + folder)
        for key, value in classified.items():
            require(recorded[key] == value, "stored classification differs: " + key)
        if budget is not None:
            require(recorded["budget_ms"] == budget, "budget differs")
            message = json.loads(raw["stdout"])
            _, blocks, errors = runner.parse_output(message["data"])
            require(not errors, "unexpected transcript content")
            grouped = dict(blocks)
            require(grouped["PROBE_PROGRAM_CONSTANTS"] == "[Int, BehaviorPartialNumeric.intCase]" and
                    grouped["PROBE_PROGRAM_DEPENDENCIES_REVIEWED"] == "135", "program inventory differs")
            programs.append(grouped["PROBE_PROGRAM"])
            printed_types.append(grouped["PROBE_PROGRAM_TYPE"])
            results.append({"budget_ms": budget, "process_elapsed_ms": recorded["process_elapsed_ms"],
                **{key: classified[key] for key in ("classification", "actual_outcome", "api_elapsed_ms", "ledger")}})
    require(len(programs) == 2 and programs[0] == programs[1] and printed_types[0] == printed_types[1],
            "accepted printed outputs differ across budgets")
    return {"experiment": EXPERIMENT, "source_case_id": "church_case_033", "observation_count": 168,
        "created_utc": receipt["created_utc"], "completed_utc": receipt["completed_utc"],
        "status": receipt["status"], "experiment_valid": True, "inputs_unchanged": True,
        "native_processes": 3, "controls_axiom_free": 11, "synthesis_queries": 2,
        "raw_stream_files": 6, "stdout_bytes": stdout_bytes, "empty_stderr_files": 3,
        "runs": results, "candidate": programs[0], "candidate_utf8_sha256": digest(programs[0].encode()),
        "program_type": printed_types[0], "direct_program_constants": ["Int", "BehaviorPartialNumeric.intCase"],
        "transitive_program_dependencies_reviewed": 135, "same_printed_candidate_across_budgets": True,
        "fingerprint_counts": {key: len(before[key]) for key in ("source_files", "local_module_files",
            "toolchain_module_files", "toolchain_native_files", "frozen_probe_files", "original_provenance_files")}}


def audit_source_replay(query_audit, runner, read=None):
    """Reconstruct the separate at source; the shared receipt's foldr1 row is context only."""
    read = read if read is not None else lambda name: (HERE / "source-replay" / name).read_bytes()
    receipt = json.loads(read("receipt.json"))
    require(receipt["reference_implementation_imported"] is False and receipt["synthesis_imported"] is False and
            receipt["generator_sha256"] == digest(read("replay_carrier_sources.py.txt")), "replay generator/scope differs")
    rows = [row for row in receipt["runs"] if row["operation"] == "at"]
    require(len(rows) == 1, "replay must contain exactly one at row")
    row = rows[0]
    require(row["observation_count"] == 168 and row["origin_experiment"] == EXPERIMENT and
            row["origin_budgets_ms"] == [5000, 10000] and row["same_printed_target_and_program"] is True and
            row["passed"] is True and row["source"] == "at.lean", "replay origin/outcome differs")
    original = (HERE / "Probe.lean").read_text(encoding="utf-8")
    require(original.count("\nnamespace AtCarrierProbe\n") == 1, "ambiguous replay prefix")
    prefix = original.split("\nnamespace AtCarrierProbe\n", 1)[0]
    require(prefix.count("import Leant2.Frontend.Sketch.Run") == 1, "unexpected source imports")
    prefix = prefix.replace("import Leant2.Frontend.Sketch.Run", "import Lean", 1)
    prefix = re.sub(r"\n/-!.*?-/\n", "\n", prefix, count=1, flags=re.S)
    expected = prefix + f'''

/- Actual printed target and program from both accepted budget runs. The checker
above is copied from the unchanged original probe; no synthesis engine or
reference implementation is imported. -/
set_option maxHeartbeats 0
namespace ActualCarrierReplay
def program : {query_audit["program_type"]} :=
  {query_audit["candidate"]}
theorem originalContract : BehaviorPartial.check_at program = true := by decide
#print axioms program
#print axioms originalContract
#eval do
  if BehaviorPartial.check_at program then
    IO.println "ALL_168_ORIGINAL_OBSERVATIONS_EXECUTED_TRUE"
  else
    throw (IO.userError "actual printed program failed compiled original observations")
end ActualCarrierReplay
'''
    source = read("at.lean")
    require(source == expected.encode("utf-8"), "replay source differs from actual printed target/program or original checker")
    require(re.findall(r"^import (.+)$", expected, re.M) == ["Lean"] and
            "namespace BehaviorPartialOracle" not in expected and "namespace BehaviorPartialControl" not in expected,
            "replay imported synthesis or oracle declarations")
    process = row["process"]
    recorded_source = str(PureWindowsPath(RECORDED_PROBE).parents[3] /
        "baseline-out/sketch-carrier-source-replay-01/at.lean")
    require(type(process["returncode"]) is int and process["returncode"] == 0 and
            not any(process[key] for key in ("timed_out", "interrupted", "launch_error")) and
            process["cleanup"] is None and process["process_timeout_seconds"] == 120 and
            process["source_sha256_before"] == process["source_sha256_after"] == digest(source), "replay native/source failure")
    query_receipt = json.loads((HERE / (EXPERIMENT + ".receipt.json")).read_bytes())
    query_process = query_receipt["probes"][0]
    require(process["lean_sha256_before"] == process["lean_sha256_after"] == query_process["lean_sha256_before"] and
            process["command"] == [query_process["command"][0], "--json", recorded_source], "replay executable/command differs")
    raw = {}
    for channel in ("stdout", "stderr"):
        filename = "at/" + channel + ".bin"
        data = read(filename)
        require(process[channel] == {"file": filename, **metadata(data)}, "replay raw hash mismatch")
        raw[channel] = data
    require(not raw["stderr"], "replay stderr is not empty")
    messages, blocks, problems = runner.parse_output(raw["stdout"].decode("utf-8"))
    require(not blocks and not problems and len(messages) == 3 and messages == row["diagnostics"] and
            row["parser_problems"] == [], "replay diagnostic inventory differs")
    desired = [("#print axioms program", "'ActualCarrierReplay.program' does not depend on any axioms", 6),
        ("#print axioms originalContract", "'ActualCarrierReplay.originalContract' does not depend on any axioms", 6),
        ("#eval do", "ALL_168_ORIGINAL_OBSERVATIONS_EXECUTED_TRUE\n", 5)]
    lines = expected.splitlines()
    for message, (command, data, column) in zip(messages, desired):
        require(lines.count(command) == 1, "ambiguous replay diagnostic source")
        line = lines.index(command) + 1
        require(message["severity"] == "information" and message["data"] == data and
                message.get("caption", "") == "" and PureWindowsPath(message["fileName"]) == PureWindowsPath(recorded_source) and
                message["pos"] == {"line": line, "column": 0} and
                message["endPos"] == {"line": line, "column": column}, "replay diagnostic/source binding differs")
    return {"operation": "at", "origin_experiment": EXPERIMENT, "observation_count": 168,
        "origin_budgets_ms": [5000, 10000], "same_printed_target_and_program": True,
        "source_reconstructed_from_original_raw_outputs": True, "imports": ["Lean"],
        "native_processes": 1, "process_elapsed_ms": process["process_elapsed_ms"],
        "axiom_free_audits": 2, "compiled_original_observations_executed_true": 168,
        "source_sha256": digest(source), "stdout_bytes": len(raw["stdout"]), "stderr_bytes": 0,
        "other_operation_in_shared_receipt": "context only; not audited by this bundle"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-reference", action="store_true",
                        help="also reconstruct frozen generated bytes from the external C:/Leant specification")
    args = parser.parse_args()
    verify_manifest()
    runner = load_module("archived_at_classifier", HERE / "run_probe.py")
    bind_historical_envelope(runner)
    with zipfile.ZipFile(HERE / "evidence.zip") as archive:
        actual = audit_experiment(archive.read, runner)
    require(actual == json.loads((HERE / "audit.json").read_bytes()), "audit summary differs from raw evidence")
    replay = audit_source_replay(actual, runner)
    require(replay == json.loads((HERE / "replay-audit.json").read_bytes()), "replay audit summary differs")
    if args.check_reference:
        runner.original_provenance()
    print("PASS: exact bundle/ZIP hashes and CRCs, 11 control audits, both accepted raw queries, receipts and snapshots, actual-source Lean-only replay" +
          (", authoritative source regeneration" if args.check_reference else ""))


if __name__ == "__main__":
    main()
