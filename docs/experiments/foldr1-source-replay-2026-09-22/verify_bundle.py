#!/usr/bin/env python3
"""Pure byte/source/diagnostic audit of the foldr1 replay only. Never runs Lean."""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import sys
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ORIGIN = HERE.parent / "sketch-projection-2026-09-22"
EXPERIMENT = "sketch-foldr1-experiment-03"
GENERATOR_SHA = "91a1f1c62aaec923660a64424ac087d81f7470f902d606ab744c0bdfcfeafdc2"
ORIGIN_PINS = {
    "SHA256.json": "5a9d1c0d4ea5e4cd877a43209d7e2f28c0d4f59bf6755eae8e0640db5d013d93",
    "verify_bundle.py": "07dd1a9e0bc9968b84ed31aa15373511dd85b499a0240d3cd33794baf1dfb160",
    "run_probe.py": "f99093a3fed8860c592b66a55e52cbd586d4526a452e9e9971271109be896222",
    "Probe.lean": "bfb979d865713392839c360436db316962f778fc277b2d95708fb332f3d0a304",
    "evidence.zip": "2cd669b7236ce1806aa2a47d4a0b1c40bc65bf584e5bdd9e69c72fba530f23a2",
}
RECORDED_SOURCE = r"C:\Users\vresh\.codex\worktrees\52df\Leant2\baseline-out\sketch-carrier-source-replay-01\foldr1.lean"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def metadata(data):
    return {"bytes": len(data), "sha256": digest(data)}


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verify_manifest():
    manifest = json.loads((HERE / "SHA256.json").read_bytes())
    files = {p.relative_to(HERE).as_posix() for p in HERE.rglob("*") if p.is_file()
             and p != HERE / "SHA256.json" and "__pycache__" not in p.parts}
    require(files == set(manifest["files"]), "bundle inventory differs")
    for name, expected in manifest["files"].items():
        path = PurePosixPath(name)
        require(name and not path.is_absolute() and ".." not in path.parts and
                ":" not in name and "\\" not in name and str(path) == name, "unsafe bundle path")
        require(metadata((HERE / name).read_bytes()) == expected, "bundle hash differs: " + name)
    require(manifest["origin_dependencies"] == ORIGIN_PINS, "dependency pin inventory differs")
    for name, expected in ORIGIN_PINS.items():
        require(digest((ORIGIN / name).read_bytes()) == expected, "sealed origin dependency differs: " + name)


def load_origin():
    """Re-audit the sealed bytes, then recover both exact printed target/program pairs."""
    for name, expected in ORIGIN_PINS.items():
        require(digest((ORIGIN / name).read_bytes()) == expected, "sealed origin dependency differs: " + name)
    auditor = load_module("sealed_projection_audit", ORIGIN / "verify_bundle.py")
    auditor.verify_manifest()
    runner = load_module("sealed_foldr1_classifier", ORIGIN / "run_probe.py")
    auditor.bind_historical_envelope(runner)
    with zipfile.ZipFile(ORIGIN / "evidence.zip") as archive:
        checked = auditor.audit_experiments(archive.read, runner)
        require(checked == json.loads((ORIGIN / "audit.json").read_bytes()), "origin audit summary differs")
        pairs = []
        for budget in (5000, 10000):
            envelope = json.loads(archive.read(f"{EXPERIMENT}/probe-{budget}/stdout.bin"))
            diagnostics, blocks, problems = runner.parse_output(envelope["data"])
            require(not diagnostics and not problems and len(dict(blocks)) == len(blocks), "origin transcript differs")
            values = dict(blocks)
            require(values["PROBE_ACCEPTED"] == "exact_type_and_all_36_observations_replayed", "origin acceptance differs")
            pairs.append((values["PROBE_PROGRAM_TYPE"], values["PROBE_PROGRAM"]))
        require(len(pairs) == 2 and pairs[0] == pairs[1], "printed target/program differs across budgets")
        receipt = json.loads(archive.read(EXPERIMENT + "/receipt.json"))
        runtime = json.loads(archive.read(EXPERIMENT + "/inputs-before.json"))["lean_executable"]
        require(all(p["lean_sha256_before"] == p["lean_sha256_after"] == runtime["sha256"]
                    for p in receipt["probes"]), "origin runtime differs")
    return {"program_type": pairs[0][0], "program": pairs[0][1],
            "prefix_source": (ORIGIN / "Probe.lean").read_text(encoding="utf-8"), "runtime": runtime}, runner


def reconstruct(origin):
    original = origin["prefix_source"]
    require(original.count("\nnamespace Foldr1CarrierProbe\n") == 1, "ambiguous frozen prefix")
    prefix = original.split("\nnamespace Foldr1CarrierProbe\n", 1)[0]
    require(prefix.count("import Leant2.Frontend.Sketch.Run") == 1, "frozen prefix import differs")
    prefix = prefix.replace("import Leant2.Frontend.Sketch.Run", "import Lean", 1)
    prefix = re.sub(r"\n/-!.*?-/\n", "\n", prefix, count=1, flags=re.S)
    return prefix + f'''

/- Actual printed target and program from both accepted budget runs. The checker
above is copied from the unchanged original probe; no synthesis engine or
reference implementation is imported. -/
set_option maxHeartbeats 0
namespace ActualCarrierReplay
def program : {origin["program_type"]} :=
  {origin["program"]}
theorem originalContract : BehaviorPartial.check_foldr1 program = true := by decide
#print axioms program
#print axioms originalContract
#eval do
  if BehaviorPartial.check_foldr1 program then
    IO.println "ALL_36_ORIGINAL_OBSERVATIONS_EXECUTED_TRUE"
  else
    throw (IO.userError "actual printed program failed compiled original observations")
end ActualCarrierReplay
'''


def audit_replay(origin, runner, read=None):
    """Audit only the foldr1 row; other rows in the shared receipt are context."""
    read = read if read is not None else lambda name: (HERE / name).read_bytes()
    receipt = json.loads(read("receipt.json"))
    require(digest(read("replay_carrier_sources.py.txt")) == receipt["generator_sha256"] == GENERATOR_SHA,
            "generator hash differs")
    require(receipt["reference_implementation_imported"] is False and receipt["synthesis_imported"] is False,
            "replay scope differs")
    rows = [r for r in receipt["runs"] if r["operation"] == "foldr1"]
    require(len(rows) == 1, "expected exactly one foldr1 replay row")
    row = rows[0]
    require(row["observation_count"] == 36 and row["origin_experiment"] == EXPERIMENT and
            row["origin_budgets_ms"] == [5000, 10000] and row["same_printed_target_and_program"] is True and
            row["passed"] is True and row["source"] == "foldr1.lean", "replay origin/outcome differs")
    expected = reconstruct(origin)
    source = read("foldr1.lean")
    require(source == expected.encode("utf-8"), "replay differs from actual printed source and original checker")
    require(re.findall(r"^import (.+)$", expected, re.M) == ["Lean"] and
            "namespace BehaviorPartialOracle" not in expected and "namespace BehaviorPartialControl" not in expected,
            "replay imports synthesis or reference implementation")
    process = row["process"]
    require(type(process["returncode"]) is int and process["returncode"] == 0 and
            not any(process[k] for k in ("timed_out", "interrupted", "launch_error")) and
            process["cleanup"] is None and process["process_timeout_seconds"] == 120, "native process failed")
    require(process["source_sha256_before"] == process["source_sha256_after"] == digest(source), "source hash differs")
    require(process["lean_sha256_before"] == process["lean_sha256_after"] == origin["runtime"]["sha256"],
            "native executable hash differs")
    require(process["command"] == [origin["runtime"]["path"], "--json", RECORDED_SOURCE], "native command differs")
    raw = {}
    for channel in ("stdout", "stderr"):
        filename = "foldr1/" + channel + ".bin"
        data = read(filename)
        require(process[channel] == {"file": filename, **metadata(data)}, "raw byte/hash differs")
        raw[channel] = data
    require(not raw["stderr"], "native stderr is not empty")
    messages, blocks, problems = runner.parse_output(raw["stdout"].decode("utf-8"))
    require(not blocks and not problems and len(messages) == 3 and messages == row["diagnostics"] and
            row["parser_problems"] == [], "diagnostic inventory differs")
    desired = [("#print axioms program", "'ActualCarrierReplay.program' does not depend on any axioms", 6),
        ("#print axioms originalContract", "'ActualCarrierReplay.originalContract' does not depend on any axioms", 6),
        ("#eval do", "ALL_36_ORIGINAL_OBSERVATIONS_EXECUTED_TRUE\n", 5)]
    lines = expected.splitlines()
    for message, (command, data, column) in zip(messages, desired):
        require(lines.count(command) == 1, "ambiguous diagnostic source")
        line = lines.index(command) + 1
        require(message["severity"] == "information" and message["data"] == data and
                message.get("caption", "") == "" and PureWindowsPath(message["fileName"]) == PureWindowsPath(RECORDED_SOURCE) and
                message["pos"] == {"line": line, "column": 0} and
                message["endPos"] == {"line": line, "column": column}, "diagnostic source/data binding differs")
    return {"operation": "foldr1", "origin_experiment": EXPERIMENT, "origin_budgets_ms": [5000, 10000],
        "same_actual_printed_target_and_program": True, "source_reconstructed_from_both_accepted_raw_outputs": True,
        "imports": ["Lean"], "native_processes": 1, "process_elapsed_ms": process["process_elapsed_ms"],
        "axiom_free_audits": 2, "compiled_original_observations_executed_true": 36,
        "source_sha256": digest(source), "stdout_bytes": len(raw["stdout"]), "stderr_bytes": 0,
        "program_utf8_sha256": digest(origin["program"].encode()),
        "program_type_utf8_sha256": digest(origin["program_type"].encode()),
        "lean_executable_sha256": origin["runtime"]["sha256"],
        "other_operations_in_shared_receipt": "context only; not audited or claimed by this bundle"}


def main():
    verify_manifest()
    origin, runner = load_origin()
    actual = audit_replay(origin, runner)
    require(actual == json.loads((HERE / "audit.json").read_bytes()), "replay summary differs")
    print("PASS: sealed origin, both printed target/program pairs, exact reconstructed source, native hashes, three diagnostics; foldr1 only")


if __name__ == "__main__":
    main()
