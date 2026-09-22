#!/usr/bin/env python3
"""Read-only, pure-Python integrity and classification audit. Never starts Lean.

The original wrapper and its raw inputs are unchanged. Historical diagnostic
paths are bound to the byte-identical archived Probe only for classification;
the original wrapper continues to use its own HERE for fresh native reruns.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path, PureWindowsPath
import sys
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
RECORDED_PROBE = r"C:\Users\vresh\.codex\worktrees\52df\Leant2\scratch\next-sketch\foldr1-probe\Probe.lean"
PROBE_SHA = "bfb979d865713392839c360436db316962f778fc277b2d95708fb332f3d0a304"
FROZEN = ("Probe.lean", "Controls.lean", "Probe.body.lean.in", "prepare.py",
          "provenance.json", "run_probe.py")
EXPERIMENTS = ("sketch-foldr1-experiment-02", "sketch-foldr1-experiment-03")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bind_historical_envelope(runner):
    """Accept exactly the recorded old path, retaining every native span check."""
    require(digest((HERE / "Probe.lean").read_bytes()) == PROBE_SHA,
            "historical path cannot bind to a different source")
    original = runner.is_probe_transcript_envelope

    def check(message):
        path = message.get("fileName")
        if not isinstance(path, str) or PureWindowsPath(path) != PureWindowsPath(RECORDED_PROBE):
            return False
        # Only this ephemeral dictionary changes, never any source/raw bytes.
        return original({**message, "fileName": str(HERE / "Probe.lean")})

    runner.is_probe_transcript_envelope = check


def audit_experiments(read, runner):
    provenance = json.loads((HERE / "provenance.json").read_bytes())
    require(provenance["source_case_id"] == "church_case_039" and
            provenance["observation_count"] == 36 and
            len(provenance["observations"]) == 36 and
            len({row["id"] for row in provenance["observations"]}) == 36 and
            provenance["profile"] == "strictConstructive" and
            provenance["explicit_query_providers"] == [] and
            provenance["carrier"] == "Option A" and
            provenance["open_holes_in_source_order"] == ["step", "init", "finish"],
            "original query inventory changed")
    controls = provenance["control_declarations"] + runner.CONTROL_EXTRA
    require(len(controls) == len(set(controls)) == 11, "control inventory")
    snapshots, summaries, programs = {}, {}, []
    for name in EXPERIMENTS:
        def get(path):
            return read(name + "/" + path)
        receipt = json.loads(get("receipt.json"))
        require(get("receipt.json") == (HERE / (name + ".receipt.json")).read_bytes(),
                "compact receipt differs from original ZIP bytes")
        before, after = [json.loads(get("inputs-" + part + ".json")) for part in ("before", "after")]
        require(before == after and receipt["inputs_unchanged"] is True, "experiment input drift")
        require(get("source-provenance.json") == (HERE / "provenance.json").read_bytes(),
                "original source provenance differs")
        for filename in FROZEN:
            require(before["frozen_probe_files"][filename] == {
                "size_bytes": (HERE / filename).stat().st_size,
                "sha256": digest((HERE / filename).read_bytes())}, "frozen input mismatch: " + filename)
        require(receipt["experiment_valid"] is True and not receipt["failures"] and len(receipt["probes"]) == 2 and
                receipt["budgets_ms"] == [5000, 10000] and receipt["skipped_budgets_ms"] == [],
                "invalid/incomplete experiment")
        require(receipt["source_case_id"] == "church_case_039" and receipt["observation_count"] == 36 and
                receipt["original_spec_sha256"] == provenance["spec_sha256_bytes"] and
                receipt["original_church_sha256_normalized"] == provenance["source_sha256_normalized"],
                "receipt corpus identity differs")
        corpus_bytes = get("original-corpus-manifest.json")
        corpus_paths = [v for p, v in before["original_provenance_files"].items()
                        if PureWindowsPath(p).name == "manifest.json"]
        require(corpus_paths == [{"size_bytes": len(corpus_bytes), "sha256": digest(corpus_bytes)}],
                "original corpus manifest bytes differ from snapshot")
        results = []
        for folder, expected, budget in [("controls", receipt["controls"], None)] + [
                ("probe-" + str(b), result, b) for b, result in zip((5000, 10000), receipt["probes"])]:
            recorded = json.loads(get(folder + "/result.json"))
            require(recorded == expected, "process receipt mismatch")
            require(recorded["returncode"] == 0 and not any(recorded[k] for k in
                    ("timed_out", "interrupted", "launch_error")), "native failure")
            source = "Controls.lean" if budget is None else "Probe.lean"
            source_sha = digest((HERE / source).read_bytes())
            require(recorded["source_sha256_before"] == recorded["source_sha256_after"] == source_sha,
                    "per-process source mismatch")
            require(recorded["lean_sha256_before"] == recorded["lean_sha256_after"] ==
                    before["lean_executable"]["sha256"], "per-process native executable mismatch")
            require(recorded["command"] == [before["lean_executable"]["path"], "--json",
                    str(PureWindowsPath(RECORDED_PROBE).with_name(source))], "unexpected native command")
            raw = {k: recorded[k] for k in ("returncode", "timed_out", "interrupted", "launch_error")}
            for channel in ("stdout", "stderr"):
                path = folder + "/" + channel + ".bin"
                data = get(path)
                require(recorded[channel] == {"file": path, "bytes": len(data), "sha256": digest(data)},
                        "raw byte/hash mismatch: " + path)
                raw[channel] = data
            classified = runner.classify(raw, controls=controls if budget is None else None, budget=budget)
            require(classified["classification"] != "failure" and not classified["problems"],
                    "raw reclassification failed: " + name + "/" + folder)
            for key, value in classified.items():
                require(recorded[key] == value, "stored classification differs: " + key)
            if budget is not None:
                require(recorded["budget_ms"] == budget, "budget mismatch")
                message = json.loads(raw["stdout"])
                _, blocks, errors = runner.parse_output(message["data"])
                require(not errors, "unexpected transcript content")
                grouped = dict(blocks)
                if classified["classification"] == "accepted":
                    require(grouped["PROBE_PROGRAM_CONSTANTS"] ==
                            "[Option, Option.some, Option.casesOn, Option.none]" and
                            grouped["PROBE_PROGRAM_DEPENDENCIES_REVIEWED"] == "5",
                            "native program dependency inventory differs")
                    programs.append(grouped["PROBE_PROGRAM"])
                results.append({"budget_ms": budget, "process_elapsed_ms": recorded["process_elapsed_ms"],
                    **{k: classified[k] for k in ("classification", "actual_outcome", "api_elapsed_ms", "ledger")}})
        desired = "bounded_miss" if name.endswith("02") else "accepted"
        require(len(results) == 2 and all(r["classification"] == desired for r in results),
                "unexpected experiment outcomes")
        require(receipt["exit_code"] == (2 if desired == "bounded_miss" else 0) and
                receipt["all_budgets_accepted"] == (desired == "accepted") and
                receipt["status"] == ("bounded_miss" if desired == "bounded_miss" else "accepted_both_budgets"),
                "top-level receipt outcome mismatch")
        snapshots[name] = before
        summaries[name] = {"created_utc": receipt["created_utc"], "completed_utc": receipt["completed_utc"],
            "status": receipt["status"], "experiment_valid": True, "inputs_unchanged": True,
            "controls_axiom_free": 11, "runs": results,
            "fingerprint_counts": {k: len(before[k]) for k in ("source_files", "local_module_files",
                "toolchain_module_files", "toolchain_native_files", "frozen_probe_files", "original_provenance_files")}}
    old, new = [snapshots[n] for n in EXPERIMENTS]
    for key in ("declared_toolchain", "lean_executable", "toolchain_module_files", "toolchain_native_files",
                "frozen_probe_files", "original_provenance_files"):
        require(old[key] == new[key], "cross-experiment drift outside implementation: " + key)
    require(read(EXPERIMENTS[0] + "/controls/stdout.bin") == read(EXPERIMENTS[1] + "/controls/stdout.bin"),
            "control audit raw outputs differ")
    require(read(EXPERIMENTS[0] + "/original-corpus-manifest.json") ==
            read(EXPERIMENTS[1] + "/original-corpus-manifest.json"), "corpus manifests differ")
    require(len(programs) == 2 and programs[0] == programs[1], "printed candidates differ across budgets")
    changed_sources = {name: {"before": old["source_files"].get(name), "after": new["source_files"].get(name)}
        for name in sorted(old["source_files"].keys() | new["source_files"].keys())
        if old["source_files"].get(name) != new["source_files"].get(name)}
    changed_modules = sum(old["local_module_files"].get(name) != new["local_module_files"].get(name)
        for name in old["local_module_files"].keys() | new["local_module_files"].keys())
    return {"experiments": summaries, "same_frozen_query_provenance_and_toolchain": True,
        "same_printed_candidate_across_accepted_budgets": True,
        "candidate": programs[0], "candidate_utf8_sha256": digest(programs[0].encode()),
        "changed_source_files": changed_sources, "changed_local_module_artifact_count": changed_modules}


def verify_manifest():
    manifest = json.loads((HERE / "SHA256.json").read_bytes())
    actual = {p.relative_to(HERE).as_posix() for p in HERE.rglob("*") if p.is_file()
              and p.name != "SHA256.json" and "__pycache__" not in p.parts}
    require(actual == set(manifest["files"]), "bundle file inventory differs")
    for name, expected in manifest["files"].items():
        data = (HERE / name).read_bytes()
        require(expected == {"bytes": len(data), "sha256": digest(data)}, "bundle hash mismatch: " + name)
    with zipfile.ZipFile(HERE / "evidence.zip") as archive:
        require(len(archive.namelist()) == len(set(archive.namelist())), "duplicate ZIP member")
        require(set(archive.namelist()) == set(manifest["zip_members"]), "ZIP inventory differs")
        for name, expected in manifest["zip_members"].items():
            data = archive.read(name)
            require(expected == {"bytes": len(data), "sha256": digest(data)}, "ZIP member hash mismatch: " + name)
    return manifest


def audit_ablation(read, runner):
    name = "sketch-foldr1-ablation-01"
    def get(path):
        return read(name + "/" + path)
    receipt = json.loads(get("receipt.json"))
    require(get("receipt.json") == (HERE / (name + ".receipt.json")).read_bytes(), "ablation receipt bytes differ")
    baseline = json.loads(read(EXPERIMENTS[1] + "/inputs-before.json"))
    before, after = [json.loads(get("inputs-" + side + ".json")) for side in ("before", "after")]
    require(before == after and receipt["inputs_unchanged"] is True, "ablation input drift")
    require(before.keys() == baseline.keys(), "ablation fingerprint categories changed")
    for key in before:
        if key != "frozen_probe_files":
            require(before[key] == baseline[key], "ablation changed native input category: " + key)
    require(before["frozen_probe_files"].keys() == set(FROZEN) | {"run_ablation.py", "prepare_ablation.py"},
            "ablation controller inventory differs")
    for filename, recorded in before["frozen_probe_files"].items():
        data = (HERE / filename).read_bytes()
        require(recorded == {"size_bytes": len(data), "sha256": digest(data)}, "ablation source hash mismatch")
    for filename in FROZEN:
        require(before["frozen_probe_files"][filename] == baseline["frozen_probe_files"][filename],
                "ablation changed frozen query/controller")
    require(get("source-provenance.json") == (HERE / "provenance.json").read_bytes() and
            get("original-corpus-manifest.json") == read(EXPERIMENTS[1] + "/original-corpus-manifest.json"),
            "ablation corpus provenance changed")
    expected = (HERE / "run_probe.py").read_text(encoding="utf-8")
    changes = [
        ('command = [str(lean), "--json", str(source)]',
         'command = [str(lean), *(["-Dleant2.skipRules=sketchProjection"] if budget is not None else []), "--json", str(source)]'),
        ('"provenance.json", "prepare.py", "run_probe.py")]',
         '"provenance.json", "prepare.py", "run_probe.py", "run_ablation.py", "prepare_ablation.py")]'),
        ('"source_mutation_performed": False,',
         '"source_mutation_performed": False,\n        "ablation": "projection disabled in native probe only",\n        "native_probe_options": ["-Dleant2.skipRules=sketchProjection"],'),
    ]
    for old, new in changes:
        require(expected.count(old) == 1, "ablation derivation anchor changed")
        expected = expected.replace(old, new)
    require(expected == (HERE / "run_ablation.py").read_text(encoding="utf-8"), "unexpected ablation runner changes")
    require(receipt["experiment_valid"] is True and not receipt["failures"] and
            receipt["status"] == "bounded_miss" and receipt["exit_code"] == 2 and
            receipt["all_budgets_accepted"] is False and receipt["budgets_ms"] == [5000, 10000] and
            receipt["skipped_budgets_ms"] == [] and len(receipt["probes"]) == 2 and
            receipt["native_probe_options"] == ["-Dleant2.skipRules=sketchProjection"], "ablation outcome differs")
    provenance = json.loads((HERE / "provenance.json").read_bytes())
    controls = provenance["control_declarations"] + runner.CONTROL_EXTRA
    results = []
    for folder, recorded, budget in [("controls", receipt["controls"], None)] + [
            ("probe-" + str(b), r, b) for b, r in zip((5000, 10000), receipt["probes"])]:
        require(recorded == json.loads(get(folder + "/result.json")), "ablation process receipt differs")
        source = "Controls.lean" if budget is None else "Probe.lean"
        require(recorded["source_sha256_before"] == recorded["source_sha256_after"] ==
                digest((HERE / source).read_bytes()), "ablation process source changed")
        require(recorded["lean_sha256_before"] == recorded["lean_sha256_after"] ==
                before["lean_executable"]["sha256"], "ablation process executable changed")
        options = [] if budget is None else ["-Dleant2.skipRules=sketchProjection"]
        require(recorded["command"] == [before["lean_executable"]["path"], *options, "--json",
                str(PureWindowsPath(RECORDED_PROBE).with_name(source))], "unexpected ablation native command")
        raw = {k: recorded[k] for k in ("returncode", "timed_out", "interrupted", "launch_error")}
        for channel in ("stdout", "stderr"):
            path = folder + "/" + channel + ".bin"
            data = get(path)
            require(recorded[channel] == {"file": path, "bytes": len(data), "sha256": digest(data)},
                    "ablation raw bytes differ")
            raw[channel] = data
        result = runner.classify(raw, controls=controls if budget is None else None, budget=budget)
        require(result["classification"] == ("controls_passed" if budget is None else "bounded_miss"),
                "ablation raw classification differs")
        for key, value in result.items():
            require(recorded[key] == value, "ablation recorded classifier differs")
        if budget is not None:
            require(recorded["budget_ms"] == budget, "ablation budget differs")
            results.append({"budget_ms": budget, "process_elapsed_ms": recorded["process_elapsed_ms"],
                **{k: result[k] for k in ("classification", "actual_outcome", "api_elapsed_ms", "ledger")}})
    require(get("controls/stdout.bin") == read(EXPERIMENTS[1] + "/controls/stdout.bin"),
            "ablation independent control audit differs")
    return {"status": receipt["status"], "inputs_unchanged": True, "experiment_valid": True,
        "same_source_modules_toolchain_query_as_accepted03": True,
        "only_native_probe_option": "-Dleant2.skipRules=sketchProjection", "runs": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-reference", action="store_true",
                        help="also verify the external C:/Leant corpus and regenerate query text in memory")
    args = parser.parse_args()
    verify_manifest()
    runner = load_module("archived_foldr1", HERE / "run_probe.py")
    require(runner.ROOT == HERE.parents[2], "rerun wrapper repository-root layout changed")
    bind_historical_envelope(runner)
    with zipfile.ZipFile(HERE / "evidence.zip") as archive:
        actual = audit_experiments(archive.read, runner)
        ablation = audit_ablation(archive.read, runner)
    require(actual == json.loads((HERE / "audit.json").read_bytes()), "audit summary differs from raw evidence")
    require(ablation == json.loads((HERE / "ablation-audit.json").read_bytes()), "ablation summary differs")
    if args.check_reference:
        provenance, spec, _, _, _ = runner.original_provenance()
        sys.path.insert(0, str(spec.parent))
        reference = load_module("frozen_behavior_spec", spec)
        require(reference.LEAN_TYPES["foldr1"] == provenance["exact_established_defaulted_lean_type"] and
                reference.lean_predicate("foldr1", "f") == provenance["exact_contract"] and
                reference.FIXTURES["foldr1"] == provenance["observations"] and
                reference.search_provider_inventory("foldr1") == provenance["original_provider_inventory"],
                "authoritative corpus query differs")
        text = (HERE / "Probe.body.lean.in").read_text(encoding="utf-8")
        text = text.replace("@@PRELUDE@@", "\n".join(reference.lean_prelude(["foldr1"]))).replace(
            "@@TARGET@@", reference.LEAN_TYPES["foldr1"]).replace(
            "@@CONTRACT@@", reference.lean_predicate("foldr1", "f"))
        require(text.encode() == (HERE / "Probe.lean").read_bytes(), "in-memory query regeneration differs")
    print("PASS: bundle hashes, original raw classifications, receipts, snapshots, candidate equality" +
          (", authoritative corpus/query regeneration" if args.check_reference else ""))


if __name__ == "__main__":
    main()
