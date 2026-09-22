"""Pure verification regressions against retained evidence; no native tools."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
import zipfile

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("at_bundle_verify_tests", HERE / "verify_bundle.py")
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)


class BundleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with zipfile.ZipFile(HERE / "evidence.zip") as archive:
            cls.recorded = {name: archive.read(name) for name in archive.namelist()}
        cls.runner = VERIFY.load_module("at_bundle_classifier_tests", HERE / "run_probe.py")
        VERIFY.bind_historical_envelope(cls.runner)
        cls.replay = {path.relative_to(HERE / "source-replay").as_posix(): path.read_bytes()
                      for path in (HERE / "source-replay").rglob("*") if path.is_file()}

    def audit(self, data=None):
        data = self.recorded if data is None else data
        return VERIFY.audit_experiment(data.__getitem__, self.runner,
            receipt_bytes=data[VERIFY.EXPERIMENT + "/receipt.json"])

    def change_receipt(self, data, change):
        key = VERIFY.EXPERIMENT + "/receipt.json"
        receipt = json.loads(data[key])
        change(receipt)
        data[key] = json.dumps(receipt).encode()

    def change_raw(self, data, folder, change):
        prefix = VERIFY.EXPERIMENT + "/" + folder
        key = prefix + "/stdout.bin"
        data[key] = change(data[key])
        process = json.loads(data[prefix + "/result.json"])
        process["stdout"] = {"file": folder + "/stdout.bin", **VERIFY.metadata(data[key])}
        data[prefix + "/result.json"] = json.dumps(process).encode()
        def replace(receipt):
            if folder == "controls":
                receipt["controls"] = process
            else:
                receipt["probes"][[5000, 10000].index(int(folder.removeprefix("probe-")))] = process
        self.change_receipt(data, replace)

    def test_complete_bundle_hashes_and_real_raw_classifications(self):
        VERIFY.verify_manifest()
        actual = self.audit()
        self.assertEqual(actual, json.loads((HERE / "audit.json").read_bytes()))
        self.assertEqual([row["classification"] for row in actual["runs"]], ["accepted", "accepted"])
        self.assertEqual(actual["controls_axiom_free"], 11)
        self.assertEqual(actual["stdout_bytes"], 7404)

    def test_surplus_or_missing_query_is_rejected_even_with_matching_copies(self):
        for extra in (True, False):
            data = dict(self.recorded)
            self.change_receipt(data, lambda r: r["probes"].append(r["probes"][0]) if extra else r["probes"].pop())
            with self.assertRaisesRegex(ValueError, "invalid/incomplete"):
                self.audit(data)

    def test_changed_raw_bytes_are_detected(self):
        data = dict(self.recorded)
        data[VERIFY.EXPERIMENT + "/probe-5000/stdout.bin"] += b" "
        with self.assertRaisesRegex(ValueError, "raw byte/hash"):
            self.audit(data)

    def test_candidate_plus_error_cannot_keep_stale_green_receipt(self):
        data = dict(self.recorded)
        self.change_raw(data, "probe-5000", lambda raw: raw +
            b'{"severity":"error","data":"synthetic trailing error"}\n')
        with self.assertRaisesRegex(ValueError, "raw classification failed"):
            self.audit(data)

    def test_healthy_bounded_miss_cannot_keep_stale_green_receipt(self):
        data = dict(self.recorded)
        def replace(raw):
            envelope = json.loads(raw)
            text = envelope["data"].split("PROBE_OUTCOME", 1)[0]
            text += ("PROBE_OUTCOME negative kind=Leant2.NegativeKind.budgetExhausted certificate=false\n"
                     "PROBE_LEDGER { ruleApplications := 533, unifications := 1736, proofAttempts := 239, candidates := 0, rejected := 237 }\n"
                     "PROBE_NOT_ACCEPTED inspect_negative_kind_and_certificate\n")
            envelope["data"] = text
            return (json.dumps(envelope) + "\n").encode()
        self.change_raw(data, "probe-5000", replace)
        with self.assertRaisesRegex(ValueError, "raw classification failed"):
            self.audit(data)

    def test_control_inventory_cannot_drop_one_audit(self):
        data = dict(self.recorded)
        self.change_raw(data, "controls", lambda raw: b"\n".join(raw.splitlines()[:-1]) + b"\n")
        with self.assertRaisesRegex(ValueError, "raw classification failed"):
            self.audit(data)

    def test_recorded_path_binding_is_narrow_and_keeps_span_checks(self):
        message = json.loads(self.recorded[VERIFY.EXPERIMENT + "/probe-5000/stdout.bin"])
        self.assertTrue(self.runner.is_probe_transcript_envelope(message))
        for change in ({"fileName": str(HERE / "Probe.lean")}, {"fileName": VERIFY.RECORDED_PROBE + ".bak"},
                       {"pos": {"line": 96, "column": 0}}, {"severity": "warning"}, {"caption": "other"}):
            self.assertFalse(self.runner.is_probe_transcript_envelope({**message, **change}))

    def test_snapshot_input_drift_is_rejected(self):
        data = dict(self.recorded)
        key = VERIFY.EXPERIMENT + "/inputs-after.json"
        snapshot = json.loads(data[key])
        snapshot["declared_toolchain"] = "different"
        data[key] = json.dumps(snapshot).encode()
        with self.assertRaisesRegex(ValueError, "input drift"):
            self.audit(data)

    def test_per_process_source_identity_and_command_are_bound(self):
        for field, value, error in (("source_sha256_after", "0" * 64, "per-process source"),
                                    ("command", ["unrelated.exe"], "native command")):
            data = dict(self.recorded)
            key = VERIFY.EXPERIMENT + "/probe-5000/result.json"
            process = json.loads(data[key])
            process[field] = value
            data[key] = json.dumps(process).encode()
            self.change_receipt(data, lambda r: r["probes"].__setitem__(0, process))
            with self.assertRaisesRegex(ValueError, error):
                self.audit(data)

    def test_source_pins_and_manifest_hashes_fail_after_local_file_change(self):
        with tempfile.TemporaryDirectory() as temporary:
            dest = Path(temporary) / "bundle"
            shutil.copytree(HERE, dest, ignore=shutil.ignore_patterns("__pycache__"))
            (dest / "Probe.lean").write_bytes((dest / "Probe.lean").read_bytes() + b"\n")
            with patch.object(VERIFY, "HERE", dest):
                with self.assertRaisesRegex(ValueError, "bundle hash mismatch"):
                    VERIFY.verify_manifest()
                with self.assertRaisesRegex(ValueError, "historical Probe bytes changed"):
                    VERIFY.bind_historical_envelope(self.runner)

    def test_missing_zip_member_fails_even_if_outer_hash_is_updated(self):
        with tempfile.TemporaryDirectory() as temporary:
            dest = Path(temporary) / "bundle"
            shutil.copytree(HERE, dest, ignore=shutil.ignore_patterns("__pycache__"))
            with zipfile.ZipFile(dest / "evidence.zip", "w") as archive:
                for name, data in self.recorded.items():
                    if not name.endswith("probe-10000/stderr.bin"):
                        archive.writestr(name, data)
            manifest = json.loads((dest / "SHA256.json").read_bytes())
            manifest["files"]["evidence.zip"] = VERIFY.metadata((dest / "evidence.zip").read_bytes())
            (dest / "SHA256.json").write_text(json.dumps(manifest), encoding="utf-8")
            with patch.object(VERIFY, "HERE", dest):
                with self.assertRaisesRegex(ValueError, "ZIP experiment inventory differs"):
                    VERIFY.verify_manifest()

    def test_relative_paths_do_not_allow_traversal_or_drives(self):
        for path in ("../outside", "/absolute", "C:/outside", "a\\b", "a//b", "a/./b"):
            self.assertFalse(VERIFY.safe_relative(path))
        self.assertTrue(VERIFY.safe_relative("probe-5000/stdout.bin"))

    def test_actual_printed_source_replay_is_independently_reconstructed(self):
        result = VERIFY.audit_source_replay(self.audit(), self.runner)
        self.assertEqual(result, json.loads((HERE / "replay-audit.json").read_bytes()))
        self.assertEqual(result["imports"], ["Lean"])
        self.assertEqual(result["compiled_original_observations_executed_true"], 168)
        self.assertEqual(result["native_processes"], 1)

    def test_replay_source_cannot_substitute_a_known_witness(self):
        data = dict(self.replay)
        data["at.lean"] = data["at.lean"].replace(b"def program :", b"def suppliedWitness :")
        with self.assertRaisesRegex(ValueError, "replay source differs"):
            VERIFY.audit_source_replay(self.audit(), self.runner, data.__getitem__)

    def test_replay_trailing_error_rejected_even_after_rehash(self):
        data = dict(self.replay)
        message = {"severity": "error", "data": "synthetic trailing error"}
        data["at/stdout.bin"] += (json.dumps(message) + "\n").encode()
        receipt = json.loads(data["receipt.json"])
        row = next(row for row in receipt["runs"] if row["operation"] == "at")
        row["process"]["stdout"] = {"file": "at/stdout.bin", **VERIFY.metadata(data["at/stdout.bin"])}
        row["diagnostics"].append(message)
        data["receipt.json"] = json.dumps(receipt).encode()
        with self.assertRaisesRegex(ValueError, "diagnostic inventory"):
            VERIFY.audit_source_replay(self.audit(), self.runner, data.__getitem__)

    def test_replay_cannot_be_attached_to_a_different_original_candidate(self):
        query = self.audit()
        query["candidate"] = "fun A d n xs => d"
        with self.assertRaisesRegex(ValueError, "replay source differs"):
            VERIFY.audit_source_replay(query, self.runner)


if __name__ == "__main__":
    unittest.main()
