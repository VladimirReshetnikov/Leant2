"""Pure bundle tests, including all unchanged frozen classifier tests."""
import copy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
import zipfile

sys.dont_write_bytecode = True
import verify_bundle as audit

FROZEN_TESTS = audit.load_module("original_classifier_tests", audit.HERE / "test_run_probe.py")
audit.bind_historical_envelope(FROZEN_TESTS.RUNNER)


class BundleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with zipfile.ZipFile(audit.HERE / "evidence.zip") as archive:
            cls.entries = {name: archive.read(name) for name in archive.namelist()}
        cls.runner = audit.load_module("bundle_test_classifier", audit.HERE / "run_probe.py")
        audit.bind_historical_envelope(cls.runner)

    def test_complete_original_evidence(self):
        actual = audit.audit_experiments(self.entries.__getitem__, self.runner)
        self.assertEqual(actual, json.loads((audit.HERE / "audit.json").read_bytes()))

    def test_manifest(self):
        audit.verify_manifest()

    def test_complete_ablation(self):
        self.assertEqual(audit.audit_ablation(self.entries.__getitem__, self.runner),
                         json.loads((audit.HERE / "ablation-audit.json").read_bytes()))

    def test_reject_extra_probe_even_with_matching_receipt_copies(self):
        entries = self.entries.copy()
        path = "sketch-foldr1-experiment-03/receipt.json"
        receipt = json.loads(entries[path])
        receipt["probes"].append(copy.deepcopy(receipt["probes"][0]))
        entries[path] = json.dumps(receipt).encode()
        read_bytes = Path.read_bytes
        compact = audit.HERE / "sketch-foldr1-experiment-03.receipt.json"
        def matching_copy(path):
            return entries["sketch-foldr1-experiment-03/receipt.json"] if path == compact else read_bytes(path)
        with patch.object(Path, "read_bytes", matching_copy):
            with self.assertRaisesRegex(ValueError, "invalid/incomplete experiment"):
                audit.audit_experiments(entries.__getitem__, self.runner)

    def test_reject_raw_byte_change(self):
        entries = self.entries.copy()
        path = "sketch-foldr1-experiment-03/probe-5000/stdout.bin"
        entries[path] += b"\n"
        with self.assertRaisesRegex(ValueError, "raw byte/hash mismatch"):
            audit.audit_experiments(entries.__getitem__, self.runner)

    def test_reject_snapshot_change(self):
        entries = self.entries.copy()
        path = "sketch-foldr1-experiment-03/inputs-after.json"
        snapshot = json.loads(entries[path])
        snapshot["source_files"]["Leant2/Search/Core.lean"]["sha256"] = "0" * 64
        entries[path] = json.dumps(snapshot).encode()
        with self.assertRaisesRegex(ValueError, "input drift"):
            audit.audit_experiments(entries.__getitem__, self.runner)

    def test_reject_result_receipt_change(self):
        entries = self.entries.copy()
        path = "sketch-foldr1-experiment-03/probe-5000/result.json"
        result = json.loads(entries[path])
        result["ledger"]["rejected"] += 1
        entries[path] = json.dumps(result).encode()
        with self.assertRaisesRegex(ValueError, "process receipt mismatch"):
            audit.audit_experiments(entries.__getitem__, self.runner)

    def test_historical_binding_rejects_unrecorded_paths(self):
        message = json.loads(self.entries["sketch-foldr1-experiment-03/probe-5000/stdout.bin"])
        for path in (str(audit.HERE / "Probe.lean"), "Probe.lean", audit.RECORDED_PROBE + ".bad"):
            self.assertFalse(self.runner.is_probe_transcript_envelope({**message, "fileName": path}))

    def test_native_rerun_location_still_uses_bundle(self):
        runner = audit.load_module("unmodified_rerun_classifier", audit.HERE / "run_probe.py")
        message = json.loads(self.entries["sketch-foldr1-experiment-03/probe-5000/stdout.bin"])
        self.assertTrue(runner.is_probe_transcript_envelope({**message, "fileName": str(audit.HERE / "Probe.lean")}))
        self.assertEqual(runner.ROOT, audit.HERE.parents[2])


def load_tests(loader, tests, pattern):
    tests.addTests(loader.loadTestsFromModule(FROZEN_TESTS))
    return tests


if __name__ == "__main__":
    unittest.main()
