"""Pure replay-audit regressions. No native tool is started."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("foldr1_replay_test_audit", HERE / "verify_bundle.py")
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class ReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.origin, cls.runner = AUDIT.load_origin()
        cls.recorded = {p.relative_to(HERE).as_posix(): p.read_bytes() for p in HERE.rglob("*")
                        if p.is_file() and "__pycache__" not in p.parts}

    def audit(self, data=None, origin=None):
        data = self.recorded if data is None else data
        return AUDIT.audit_replay(self.origin if origin is None else origin, self.runner, data.__getitem__)

    def change_row(self, data, change):
        receipt = json.loads(data["receipt.json"])
        change(next(r for r in receipt["runs"] if r["operation"] == "foldr1"))
        data["receipt.json"] = json.dumps(receipt).encode()

    def change_messages(self, data, change):
        messages = [json.loads(line) for line in data["foldr1/stdout.bin"].splitlines()]
        change(messages)
        data["foldr1/stdout.bin"] = ("\n".join(json.dumps(m) for m in messages) + "\n").encode()
        def update(row):
            row["diagnostics"] = messages
            row["process"]["stdout"] = {"file": "foldr1/stdout.bin", **AUDIT.metadata(data["foldr1/stdout.bin"])}
        self.change_row(data, update)

    def test_complete_manifest_and_actual_replay(self):
        AUDIT.verify_manifest()
        actual = self.audit()
        self.assertEqual(actual, json.loads((HERE / "audit.json").read_bytes()))
        self.assertEqual(actual["compiled_original_observations_executed_true"], 36)
        self.assertEqual(actual["imports"], ["Lean"])

    def test_actual_program_and_type_cannot_be_replaced(self):
        for field, value in (("program", "fun A d combine xs => d"), ("program_type", "Nat")):
            with self.subTest(field=field):
                changed = {**self.origin, field: value}
                with self.assertRaisesRegex(ValueError, "actual printed source"):
                    self.audit(origin=changed)

    def test_original_checker_and_import_cannot_be_replaced(self):
        for old, new in ((b"BehaviorPartial.check_foldr1", b"BehaviorPartial.changed_checker"),
                         (b"import Lean", b"import Leant2")):
            data = dict(self.recorded)
            data["foldr1.lean"] = data["foldr1.lean"].replace(old, new)
            with self.assertRaisesRegex(ValueError, "actual printed source"):
                self.audit(data)

    def test_raw_byte_change_fails(self):
        data = dict(self.recorded)
        data["foldr1/stdout.bin"] += b" "
        with self.assertRaisesRegex(ValueError, "raw byte/hash"):
            self.audit(data)

    def test_extra_or_missing_diagnostic_fails_even_when_rehashed(self):
        for change in (lambda m: m.append({"severity": "error", "data": "trailing error"}), lambda m: m.pop()):
            data = dict(self.recorded)
            self.change_messages(data, change)
            with self.assertRaisesRegex(ValueError, "diagnostic inventory"):
                self.audit(data)

    def test_exact_diagnostic_location_kind_and_payload(self):
        for change in ({"severity": "warning"}, {"caption": "other"}, {"fileName": "other.lean"},
                       {"pos": {"line": 37, "column": 0}}, {"endPos": {"line": 36, "column": 7}},
                       {"data": "'ActualCarrierReplay.program' depends on axioms: [sorryAx]"}):
            data = dict(self.recorded)
            self.change_messages(data, lambda m: m[0].update(change))
            with self.assertRaisesRegex(ValueError, "source/data binding"):
                self.audit(data)

    def test_compiled_execution_marker_must_be_exact(self):
        data = dict(self.recorded)
        self.change_messages(data, lambda m: m[2].update(data="ALL_35_ORIGINAL_OBSERVATIONS_EXECUTED_TRUE\n"))
        with self.assertRaisesRegex(ValueError, "source/data binding"):
            self.audit(data)

    def test_native_failure_cannot_keep_green_receipt(self):
        for key, value in (("returncode", 1), ("timed_out", True), ("interrupted", True), ("launch_error", True)):
            data = dict(self.recorded)
            self.change_row(data, lambda row: row["process"].__setitem__(key, value))
            with self.assertRaisesRegex(ValueError, "native process failed"):
                self.audit(data)

    def test_source_runtime_and_command_are_bound(self):
        for key, value, error in (("source_sha256_after", "0" * 64, "source hash"),
                                  ("lean_sha256_before", "0" * 64, "executable hash"),
                                  ("command", ["unrelated.exe"], "native command")):
            data = dict(self.recorded)
            self.change_row(data, lambda row: row["process"].__setitem__(key, value))
            with self.assertRaisesRegex(ValueError, error):
                self.audit(data)

    def test_stderr_cannot_be_hidden_by_rehash(self):
        data = dict(self.recorded)
        data["foldr1/stderr.bin"] = b"unexpected stderr"
        self.change_row(data, lambda row: row["process"].__setitem__("stderr",
            {"file": "foldr1/stderr.bin", **AUDIT.metadata(data["foldr1/stderr.bin"])}))
        with self.assertRaisesRegex(ValueError, "stderr is not empty"):
            self.audit(data)

    def test_duplicate_foldr1_row_fails(self):
        data = dict(self.recorded)
        receipt = json.loads(data["receipt.json"])
        receipt["runs"].append(copy.deepcopy(receipt["runs"][0]))
        data["receipt.json"] = json.dumps(receipt).encode()
        with self.assertRaisesRegex(ValueError, "exactly one foldr1"):
            self.audit(data)

    def test_at_row_is_context_only(self):
        data = dict(self.recorded)
        receipt = json.loads(data["receipt.json"])
        receipt["runs"] = [r for r in receipt["runs"] if r["operation"] == "foldr1"]
        receipt["success"] = False
        data["receipt.json"] = json.dumps(receipt).encode()
        self.assertEqual(self.audit(data), self.audit())


if __name__ == "__main__":
    unittest.main()
