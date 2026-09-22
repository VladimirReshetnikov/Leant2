import contextlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import run_sketches as run


def message(data, severity="information", line=5):
    return {"data": data, "severity": severity, "pos": {"line": line, "column": 0}}


def output(messages):
    return "\n".join(json.dumps(m) for m in messages)


class SketchHarnessTests(unittest.TestCase):
    def setUp(self):
        self.cases = {c["id"]: c for c in run.load_cases()}

    def positive(self):
        case = self.cases["two-hole-fold"]
        return case, [message("providers: []", line=4),
            message("leant2 sketch: prepared 2 hole(s)"),
            message("leant2 sketch: 1 candidate(s) [rules 1, proofs 1]\n  it1  List.foldr Nat.add 1"),
            message(run.SOURCE_PREFIX + "List.foldr Nat.add 1"),
            message(run.FRONT.audit_marker(case), line=30), message(run.VALUE, line=25)]

    def audit(self, case, messages, code=0, stderr="", stage="original"):
        return run.classify(case, stage, output(messages), stderr, code, [5, 6, 7, 8])

    def test_exact_inventory_and_disjoint_counts(self):
        self.assertEqual(len(self.cases), 7)
        self.assertEqual(sum(1 + c["replay"] for c in self.cases.values()), 10)
        self.assertEqual(sum(c["expect"] == "candidate" for c in self.cases.values()), 3)
        self.assertEqual([self.cases[n]["holes"] for n in ("two-hole-fold", "lambda-identity", "zero-hole-correct")], [2, 1, 0])
        for case in self.cases.values():
            source, locations = run.source(case, 5000)
            query = source.split("#leant2_sketch", 1)[0]
            self.assertNotIn("def ", query)
            self.assertNotIn("reference-controls", source)
            self.assertEqual(locations, [5, 6, 7, 8])

    def test_candidate_with_error_nonzero_or_stderr_fails(self):
        case, messages = self.positive()
        self.assertTrue(self.audit(case, messages)["passed"])
        self.assertFalse(self.audit(case, messages + [message("late failure", "error")])["passed"])
        self.assertFalse(self.audit(case, messages, code=1)["passed"])
        self.assertFalse(self.audit(case, messages, stderr="native error")["passed"])

    def test_source_missing_duplicate_wrong_location_or_unsafe_fails(self):
        case, messages = self.positive()
        self.assertFalse(self.audit(case, messages[:3] + messages[4:])["passed"])
        self.assertFalse(self.audit(case, messages + [messages[3]])["passed"])
        for text, line in (("?step", 5), ("Leant2.hidden", 5), ("sorry", 5), ("0", 90)):
            copy = list(messages)
            copy[3] = message(run.SOURCE_PREFIX + text, line=line)
            self.assertFalse(self.audit(case, copy)["passed"])

    def test_exact_preparation_count_and_independent_checks_required(self):
        case, messages = self.positive()
        wrong = list(messages)
        wrong[1] = message("leant2 sketch: prepared 1 hole(s)")
        self.assertFalse(self.audit(case, wrong)["passed"])
        self.assertFalse(self.audit(case, messages[:-1])["passed"])
        self.assertFalse(self.audit(case, messages[:4] + messages[5:])["passed"])

    def test_false_silence_and_bounded_miss_are_not_certificates(self):
        case = self.cases["false-contract"]
        messages = [message("providers: []", line=4), message("leant2 sketch: prepared 2 hole(s)"), message(run.ABSENT)]
        self.assertFalse(self.audit(case, messages)["passed"])
        self.assertFalse(self.audit(case, messages + [message("leant2 sketch: budget exhausted")])["passed"])
        self.assertTrue(self.audit(case, messages + [message("leant2 sketch: provably no program satisfies the contract")])["passed"])

    def test_wrong_fixed_body_cannot_claim_global_impossibility(self):
        case = self.cases["zero-hole-wrong"]
        messages = [message("providers: []", line=4), message("leant2 sketch: prepared 0 hole(s)"), message(run.ABSENT)]
        self.assertTrue(self.audit(case, messages + [message("leant2 sketch: 1 program(s) of the type proposed, none passed the contract")])["passed"])
        self.assertFalse(self.audit(case, messages + [message("leant2 sketch: provably no program satisfies the contract")])["passed"])
        self.assertFalse(self.audit(case, messages[0:2] + [message("leant2 sketch: budget exhausted")])["passed"])

    def test_wrong_fixed_body_requires_an_actual_recorded_rejection(self):
        case = self.cases["zero-hole-wrong"]
        messages = [message("providers: []", line=4), message("leant2 sketch: prepared 0 hole(s)"), message(run.ABSENT)]
        for outcome in ("budget exhausted", "no term found within the search bounds",
                        "0 program(s) of the type proposed, none passed the contract"):
            with self.subTest(outcome=outcome):
                self.assertFalse(self.audit(case, messages + [message(run.OUTCOME_PREFIX + outcome)])["passed"])
        self.assertTrue(self.audit(case, messages + [message(run.OUTCOME_PREFIX +
            "2 program(s) of the type proposed, none passed the contract")])["passed"])

    def test_all_fresh_negative_sources_check_bare_and_numbered_aliases(self):
        negative_cases = [c for c in self.cases.values() if c["expect"] != "candidate"]
        self.assertEqual(len(negative_cases), 4)
        for case in negative_cases:
            with self.subTest(case=case["id"]):
                source, _ = run.source(case, 5000)
                self.assertIn("for name in [`it, `it1] do", source)
                self.assertIn("(Leant2.resultBinding? (← getEnv) name).isSome", source)
                self.assertIn("!(getAliases (← getEnv) name false).isEmpty", source)
                self.assertLess(source.index("throwError \"sketch negative retained"),
                                source.index(f'logInfo "{run.ABSENT}"'))

    def test_preflight_requires_exact_error_and_no_search_success(self):
        case = self.cases["duplicate-label"]
        messages = [message("providers: []", line=4), message(run.PREP_PREFIX + " duplicate label", "error"), message(run.ABSENT)]
        self.assertTrue(self.audit(case, messages, code=1)["passed"])
        self.assertFalse(self.audit(case, messages, code=0)["passed"])
        self.assertFalse(self.audit(case, [messages[0], message("unrelated parse error", "error"), messages[2]], code=1)["passed"])
        self.assertFalse(self.audit(case, messages + [message("leant2 sketch: prepared 0 hole(s)")], code=1)["passed"])

    def test_actual_multiline_source_is_preserved_in_lean_only_replay(self):
        case = self.cases["lambda-identity"]
        term = "fun (A : Type) =>\n  fun (value : A) => value"
        text, locations = run.source(case, 10000, term)
        self.assertEqual(re.findall(r"^import (.+)$", text, re.M), ["Lean"])
        self.assertIn("  " + term.replace("\n", "\n  ") + "\n", text)
        self.assertNotIn("#leant2_sketch", text)
        self.assertNotIn("it1", text)
        self.assertEqual(locations, [])
        messages = [message(run.FRONT.audit_marker(case)), message(run.VALUE)]
        self.assertTrue(self.audit(case, messages, stage="replay")["passed"])
        self.assertFalse(self.audit(case, messages + [message(run.SOURCE_PREFIX + term)], stage="replay")["passed"])

    def test_provider_reference_contamination_fails(self):
        case, messages = self.positive()
        messages[0] = message("providers: [offsetReference]", line=4)
        self.assertFalse(self.audit(case, messages)["passed"])

    def test_empty_fixture_inventory_cannot_produce_zero_case_success(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            (folder / "cases.json").write_text(
                json.dumps({"schema_version": 1, "cases": []}), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "invalid sketch fixture inventory"):
                run.load_cases(folder)

    @staticmethod
    def stage(name, **updates):
        return {"stage": name, "passed": True, "timed_out": False,
                "invalid_utf8": False, **updates}

    def test_case_requires_exact_complete_stage_inventory(self):
        case = self.cases["two-hole-fold"]
        original, replay = self.stage("original"), self.stage("replay")
        self.assertTrue(run.case_passed(case, [original, replay]))
        for stages in ([], [original], [replay, original], [original, replay, replay],
                       [original, self.stage("replay", passed=False)],
                       [original, self.stage("replay", timed_out=True)],
                       [original, self.stage("replay", invalid_utf8=True)]):
            with self.subTest(stages=stages):
                self.assertFalse(run.case_passed(case, stages))
        negative = self.cases["zero-hole-wrong"]
        self.assertTrue(run.case_passed(negative, [original]))
        self.assertFalse(run.case_passed(negative, [original, replay]))

    def test_process_flags_override_otherwise_valid_diagnostics(self):
        case, messages = self.positive()
        raw = {"stage": "original", "stdout": output(messages), "stderr": "", "returncode": 0,
               "timed_out": False, "invalid_utf8": False}
        for key in ("timed_out", "invalid_utf8"):
            with self.subTest(key=key), patch.object(run, "process", return_value={**raw, key: True}):
                result = run.run_stage(case, "original", "", [5, 6, 7, 8], None, None, {}, 1)
                self.assertFalse(result["passed"])
                self.assertIn(key, result["problems"])

    @staticmethod
    def reference(**updates):
        return {"stage": "references", "stdout": output([message('"SKETCH_REFERENCES_OK"')]),
                "stderr": "", "returncode": 0, "timed_out": False,
                "invalid_utf8": False, **updates}

    def test_reference_requires_clean_process_and_exact_completion(self):
        self.assertTrue(run.classify_reference(self.reference())["passed"])
        clean = self.reference()["stdout"]
        for updates in ({"stdout": ""}, {"stdout": clean + "\n" + clean},
                        {"stdout": clean + "\n" + output([message("failed proof", "error")])},
                        {"stdout": clean + "\n" + output([message("uses sorry", "warning")])},
                        {"stdout": clean + "\nnot JSON"}, {"returncode": 1},
                        {"stderr": "runtime failure"}, {"timed_out": True}, {"invalid_utf8": True}):
            with self.subTest(updates=updates):
                self.assertFalse(run.classify_reference(self.reference(**updates))["passed"])

    def mocked_main(self, *, reference_failed=False, failed_case=None, input_changed=False):
        """Exercise receipt/exit logic without invoking Lean, Lake, Elan, or Git."""
        ref = self.reference(returncode=1 if reference_failed else 0)

        def stage(case, name, *args):
            passed = not (case["id"] == failed_case and name == "original")
            return self.stage(name, passed=passed, completed_source="List.foldr Nat.add 1")

        setup = subprocess.CompletedProcess([], 0, json.dumps({"LEAN_PATH": "unused"}), "")
        fingerprints = [{"source": "before"}, {"source": "changed" if input_changed else "before"}]
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "receipts"
            argv = ["run_sketches.py", "--lean", str(Path(directory) / "unused-lean"),
                    "--budget", "5000", "--out", str(out)]
            with patch.object(sys, "argv", argv), patch.object(run, "fingerprints", side_effect=fingerprints), \
                    patch.object(run.subprocess, "check_output", side_effect=["1" * 40, "", "1" * 40]), \
                    patch.object(run.subprocess, "run", return_value=setup), \
                    patch.object(run, "process", return_value=ref), \
                    patch.object(run, "run_stage", side_effect=stage), \
                    contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as stopped:
                run.main()
            return stopped.exception.code, json.loads((out / "receipt.json").read_text(encoding="utf-8"))

    def test_reference_failure_fails_run_without_changing_public_denominator(self):
        status, receipt = self.mocked_main(reference_failed=True)
        self.assertEqual(status, 1)
        self.assertEqual((receipt["passed"], receipt["total"]), (7, 7))
        self.assertEqual((receipt["actual_public_processes"], receipt["reference_processes"]), (10, 1))
        self.assertFalse(receipt["success"])
        self.assertIn("independent reference controls", receipt["failures"])

    def test_missing_replay_fails_case_without_shrinking_denominator(self):
        status, receipt = self.mocked_main(failed_case="two-hole-fold")
        self.assertEqual(status, 1)
        self.assertEqual((receipt["passed"], receipt["total"]), (6, 7))
        self.assertEqual((receipt["actual_public_processes"], receipt["expected_public_processes"]), (9, 10))
        self.assertFalse(receipt["success"])
        self.assertIn("two-hole-fold", receipt["failures"])

    def test_input_change_fails_otherwise_successful_run(self):
        status, receipt = self.mocked_main(input_changed=True)
        self.assertEqual(status, 1)
        self.assertEqual((receipt["passed"], receipt["total"]), (7, 7))
        self.assertFalse(receipt["success"])
        self.assertIn("inputs changed during run", receipt["failures"])


if __name__ == "__main__":
    unittest.main()
