"""Protocol-boundary tests: a reported candidate alone must never pass E8."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("run_extended", ROOT / "tools/run_extended.py")
HARNESS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(HARNESS)


class ExtendedProtocolTests(unittest.TestCase):
    def setUp(self):
        self.candidate = {"expect": "candidate"}
        self.open = {"expect": "open"}
        self.control = {"expect": "none"}
        self.prefix = "λ> :synth extended_candidate : Nat\n-- leant2: 12 ms\n"
        self.solved = self.prefix + '  it1  0\n"EXTENDED_REPLAY_OK"\n'

    def result(self, case, output, stderr="", returncode=0):
        return HARNESS.classify(case, output, stderr, returncode)

    def test_candidate_requires_replay(self):
        self.assertTrue(self.result(self.candidate, self.solved)["passed"])
        result = self.result(self.candidate, self.prefix + "  it1  0\n")
        self.assertFalse(result["passed"])
        self.assertEqual(result["outcome"], "replay_error")

    def test_diagnostic_after_candidate_is_failure_even_when_open(self):
        for case in (self.candidate, self.open):
            result = self.result(case, self.solved + "error: unsupported recursor\n")
            self.assertFalse(result["passed"])
            result = self.result(case, self.solved + "error(lean.dependsOnNoncomputable): no executable code\n")
            self.assertFalse(result["passed"])

    def test_current_and_legacy_timing_formats(self):
        self.assertEqual(self.result(self.candidate, self.solved)["query_elapsed_ms"], 12)
        self.assertEqual(self.result(self.candidate, self.solved.replace("-- leant2:", "leant2:"))["query_elapsed_ms"], 12)

    def test_stderr_and_process_failure_are_not_open_results(self):
        self.assertFalse(self.result(self.open, self.solved, "runtime failure")["passed"])
        self.assertFalse(self.result(self.open, self.solved, returncode=1)["passed"])

    def test_impossible_contract_requires_certified_rejection(self):
        self.assertTrue(self.result(self.control, self.prefix +
                        "provably no program satisfies the contract\n")["passed"])
        self.assertFalse(self.result(self.control, self.prefix + "budget exhausted\n")["passed"])
        self.assertEqual(self.result(self.control, self.solved)["outcome"], "false_positive")

    def test_runtime_counterexample_is_failure(self):
        bad = self.solved.replace("EXTENDED_REPLAY_OK", "EXTENDED_REPLAY_FALSE")
        self.assertEqual(self.result(self.candidate, bad)["outcome"], "false_positive")

    def test_open_results_must_be_recognized_and_complete(self):
        self.assertTrue(self.result(self.open, self.prefix + "budget exhausted\n")["passed"])
        self.assertFalse(self.result(self.open, self.prefix + "unknown outcome\n")["passed"])
        self.assertFalse(self.result(self.open, "budget exhausted\n")["passed"])
        self.assertFalse(self.result(self.open, self.solved + self.solved)["passed"])
        self.assertFalse(self.result(self.open, self.prefix + "provably uninhabited\n")["passed"])
        self.assertFalse(self.result(self.open, self.prefix + "provably no program satisfies the contract\n")["passed"])

    def test_replay_without_candidate_is_protocol_error(self):
        output = self.prefix + 'budget exhausted\n"EXTENDED_REPLAY_OK"\n'
        self.assertEqual(self.result(self.open, output)["outcome"], "protocol_error")

    def test_fixtures_have_exact_article_coverage(self):
        cases = HARNESS.load_cases()
        probes = [c for c in cases if c["group"] == "article-probes"]
        self.assertEqual([c["id"][:7] for c in probes], [f"probe{n:02}" for n in range(1, 17)])
        self.assertEqual(len([c for c in cases if c["group"] == "lean-core"]), 9)
        self.assertEqual(len([c for c in cases if c["expect"] == "none"]), 4)
        self.assertEqual(len([c for c in cases if c["expect"] == "candidate"]), 20)
        self.assertEqual({c["id"] for c in cases if c["expect"] == "open"},
                         {"probe09_max", "probe10_drop_zeros", "probe11_tree_inorder",
                          "probe14_fin", "probe16_le_trans"})
        for c in cases:
            transcript = HARNESS.transcript(c)
            self.assertEqual(transcript.count(":synth "), 1)
            self.assertNotIn("def reference", transcript)

    def test_kernel_checks_are_withheld_and_validate_the_reference(self):
        case = {"id": "kernel_check", "expect": "candidate", "type": "Nat → Nat",
                "reference": "Nat.succ", "replay": "{f} 8 = 9",
                "kernel_checks": [{"type": "∀ n, {f} n = n + 1",
                                   "proof": "by intro n; rfl",
                                   "reference_proof": "by intro n; simp [{f}]"}]}
        transcript = HARNESS.transcript(case)
        query = next(line for line in transcript.splitlines() if line.startswith(":synth"))
        self.assertNotIn("∀ n", query)
        self.assertNotIn("Nat.succ", transcript)
        self.assertIn("example : ∀ n, it1 n = n + 1 := by intro n; rfl", transcript)
        self.assertIn("(Leant2.resultBinding? (← getEnv) `it1).isSome", transcript)
        self.assertNotIn("(← getEnv).contains `it1", transcript)
        self.assertIn("example : ∀ n, reference n = n + 1 := by intro n; simp [reference]",
                      HARNESS.fixture_source([case]))

    def test_invalid_kernel_checks_are_rejected(self):
        case = {"id": "invalid_check", "expect": "candidate", "type": "Nat",
                "reference": "0"}
        for checks in ({"type": "True", "proof": "by trivial"},
                       [{"type": "True"}], [{"type": "True", "proof": ""}],
                       [{"type": "True", "proof": "by trivial", "reference_proof": 1}]):
            with self.subTest(checks=checks), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "manifest.json"
                path.write_text(json.dumps({"cases": [dict(case, kernel_checks=checks)]}),
                                encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "kernel_checks"):
                    HARNESS.load_cases(path)

    def test_recursion_manifest_keeps_required_equations_and_controls(self):
        cases = HARNESS.load_cases(ROOT / "tests/benchmarks/recursion.json")
        self.assertEqual(len([case for case in cases if case["expect"] == "candidate"]), 3)
        self.assertEqual(len([case for case in cases if case["expect"] == "none"]), 2)
        for case in cases:
            transcript = HARNESS.transcript(case)
            self.assertEqual(transcript.count(":synth "), 1)
            if case["expect"] == "candidate":
                self.assertEqual(len(case["kernel_checks"]), 2)
                self.assertIn("∀", case["kernel_checks"][1]["type"])
                self.assertNotIn(" := " + case["reference"], transcript)
                for name in case["forbidden_providers"]:
                    self.assertIn(f"providers.contains `{name}", transcript)
                self.assertLess(transcript.index("providers.contains"), transcript.index(":synth "))
                self.assertNotEqual(case.get("contract"), case["replay"])
        vector = next(case for case in cases if case["id"] == "recursion_vec_map")
        self.assertEqual(vector["type"],
                         "∀ (A B : Type), (A → B) → ∀ n, RecursionVec A n → RecursionVec B n")


if __name__ == "__main__":
    unittest.main()
