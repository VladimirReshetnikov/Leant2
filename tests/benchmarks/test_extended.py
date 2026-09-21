"""Protocol-boundary tests: a reported candidate alone must never pass E8."""
import importlib.util
from pathlib import Path
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
        for c in cases:
            transcript = HARNESS.transcript(c)
            self.assertEqual(transcript.count(":synth "), 1)
            self.assertNotIn("def reference", transcript)


if __name__ == "__main__":
    unittest.main()
