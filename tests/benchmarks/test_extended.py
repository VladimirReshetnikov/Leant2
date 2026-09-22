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
        self.assertEqual(len([c for c in cases if c["expect"] == "candidate"]), 25)
        self.assertEqual({c["id"] for c in cases if c["expect"] == "open"},
                         set())
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

    def test_guard_manifest_preserves_finite_contracts_and_separate_universal_replay(self):
        cases = HARNESS.load_cases(ROOT / "tests/benchmarks/guards.json")
        by_id = {case["id"]: case for case in cases}
        original = {case["id"]: case for case in HARNESS.load_cases()}
        self.assertEqual(len(cases), 5)
        self.assertEqual(sum(case["expect"] == "candidate" for case in cases), 3)
        self.assertEqual(sum(case["expect"] == "none" for case in cases), 2)
        self.assertEqual(by_id["guard_nat_max"]["contract"], original["probe09_max"]["contract"])
        self.assertEqual(by_id["guard_drop_zeros"]["contract"], original["probe10_drop_zeros"]["contract"])
        for case in cases:
            transcript = HARNESS.transcript(case)
            self.assertEqual(transcript.count(":synth "), 1)
            if case["expect"] == "none":
                self.assertEqual(case["contract"], "False")
                continue
            query = next(line for line in transcript.splitlines() if line.startswith(":synth "))
            self.assertNotIn("∀", query)
            self.assertNotIn(" := " + case["reference"], transcript)
            self.assertNotEqual(case["replay"], case["contract"])
            self.assertIn(f"example : {case['type']} := it1", transcript)
            for check in case["kernel_checks"]:
                self.assertIn("∀", check["type"])
                self.assertNotIn("by decide", check["proof"])
                self.assertIn("reference_proof", check)
                command = f"example : {check['type'].replace('{f}', 'it1')} := {check['proof'].replace('{f}', 'it1')}"
                self.assertIn(command, transcript)
                self.assertGreater(transcript.index(command), transcript.index(query))
                reference_command = f"example : {check['type'].replace('{f}', 'reference')} := {check['reference_proof'].replace('{f}', 'reference')}"
                self.assertIn(reference_command, HARNESS.fixture_source([case]))

    def test_guard_provider_checks_keep_public_filter_scope_honest(self):
        cases = {case["id"]: case for case in
                 HARNESS.load_cases(ROOT / "tests/benchmarks/guards.json")}
        for name in ("guard_nat_max", "guard_nat_min"):
            case = cases[name]
            self.assertTrue({"Nat.max", "Max.max", "Nat.min", "Min.min"}.issubset(case["forbidden_providers"]))
            transcript = HARNESS.transcript(case)
            for provider in case["forbidden_providers"]:
                self.assertIn(f"providers.contains `{provider}", transcript)
            self.assertLess(transcript.index("providers.contains"), transcript.index(":synth "))
        drop = cases["guard_drop_zeros"]
        self.assertTrue({"List.filter", "List.filterMap"}.isdisjoint(drop.get("forbidden_providers", [])))
        self.assertIn("induction xs", drop["kernel_checks"][0]["proof"])
        self.assertEqual(drop["kernel_checks"][0]["type"],
                         "∀ xs : List Nat, {f} xs = List.filter (fun n => n != 0) xs")


if __name__ == "__main__":
    unittest.main()
