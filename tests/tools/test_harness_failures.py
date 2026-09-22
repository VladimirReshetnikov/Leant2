"""The acceptance driver must not turn missing output or failed processes green."""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
import run_all
import run_baseline


class Output(io.StringIO):
    def reconfigure(self, **kwargs):
        pass


class HarnessFailures(unittest.TestCase):
    def baseline(self, output, returncode=0, stderr=b""):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "synth-example.txt").write_text(":synth Nat\n:synth Bool\n", encoding="utf-8")
            (root / "synth-example.golden").write_text(
                "λ> :synth Nat\n  it1  0\nλ> :synth Bool\n  it1  true\n", encoding="utf-8")

            def run(command, **kwargs):
                if command[0] == "elan":
                    return subprocess.CompletedProcess(command, 0, "", "")
                return subprocess.CompletedProcess(command, returncode, output.encode("utf-8"), stderr)

            args = ["run_baseline.py", "--leant", str(root), "--out", str(root / "out")]
            with patch.object(sys, "argv", args), patch.object(subprocess, "run", side_effect=run), \
                    contextlib.redirect_stdout(Output()):
                status = run_baseline.main()
            return status, json.loads((root / "out/summary.json").read_text(encoding="utf-8"))

    def test_missing_query_remains_in_denominator(self):
        status, rows = self.baseline("λ> :synth Nat\n  it1  0\n-- leant2-query-end\n")
        self.assertEqual(status, 1)
        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[1]["ours"], "missing")
        self.assertFalse(rows[1]["ok"])

    def test_crash_after_candidates_is_failure(self):
        status, rows = self.baseline(self.complete_output(), 9)
        self.assertEqual(status, 1)
        self.assertFalse(any(row["ok"] for row in rows))

    def test_full_output_passes(self):
        status, rows = self.baseline(self.complete_output())
        self.assertEqual(status, 0)
        self.assertTrue(all(row["ok"] for row in rows))

    @staticmethod
    def complete_output():
        return ("λ> :synth Nat\n  it1  0\n-- leant2-query-end\n"
                "λ> :synth Bool\n  it1  true\n-- leant2-query-end\n")

    def test_missing_completion_is_not_success(self):
        status, rows = self.baseline(self.complete_output().replace("-- leant2-query-end\n", ""))
        self.assertEqual(status, 1)
        self.assertTrue(all(row["ours"] == "incomplete" for row in rows))

    def test_diagnostic_after_candidate_is_not_success(self):
        output = self.complete_output().replace("  it1  0\n", "  it1  0\nerror(lean.dependsOnNoncomputable): failed\n")
        status, rows = self.baseline(output)
        self.assertEqual(status, 1)
        self.assertEqual(rows[0]["ours"], "error")

    def test_stderr_after_success_is_failure(self):
        status, rows = self.baseline(self.complete_output(), stderr=b"runtime failure")
        self.assertEqual(status, 1)
        self.assertFalse(any(row["ok"] for row in rows))

    def test_later_command_is_outside_category_only_score(self):
        output = self.complete_output().replace("-- leant2-query-end\n", "-- leant2-query-end\nerror: later user command\n", 1)
        status, rows = self.baseline(output)
        self.assertEqual(status, 0)
        self.assertTrue(all(row["ok"] for row in rows))

    def aggregate(self, total, returncode):
        result = subprocess.CompletedProcess([], returncode, total, "failure details")
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(sys, "argv", ["run_all.py", "--skip-build", "--out", directory]), \
                patch.object(run_all, "HARNESSES", [("fake", ["fake.py"])]), \
                patch.object(subprocess, "run", return_value=result), \
                contextlib.redirect_stdout(Output()), self.assertRaises(SystemExit) as stopped:
            run_all.main()
        return stopped.exception.code

    def test_aggregate_checks_process_exit(self):
        self.assertEqual(self.aggregate("TOTAL 2/2\n", 4), 1)

    def test_aggregate_rejects_empty_score(self):
        self.assertEqual(self.aggregate("TOTAL 0/0\n", 0), 1)

    def test_aggregate_accepts_successful_score(self):
        self.assertEqual(self.aggregate("TOTAL 2/2\n", 0), 0)

    def integrated_aggregate(self, failing=None):
        totals = {"baseline": 278, "recursive": 9, "church": 28, "context": 95,
                  "corpus": 350, "session": 6, "results": 10, "extended": 29,
                  "recursion-gates": 5, "local-proofs": 6, "guard-gates": 5, "tree-composition": 3}
        commands = {}

        def run(command, **kwargs):
            if "--manifest" in command:
                manifest = command[command.index("--manifest") + 1]
                name = {"tests/benchmarks/recursion.json": "recursion-gates",
                        "tests/benchmarks/local-proofs.json": "local-proofs",
                        "tests/benchmarks/guards.json": "guard-gates",
                        "tests/benchmarks/tree-composition.json": "tree-composition"}[manifest]
            else:
                name = Path(command[3]).stem.removeprefix("run_")
            commands[name] = command
            total = totals[name]
            return subprocess.CompletedProcess(command, 1 if name == failing else 0,
                                               f"TOTAL {total}/{total}\n", "")

        with tempfile.TemporaryDirectory() as directory, \
                patch.object(sys, "argv", ["run_all.py", "--skip-build", "--out", directory]), \
                patch.object(subprocess, "run", side_effect=run), \
                contextlib.redirect_stdout(Output()), self.assertRaises(SystemExit) as stopped:
            try:
                run_all.main()
            finally:
                summary = json.loads((Path(directory) / "summary.json").read_text(encoding="utf-8"))
        return stopped.exception.code, commands, summary

    def test_aggregate_routes_independent_results_and_manifest_receipts(self):
        status, commands, summary = self.integrated_aggregate()
        self.assertEqual(status, 0)
        self.assertEqual(len(summary["harnesses"]), 12)
        self.assertEqual(sum(row["total"] for row in summary["harnesses"]), 824)
        outputs = {name: command[command.index("--out") + 1] for name, command in commands.items()}
        self.assertEqual(len(set(outputs.values())), 12)
        self.assertEqual(Path(outputs["results"]).name, "results")
        self.assertEqual(Path(outputs["extended"]).name, "extended.json")
        self.assertEqual(Path(outputs["recursion-gates"]).name, "recursion-gates.json")
        self.assertEqual(Path(outputs["local-proofs"]).name, "local-proofs.json")
        self.assertEqual(Path(outputs["guard-gates"]).name, "guard-gates.json")
        self.assertEqual(Path(outputs["tree-composition"]).name, "tree-composition.json")
        recursion = commands["recursion-gates"]
        self.assertEqual(recursion[recursion.index("--manifest") + 1], "tests/benchmarks/recursion.json")
        local = commands["local-proofs"]
        self.assertEqual(local[local.index("--manifest") + 1], "tests/benchmarks/local-proofs.json")
        guards = commands["guard-gates"]
        self.assertEqual(guards[guards.index("--manifest") + 1], "tests/benchmarks/guards.json")
        tree = commands["tree-composition"]
        self.assertEqual(tree[tree.index("--manifest") + 1], "tests/benchmarks/tree-composition.json")
        self.assertNotIn("--manifest", commands["extended"])

    def test_manifest_exit_failure_fails_aggregate_despite_full_score(self):
        for name, total in (("recursion-gates", 5), ("local-proofs", 6), ("guard-gates", 5), ("tree-composition", 3)):
            with self.subTest(harness=name):
                status, _, summary = self.integrated_aggregate(failing=name)
                self.assertEqual(status, 1)
                receipt = next(row for row in summary["harnesses"] if row["harness"] == name)
                self.assertEqual((receipt["passed"], receipt["total"]), (total, total))
                self.assertFalse(receipt["ok"])


if __name__ == "__main__":
    unittest.main()
