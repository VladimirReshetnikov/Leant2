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
        with patch.object(sys, "argv", ["run_all.py", "--skip-build"]), \
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


if __name__ == "__main__":
    unittest.main()
