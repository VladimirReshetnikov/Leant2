"""Secondary harnesses reject incomplete REPL output and hidden Lean errors."""
import contextlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
import repl_protocol as protocol
import run_church
import run_recursive


class Output(io.StringIO):
    def reconfigure(self, **kwargs):
        pass


def query(command=":synth q : Nat", body="  it1  0", complete=True):
    return (f"λ> {command}\nleant2: 1 ms\n{body}\n" +
            ("-- leant2-query-end\n" if complete else ""))


class ProtocolTests(unittest.TestCase):
    command = ":synth q : Nat"

    def parse(self, text, **kwargs):
        return protocol.parse(text, kwargs.pop("stderr", ""), kwargs.pop("status", 0),
                              kwargs.pop("expected", [self.command]), **kwargs)

    def test_candidate_then_named_error_is_failure(self):
        result = self.parse(query(body="  it1  0\nerror(lean.dependsOnNoncomputable): failed"))
        self.assertFalse(result.healthy)
        self.assertEqual(result.query(0).outcome, "error")
        self.assertFalse(protocol.passes(result.query(0), "candidate"))

    def test_missing_and_unterminated_queries_do_not_pass(self):
        for text in ("", query(complete=False)):
            result = self.parse(text)
            self.assertFalse(result.healthy)
            self.assertFalse(protocol.passes(result.query(0), "candidate"))

    def test_extra_queries_and_wrong_echo_fail(self):
        self.assertFalse(self.parse(query() + query()).healthy)
        self.assertFalse(self.parse(query(":synth wrong : Bool")).healthy)

    def test_duplicate_completion_fails(self):
        self.assertFalse(self.parse(query() + "-- leant2-query-end\n").healthy)

    def test_false_control_needs_certified_rejection(self):
        for body in ("", "budget exhausted", "no term found within the search bounds", "  it1  0"):
            self.assertFalse(protocol.passes(self.parse(query(body=body)).query(0), "false"))
        result = self.parse(query(body="provably no program satisfies the contract"))
        self.assertTrue(result.healthy)
        self.assertTrue(protocol.passes(result.query(0), "false"))

    def test_opaque_contract_remains_inconclusive(self):
        for body in ("budget exhausted", "no term found within the search bounds",
                     "3 program(s) of the type proposed, none passed the contract"):
            result = self.parse(query(body=body))
            self.assertTrue(result.healthy)
            self.assertTrue(protocol.passes(result.query(0), "inconclusive"))
        impossible = self.parse(query(body="provably no program satisfies the contract"))
        self.assertFalse(protocol.passes(impossible.query(0), "inconclusive"))

    def test_zero_exit_stderr_and_nonzero_exit_fail(self):
        self.assertFalse(self.parse(query(), stderr="runtime failure").healthy)
        self.assertFalse(self.parse(query(), status=9).healthy)

    def test_rejected_declaration_is_allowed_only_outside_query(self):
        text = "error: Type mismatch: True has type Prop but expected Nat\n" + query()
        self.assertFalse(self.parse(text).healthy)
        self.assertTrue(self.parse(text, allowed_outside_errors=1).healthy)
        bad = query(body="  it1  0\nerror: Type mismatch")
        self.assertFalse(self.parse(bad, allowed_outside_errors=1).healthy)
        self.assertFalse(self.parse("uncaught exception: crash\n" + query(), allowed_outside_errors=1).healthy)

    def test_timing_and_windows_newlines(self):
        self.assertTrue(self.parse(query().replace("\n", "\r\n")).healthy)
        self.assertFalse(self.parse(query().replace("leant2: 1 ms\n", "")).healthy)

    def test_setup_errors_and_sorries_fail(self):
        self.assertFalse(self.parse("error: unknown constructor\n" + query()).healthy)
        self.assertFalse(self.parse(query(body="  it1  0\nwarning: declaration uses `sorry`")).healthy)

    def test_contradictory_outcomes_fail(self):
        result = self.parse(query(body="  it1  0\nbudget exhausted"))
        self.assertFalse(result.healthy)


class HarnessIntegrationTests(unittest.TestCase):
    def run_harness(self, module, emit):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / ("church" if module is run_church else "recursive.out")

            def run(command, **kwargs):
                if command[0] == "elan":
                    return subprocess.CompletedProcess(command, 0, "", "")
                self.assertIn("--query-markers", command)
                source = kwargs["input"].decode("utf-8")
                return subprocess.CompletedProcess(command, 0, emit(source).encode("utf-8"), b"")

            screen = Output()
            args = [module.__name__, "--out", str(output)]
            with patch.object(sys, "argv", args), patch.object(subprocess, "run", side_effect=run), \
                    contextlib.redirect_stdout(screen):
                status = module.main()
            paths = list(Path(directory).rglob("*.out"))
            self.assertTrue(paths)
            for path in paths:
                self.assertTrue(path.with_suffix(".in").exists())
                self.assertTrue(path.with_suffix(".stderr").exists())
            return status, screen.getvalue()

    @staticmethod
    def successful(source):
        return "".join(query(line, "provably no program satisfies the contract" if line.endswith(" where False") else "  it1  0")
                       for line in source.splitlines() if line.startswith(":synth"))

    def test_recursive_complete_and_truncated_denominator(self):
        status, text = self.run_harness(run_recursive, self.successful)
        self.assertEqual(status, 0)
        self.assertIn("TOTAL 9/9", text)
        status, text = self.run_harness(run_recursive, lambda source: self.successful(source).split("λ>")[0])
        self.assertEqual(status, 1)
        self.assertIn("TOTAL 0/9", text)

    def test_church_truncation_and_stretch_errors_fail_without_shrinking_total(self):
        spec = SimpleNamespace(lean_prelude=lambda: [], lean_predicate=lambda op, name: "True")
        groups = [("church", [f"core{i}" for i in range(6)]),
                  ("extended", [f"extended{i}" for i in range(13)]),
                  ("partial", sorted(run_church.STRETCH) + [f"required{i}" for i in range(6)])]
        fixture = [(label, spec, ops, {op: "Nat" for op in ops}, []) for label, ops in groups]
        with patch.object(run_church, "load_specs", return_value=fixture):
            status, text = self.run_harness(run_church, self.successful)
            self.assertEqual(status, 0)
            self.assertIn("TOTAL 28/28", text)
            status, text = self.run_harness(run_church, lambda source: query(next(line for line in source.splitlines() if line.startswith(":synth"))))
            self.assertEqual(status, 1)
            self.assertIn("TOTAL 0/28", text)
            status, text = self.run_harness(run_church, lambda source: self.successful(source).replace("  it1  0", "  it1  0\nerror: bad stretch", 1) if "partial_at" in source else self.successful(source))
            self.assertEqual(status, 1)
            self.assertIn("STRETCH-ERROR", text)
            self.assertIn("TOTAL 21/28", text)


if __name__ == "__main__":
    unittest.main()
