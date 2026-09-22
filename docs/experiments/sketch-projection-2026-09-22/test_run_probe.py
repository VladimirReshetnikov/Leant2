"""Pure parser/classification checks. No native command or process is started."""
from __future__ import annotations
import importlib.util
import json
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location("frozen_foldr1_runner", Path(__file__).with_name("run_probe.py"))
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


def raw(text, **overrides):
    return {"stdout": text.encode("utf-8"), "stderr": b"", "returncode": 0,
            "timed_out": False, "launch_error": False, "interrupted": False, **overrides}


def prelude(budget=5000):
    return (f"PROBE_BEGIN case=church_case_039 operation=foldr1 observations=36 providers=0 profile=strictConstructive budgetMs={budget}\n"
            "PROBE_ELAPSED_MS 5010\nPROBE_PREPARATION { holes := [step, init, finish] }\n"
            "PROBE_LEDGER { ruleApplications := 100,\n  unifications := 90, proofAttempts := 50, candidates := 0, rejected := 40 }\n")


def accepted():
    return (prelude().replace("candidates := 0", "candidates := 1") + "PROBE_OUTCOME verified candidates=1\n"
            "PROBE_CANDIDATE 0 original_type_replayed=true original_observations_replayed=36 strict_axioms=0\n"
            "PROBE_PROGRAM_TYPE ∀ A : Type, A → A\n"
            "PROBE_PROGRAM fun A x =>\n  x\nPROBE_PROGRAM_CONSTANTS []\n"
            "PROBE_PROGRAM_DEPENDENCIES_REVIEWED 0\n"
            "PROBE_ACCEPTED exact_type_and_all_36_observations_replayed\n")


def negative(kind="budgetExhausted", certificate="false"):
    return (prelude() + f"PROBE_OUTCOME negative kind=Leant2.NegativeKind.{kind} certificate={certificate}\n"
            "PROBE_NOT_ACCEPTED inspect_negative_kind_and_certificate\n")


class ClassificationTests(unittest.TestCase):
    def status(self, text, **overrides):
        return RUNNER.classify(raw(text, **overrides), budget=5000)["classification"]

    def test_complete_acceptance(self):
        result = RUNNER.classify(raw(accepted()), budget=5000)
        self.assertEqual(result["classification"], "accepted")
        self.assertEqual(result["api_elapsed_ms"], 5010)
        self.assertEqual(result["ledger"]["unifications"], 90)

    def test_both_bounded_negatives(self):
        for kind in ("budgetExhausted", "grammarExhausted"):
            self.assertEqual(self.status(negative(kind)), "bounded_miss")

    def test_refuted_proposals_are_bounded(self):
        text = prelude() + "PROBE_OUTCOME refutedAll rejected=40\nPROBE_NOT_ACCEPTED bounded_proposals_failed_no_impossibility_claim\n"
        self.assertEqual(self.status(text), "bounded_miss")

    def test_semantic_negative_is_failure(self):
        for kind in ("impossible", "contractImpossible"):
            self.assertEqual(self.status(negative(kind, "true")), "failure")

    def test_bad_native_statuses(self):
        for fields in ({"returncode": 1}, {"timed_out": True}, {"launch_error": True},
                       {"stderr": b"native error"}, {"interrupted": True}):
            self.assertEqual(self.status(accepted(), **fields), "failure")

    def test_invalid_utf8(self):
        self.assertEqual(RUNNER.classify(raw("", stdout=b"\xff"), budget=5000)["classification"], "failure")

    def test_native_diagnostics_fail(self):
        for severity in ("error", "warning", "information"):
            message = json.dumps({"severity": severity, "data": "unexpected diagnostic"}) + "\n"
            self.assertEqual(self.status(accepted() + message), "failure")

    def test_missing_duplicate_or_contradictory_marker(self):
        cases = [accepted().replace("PROBE_ACCEPTED", "OMITTED"),
                 accepted() + "PROBE_ACCEPTED exact_type_and_all_36_observations_replayed\n",
                 accepted() + "PROBE_NOT_ACCEPTED inspect_negative_kind_and_certificate\n",
                 accepted().replace("original_observations_replayed=36", "original_observations_replayed=35"),
                 accepted().replace("candidates := 1", "candidates := 0"),
                 accepted().replace("budgetMs=5000", "budgetMs=10000")]
        for text in cases:
            self.assertEqual(self.status(text), "failure")

    def test_controls_require_exact_clean_audits(self):
        names = ["Reference.one", "Reference.two"]
        lines = [json.dumps({"severity": "information", "data": f"'{name}' does not depend on any axioms"}) for name in names]
        text = "\n".join(lines) + "\n"
        self.assertEqual(RUNNER.classify(raw(text), controls=names)["classification"], "controls_passed")
        for bad in (lines[0] + "\n", text + lines[0] + "\n", text.replace("does not depend on any axioms", "depends on axioms: [sorryAx]"),
                    text + "unexpected native output\n"):
            self.assertEqual(RUNNER.classify(raw(bad), controls=names)["classification"], "failure")

    def test_actual_native_information_envelope(self):
        fixture = Path(__file__).with_name("wrapper-fixtures")
        stdout = (fixture / "probe-5000-information.stdout.bin").read_bytes()
        stderr = (fixture / "probe-5000-information.stderr.bin").read_bytes()
        result = RUNNER.classify(raw("", stdout=stdout, stderr=stderr), budget=5000)
        self.assertEqual(result["classification"], "bounded_miss")
        self.assertEqual(result["transcript_transport"], "lean_information_envelope")
        self.assertEqual(result["api_elapsed_ms"], 5157)
        self.assertEqual(result["ledger"], {"ruleApplications": 9373, "unifications": 19436,
                                          "proofAttempts": 5693, "candidates": 0, "rejected": 5613})

    def actual_envelope(self):
        filename = Path(__file__).with_name("wrapper-fixtures") / "probe-5000-information.stdout.bin"
        return json.loads(filename.read_bytes().decode("utf-8"))

    def test_envelope_rejects_wrong_location_or_kind(self):
        original = self.actual_envelope()
        changes = [{"fileName": str(Path(__file__).with_name("Controls.lean"))},
                   {"pos": {"line": 87, "column": 0}}, {"pos": {"line": 86, "column": 1}},
                   {"endPos": {"line": 86, "column": 9}}, {"endPos": {"line": 87, "column": 8}},
                   {"severity": "warning"}, {"severity": "error"}, {"caption": "unrelated"}]
        for change in changes:
            message = {**original, **change}
            self.assertEqual(self.status(json.dumps(message)), "failure")

    def test_envelope_rejects_extra_or_duplicate_diagnostics(self):
        message = self.actual_envelope()
        one = json.dumps(message) + "\n"
        extra = json.dumps({"severity": "information", "data": "unrelated"}) + "\n"
        for text in (one + one, one + extra, one + prelude(), prelude() + one):
            self.assertEqual(self.status(text), "failure")
        for data in (message["data"] + message["data"], message["data"] + extra,
                     "unrelated output\n" + message["data"]):
            self.assertEqual(self.status(json.dumps({**message, "data": data})), "failure")

    def test_acceptance_inside_exact_information_envelope(self):
        message = {**self.actual_envelope(), "data": accepted()}
        self.assertEqual(self.status(json.dumps(message)), "accepted")


if __name__ == "__main__":
    unittest.main()
