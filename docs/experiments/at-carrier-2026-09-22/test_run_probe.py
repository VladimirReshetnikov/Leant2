"""Pure synthetic classifier/source/ordering guards. No native process runs.

All transcripts here are synthetic protocol fixtures, not at execution evidence.
"""
from __future__ import annotations

from contextlib import ExitStack, redirect_stdout
import importlib.util
import io
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RUNNER = load("at_probe_runner_tests", "run_probe.py")
GENERATOR = load("at_probe_generator_tests", "prepare.py")


def raw(text, **overrides):
    return {"stdout": text.encode("utf-8"), "stderr": b"", "returncode": 0,
            "timed_out": False, "launch_error": False, "interrupted": False, **overrides}


def prelude(budget=5000):
    return (f"PROBE_BEGIN case=church_case_033 operation=at observations=168 providers=1 profile=strictConstructive budgetMs={budget}\n"
            "PROBE_ELAPSED_MS 5010\nPROBE_PREPARATION { holes := [step, init] }\n"
            "PROBE_LEDGER { ruleApplications := 100,\n  unifications := 90, proofAttempts := 50, candidates := 0, rejected := 40 }\n")


def accepted(budget=5000):
    # Syntactically complete protocol, not a claimed Lean term/result.
    return (prelude(budget).replace("candidates := 0", "candidates := 1") + "PROBE_OUTCOME verified candidates=1\n"
            "PROBE_CANDIDATE 0 original_type_replayed=true original_observations_replayed=168 strict_axioms=0\n"
            "PROBE_PROGRAM_TYPE synthetic target text\n"
            "PROBE_PROGRAM synthetic completed expression\n  continuation\nPROBE_PROGRAM_CONSTANTS [BehaviorPartialNumeric.intCase]\n"
            "PROBE_PROGRAM_DEPENDENCIES_REVIEWED 1\n"
            "PROBE_ACCEPTED exact_type_and_all_168_observations_replayed\n")


def negative(kind="budgetExhausted", certificate="false", budget=5000):
    return (prelude(budget) + f"PROBE_OUTCOME negative kind=Leant2.NegativeKind.{kind} certificate={certificate}\n"
            "PROBE_NOT_ACCEPTED inspect_negative_kind_and_certificate\n")


def envelope(data):
    source = HERE / "Probe.lean"
    lines = [n for n, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1)
             if line == "run_elab do"]
    assert len(lines) == 1
    return {"fileName": str(source), "severity": "information", "caption": "",
            "pos": {"line": lines[0], "column": 0},
            "endPos": {"line": lines[0], "column": 8}, "data": data}


def control_text(names):
    return "\n".join(json.dumps({"severity": "information", "data": f"'{name}' does not depend on any axioms"})
                     for name in names) + "\n"


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

    def test_refuted_proposals_require_matching_positive_count(self):
        text = prelude() + "PROBE_OUTCOME refutedAll rejected=40\nPROBE_NOT_ACCEPTED bounded_proposals_failed_no_impossibility_claim\n"
        self.assertEqual(self.status(text), "bounded_miss")
        for count in ("0", "39"):
            self.assertEqual(self.status(text.replace("rejected=40", "rejected=" + count)), "failure")

    def test_semantic_negative_or_certified_bounded_negative_is_failure(self):
        for kind, certificate in (("impossible", "true"), ("contractImpossible", "true"),
                                  ("budgetExhausted", "true"), ("impossible", "false")):
            self.assertEqual(self.status(negative(kind, certificate)), "failure")

    def test_bad_native_statuses(self):
        for fields in ({"returncode": 1}, {"returncode": None}, {"timed_out": True}, {"launch_error": True},
                       {"stderr": b"native error"}, {"interrupted": True}):
            self.assertEqual(self.status(accepted(), **fields), "failure")

    def test_invalid_utf8(self):
        self.assertEqual(RUNNER.classify(raw("", stdout=b"\xff"), budget=5000)["classification"], "failure")

    def test_native_diagnostics_fail_even_after_candidate(self):
        for severity in ("error", "warning", "information"):
            message = json.dumps({"severity": severity, "data": "unexpected diagnostic"}) + "\n"
            self.assertEqual(self.status(accepted() + message), "failure")

    def test_identity_observation_provider_and_profile_changes_fail(self):
        for before, after in (("observations=168", "observations=167"), ("providers=1", "providers=0"),
                              ("church_case_033", "church_case_039"), ("budgetMs=5000", "budgetMs=10000"),
                              ("strictConstructive", "standard"),
                              ("original_observations_replayed=168", "original_observations_replayed=167")):
            self.assertEqual(self.status(accepted().replace(before, after)), "failure")

    def test_missing_duplicate_or_contradictory_marker(self):
        cases = [accepted().replace("PROBE_ACCEPTED", "OMITTED"),
                 accepted() + "PROBE_ACCEPTED exact_type_and_all_168_observations_replayed\n",
                 accepted() + "PROBE_NOT_ACCEPTED inspect_negative_kind_and_certificate\n",
                 accepted().replace("candidates := 1", "candidates := 0"),
                 accepted().replace("PROBE_PROGRAM_DEPENDENCIES_REVIEWED 1", "PROBE_PROGRAM_DEPENDENCIES_REVIEWED unknown"),
                 accepted().replace("PROBE_LEDGER", "PROBE_OTHER")]
        for text in cases:
            self.assertEqual(self.status(text), "failure")

    def test_controls_require_exact_eleven_clean_audits(self):
        names = json.loads((HERE / "provenance.json").read_text(encoding="utf-8"))["control_declarations"]
        self.assertEqual(len(names), 11)
        text = control_text(names)
        self.assertEqual(RUNNER.classify(raw(text), controls=names)["classification"], "controls_passed")
        for bad in (control_text(names[:-1]), text + control_text(names[:1]),
                    text.replace("does not depend on any axioms", "depends on axioms: [sorryAx]"),
                    text + "unexpected native output\n", text + prelude()):
            self.assertEqual(RUNNER.classify(raw(bad), controls=names)["classification"], "failure")

    def test_synthetic_exact_information_envelope(self):
        result = RUNNER.classify(raw(json.dumps(envelope(negative()))), budget=5000)
        self.assertEqual(result["classification"], "bounded_miss")
        self.assertEqual(result["transcript_transport"], "lean_information_envelope")
        self.assertEqual(self.status(json.dumps(envelope(accepted()))), "accepted")

    def test_envelope_rejects_wrong_location_or_kind(self):
        original = envelope(accepted())
        line = original["pos"]["line"]
        changes = [{"fileName": str(HERE / "Controls.lean")},
                   {"pos": {"line": line + 1, "column": 0}}, {"pos": {"line": line, "column": 1}},
                   {"endPos": {"line": line, "column": 9}}, {"endPos": {"line": line + 1, "column": 8}},
                   {"severity": "warning"}, {"severity": "error"}, {"caption": "unrelated"}]
        for change in changes:
            self.assertEqual(self.status(json.dumps({**original, **change})), "failure")

    def test_envelope_rejects_extra_duplicate_nested_or_mixed_diagnostics(self):
        message = envelope(accepted())
        one = json.dumps(message) + "\n"
        extra = json.dumps({"severity": "information", "data": "unrelated"}) + "\n"
        for text in (one + one, one + extra, one + prelude(), prelude() + one):
            self.assertEqual(self.status(text), "failure")
        for data in (message["data"] + message["data"], message["data"] + extra,
                     "unrelated output\n" + message["data"]):
            self.assertEqual(self.status(json.dumps({**message, "data": data})), "failure")


class SourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.artifacts = GENERATOR.build_artifacts()
        cls.probe = cls.artifacts["Probe.lean"].decode("utf-8")
        cls.controls = cls.artifacts["Controls.lean"].decode("utf-8")
        cls.manifest = json.loads(cls.artifacts["provenance.json"])
        cls.spec = GENERATOR.load_spec()

    def test_exact_artifacts_reproduce_authoritative_inputs(self):
        for name, expected in self.artifacts.items():
            self.assertEqual((HERE / name).read_bytes(), expected, name)
        self.assertEqual(RUNNER.original_provenance()[0], self.manifest)

    def test_original_target_and_all_observations_unchanged(self):
        self.assertEqual(self.manifest["exact_established_defaulted_lean_type"], self.spec.LEAN_TYPES["at"])
        self.assertEqual(self.manifest["observations"], json.loads(json.dumps(self.spec.FIXTURES["at"])))
        self.assertEqual(len({row["id"] for row in self.manifest["observations"]}), 168)
        self.assertEqual(self.manifest["observations"][0]["id"], "at_int_0_0_neg2")
        self.assertEqual(self.manifest["observations"][-1]["id"], "at_mixed_1_2_9")
        self.assertIn("\n".join(self.spec.lean_prelude(["at"])), self.probe)
        self.assertEqual(self.manifest["exact_contract"], "BehaviorPartial.check_at (f) = true")

    def test_only_exact_existing_primitive_and_strict_query(self):
        providers = self.spec.search_provider_source("at", "lean")
        self.assertIn("\n".join(providers), self.probe)
        self.assertEqual(self.manifest["explicit_query_providers"], ["BehaviorPartialNumeric.intCase"])
        self.assertIn("providers := #[``BehaviorPartialNumeric.intCase]", self.probe)
        self.assertIn("profile := .strictConstructive", self.probe)
        self.assertIn("maxCandidates := 1, graceMs := 0", self.probe)
        self.assertNotIn("sessionProviders", self.probe)

    def test_two_holes_exclude_list_and_index_from_original_scope(self):
        sketch = self.probe.split("  let sketch ← `(\n", 1)[1].split("\n  IO.println", 1)[0]
        self.assertTrue(sketch.startswith("    fun (A : Type) (d : A) =>\n      (fun (step"))
        self.assertIn("(n : Int) (xs : ∀ R : Type", sketch)
        self.assertTrue(sketch.endswith("xs (Int → A) step init n) ?step ?init)"))
        self.assertEqual(re.findall(r"\?\w+", sketch), ["?step", "?init"])
        self.assertIn("hole.locals == 2", self.probe)
        self.assertIn("== #[`step, `init]", self.probe)

    def test_controls_are_lean_only_and_known_terms_never_in_probe(self):
        self.assertEqual(re.findall(r"^import .*", self.controls, re.M), ["import Lean"])
        self.assertEqual(re.findall(r"^import .*", self.probe, re.M), ["import Leant2.Frontend.Sketch.Run"])
        witness = self.spec.LEAN_PROVIDER_WITNESSES["at"]
        self.assertIn(witness, self.controls)
        self.assertNotIn(witness, self.probe)
        for namespace in ("BehaviorPartialOracle", "BehaviorPartialControl"):
            self.assertNotIn("namespace " + namespace, self.probe)
        for wrong in ("always_default", "ignores_index"):
            self.assertIn("theorem wrong_at_" + wrong + "_rejected", self.controls)
        self.assertEqual(re.findall(r"^#print axioms (.+)$", self.controls, re.M), self.manifest["control_declarations"])

    def test_transitive_program_audit_keeps_narrow_primitive_exception(self):
        self.assertIn("if forbiddenNamespace && name != ``BehaviorPartialNumeric.intCase then", self.probe)
        self.assertIn("(`BehaviorPartialNumeric).isPrefixOf name", self.probe)
        self.assertIn("pending := pending ++ info.type.getUsedConstants", self.probe)
        self.assertIn("info.value? (allowOpaque := true)", self.probe)
        self.assertIn("pending := pending ++ value.getUsedConstants", self.probe)
        self.assertIn("candidate.proof (mkApp contract candidate.program)", self.probe)

    def test_mutated_provenance_is_refused_before_native_launch(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            for name, content in self.artifacts.items():
                (folder / name).write_bytes(content)
            # Use the real generator through an explicit test-only load seam;
            # changing one recorded observation cannot be blessed by a stale hash.
            altered = dict(self.manifest)
            altered["observation_count"] = 167
            (folder / "provenance.json").write_text(json.dumps(altered), encoding="utf-8")
            with patch.object(RUNNER, "HERE", folder), patch.object(RUNNER.importlib.util, "spec_from_file_location") as loader:
                loader.return_value = type("Spec", (), {"loader": type("Loader", (), {"exec_module": staticmethod(lambda module: None)})()})()
                with patch.object(RUNNER.importlib.util, "module_from_spec", return_value=GENERATOR):
                    with self.assertRaisesRegex(ValueError, "generated artifact differs"):
                        RUNNER.original_provenance()


class OrchestrationTests(unittest.TestCase):
    def execute_fake(self, *, bad_controls=False, drift=False, first_failure=False):
        """Mock all native/fingerprint entry points; exercise actual main order."""
        with tempfile.TemporaryDirectory() as temporary, ExitStack() as stack:
            base = Path(temporary)
            root = base / "root"
            root.mkdir()
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0", encoding="utf-8")
            (root / "lake-manifest.json").write_text('{"packages": []}', encoding="utf-8")
            lean = base / "leanprover--lean4---v4.34.0/bin/lean.exe"
            lean.parent.mkdir(parents=True)
            lean.write_bytes(b"not executable; native calls are mocked")
            out = base / "output"
            manifest, spec, corpus, church, normalized = RUNNER.original_provenance()
            seen = []

            def fake_native(executable, source, folder, timeout, budget):
                folder.mkdir()
                seen.append(budget)
                if budget is None:
                    names = manifest["control_declarations"]
                    text = control_text(names[:-1] if bad_controls else names)
                else:
                    text = negative(budget=budget)
                    if first_failure:
                        text += json.dumps({"severity": "error", "data": "synthetic error"})
                process = {"source_sha256_before": "same", "source_sha256_after": "same",
                           "lean_sha256_before": "same", "lean_sha256_after": "same"}
                return raw(text), process

            stack.enter_context(patch.object(RUNNER, "ROOT", root))
            stack.enter_context(patch.object(RUNNER, "original_provenance", return_value=(manifest, spec, corpus, church, normalized)))
            stack.enter_context(patch.object(RUNNER, "fingerprints", side_effect=[{"identity": 1}, {"identity": 2 if drift else 1}]))
            stack.enter_context(patch.object(RUNNER, "run_native", side_effect=fake_native))
            stack.enter_context(patch.object(RUNNER.subprocess, "Popen", side_effect=AssertionError("native forbidden in pure tests")))
            stack.enter_context(patch.object(RUNNER.sys, "argv", ["run_probe.py", "--lean", str(lean), "--out", str(out), "--native-slot-released"]))
            stack.enter_context(redirect_stdout(io.StringIO()))
            code = RUNNER.main()
            receipt = json.loads((out / "receipt.json").read_text(encoding="utf-8"))
            return code, receipt, seen

    def test_controls_must_precede_queries_and_failure_stops_both(self):
        code, receipt, seen = self.execute_fake(bad_controls=True)
        self.assertEqual(code, 1)
        self.assertEqual(seen, [None])
        self.assertEqual(receipt["skipped_budgets_ms"], [5000, 10000])

    def test_bounded_miss_continues_second_budget_and_returns_two(self):
        code, receipt, seen = self.execute_fake()
        self.assertEqual(code, 2)
        self.assertEqual(seen, [None, 5000, 10000])
        self.assertTrue(receipt["experiment_valid"])
        self.assertFalse(receipt["all_budgets_accepted"])

    def test_query_error_stops_later_budget(self):
        code, receipt, seen = self.execute_fake(first_failure=True)
        self.assertEqual(code, 1)
        self.assertEqual(seen, [None, 5000])
        self.assertEqual(receipt["skipped_budgets_ms"], [10000])

    def test_input_drift_invalidates_clean_processes(self):
        code, receipt, seen = self.execute_fake(drift=True)
        self.assertEqual(code, 1)
        self.assertEqual(seen, [None, 5000, 10000])
        self.assertFalse(receipt["experiment_valid"])
        self.assertFalse(receipt["inputs_unchanged"])


if __name__ == "__main__":
    unittest.main()
