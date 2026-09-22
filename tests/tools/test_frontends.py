"""Protocol/fixture regressions only: these tests never invoke Lean or Lake."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import run_frontends as frontend


def message(data, severity="information", line=8):
    return {"data": data, "severity": severity, "pos": {"line": line, "column": 2}}


def stream(*messages):
    return "\n".join(json.dumps(item) for item in messages) + "\n"


class FrontendProtocolTests(unittest.TestCase):
    def setUp(self):
        self.cases = {case["id"]: case for case in frontend.load_cases()}

    def test_exact_inventory_and_fresh_replay_import_boundary(self):
        self.assertEqual(len(self.cases), 8)
        self.assertEqual(sum(bool(c.get("suggestion_replay")) for c in self.cases.values()), 3)
        self.assertEqual(sum(bool(c.get("negative")) for c in self.cases.values()), 2)
        text, _ = frontend.source(self.cases["tactic-local-data"], 5000, "exact f x")
        self.assertTrue(text.startswith("import Lean\n"))
        self.assertNotIn("import Leant2", text)
        self.assertNotIn("leant2.budgetMs", text)
        self.assertNotIn(frontend.HOLE, text)
        self.assertIn("collectAxioms", text)

    def test_theorem_audit_reads_opaque_proofs_and_keeps_sorry_checks(self):
        # These four cases reached a checked theorem in the first native run;
        # ConstantInfo.value? defaults to excluding that proof body.
        for name in ("term-local-context", "tactic-local-proof", "term-false", "tactic-false"):
            with self.subTest(case=name):
                text = frontend.audit_source(self.cases[name])
                self.assertIn("ci.value? (allowOpaque := true)", text)
                self.assertIn("value.hasSorry", text)
                self.assertIn("collectAxioms name", text)
                self.assertIn("frontend result has no checked value", text)

    def successful(self, case, stage="original", suggestion="exact f x"):
        infos = [message(frontend.audit_marker(case))]
        if case.get("observations"):
            infos.append(message(frontend.VALUE_MARKER))
        if stage == "original" and case.get("suggestion_replay"):
            infos.append(message("Try this:\n  " + suggestion))
        return stream(*infos)

    def test_actual_info_text_is_extracted_without_name_rewrite(self):
        case = self.cases["tactic-local-data"]
        result = frontend.classify(case, "original", self.successful(case), "", 0, [8])
        self.assertTrue(result["passed"], result)
        self.assertEqual(result["suggestion"], "exact f x")

    def test_real_lean_apply_widget_label_preserves_tactic_text(self):
        # Actual text from baseline-out/frontend-focused-02.log.
        text = "Try this:\n  [apply] exact (fun A B f => f) A B f a"
        self.assertEqual(frontend.extract_suggestion([message(text)], [8]),
                         "exact (fun A B f => f) A B f a")
        multiline = "Try this:\n  [apply] exact fun x =>\n    let y := x\n    y"
        self.assertEqual(frontend.extract_suggestion([message(multiline)], [8]),
                         "exact fun x =>\n  let y := x\n  y")

    def test_suggestion_does_not_strip_arbitrary_prefixes(self):
        for prefix in ("[accept] ", "[apply-all] ", "[apply] [apply] ", "note: ", "[apply]\n"):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                frontend.extract_suggestion([message("Try this:\n  " + prefix + "exact f x")], [8])

    def test_candidate_or_marker_followed_by_error_is_failure(self):
        case = self.cases["tactic-local-data"]
        stdout = self.successful(case) + stream(message("type mismatch", "error"))
        self.assertFalse(frontend.classify(case, "original", stdout, "", 0, [8])["passed"])

    def test_missing_marker_runtime_result_or_process_integrity_fails(self):
        case = self.cases["term-local-context"]
        good = self.successful(case)
        variants = [("", "", 0), (good, "warning from runtime", 0), (good, "", 1),
                    (stream(message(frontend.audit_marker(case))), "", 0), (good + "not-json\n", "", 0)]
        for stdout, stderr, code in variants:
            with self.subTest(stdout=stdout, stderr=stderr, code=code):
                self.assertFalse(frontend.classify(case, "original", stdout, stderr, code, [8])["passed"])

    def test_duplicate_wrong_line_or_unchecked_suggestion_fails(self):
        case = self.cases["tactic-local-data"]
        good = self.successful(case)
        self.assertFalse(frontend.classify(case, "original", good, "", 0, [9])["passed"])
        duplicate = good + stream(message("Try this: exact x"))
        self.assertFalse(frontend.classify(case, "original", duplicate, "", 0, [8])["passed"])
        for term in ("exact sorry", "exact _leant2_compiled.map x", "exact synth%", "refine ?_"):
            result = frontend.classify(case, "original", self.successful(case, suggestion=term), "", 0, [8])
            self.assertFalse(result["passed"], term)

    def test_recursive_display_must_be_independent_source(self):
        case = self.cases["tactic-indexed-map"]
        bad = self.successful(case, suggestion="exact FrontendCase.Vec.rec _ _")
        self.assertFalse(frontend.classify(case, "original", bad, "", 0, [8])["passed"])
        good = self.successful(case, suggestion="exact fun xs => match xs with | .nil => .nil")
        self.assertTrue(frontend.classify(case, "original", good, "", 0, [8])["passed"])
        # Syntactic extraction alone never establishes validity: fresh Lean replay
        # is required by the runner and this deliberately incomplete snippet fails there.

    def test_negative_requires_specific_error_and_correct_exit(self):
        case = self.cases["term-false"]
        good = stream(message(frontend.FAILURE_PREFIX + " no accepted result", "error", 3))
        self.assertTrue(frontend.classify(case, "negative-error", good, "", 1, [3])["passed"])
        for text, code in ((good, 0), (good, -9), (good, None),
                           (stream(message("Unknown identifier synth%", "error", 3)), 1)):
            self.assertFalse(frontend.classify(case, "negative-error", text, "", code, [3])["passed"])

    def test_top_level_recovery_warning_is_only_allowed_in_failed_file(self):
        case = self.cases["term-false"]
        error = message(frontend.FAILURE_PREFIX + " no accepted result", "error", 3)
        warning = message("declaration uses 'sorry'", "warning", 3)
        self.assertTrue(frontend.classify(case, "negative-error", stream(error, warning), "", 1, [3])["passed"])
        outer = self.successful(case) + stream(warning)
        self.assertFalse(frontend.classify(case, "original", outer, "", 0, [8])["passed"])

    def test_failed_outer_negative_cannot_be_saved_by_error_substage(self):
        case = self.cases["tactic-false"]
        self.assertFalse(frontend.classify(case, "original", "", "", 0, [8])["passed"])
        bad = self.successful(case) + stream(message("Try this: exact False.elim h"))
        self.assertFalse(frontend.classify(case, "original", bad, "", 0, [8])["passed"])

    def test_replay_stage_cannot_invoke_frontend_again(self):
        case = self.cases["tactic-local-data"]
        good = self.successful(case, stage="suggestion-replay")
        self.assertTrue(frontend.classify(case, "suggestion-replay", good, "", 0, [8])["passed"])
        self.assertFalse(frontend.classify(case, "suggestion-replay", self.successful(case), "", 0, [8])["passed"])

    def test_fingerprints_include_interpreter_and_private_artifacts_and_new_source(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            folder = root / ".lake/build/lib/lean/Leant2"
            folder.mkdir(parents=True)
            for suffix in (".olean", ".olean.private", ".olean.server", ".ir", ".trace"):
                (folder / ("New" + suffix)).write_bytes(suffix.encode())
            (root / "Leant2").mkdir()
            (root / "Leant2/New.lean").write_text("-- new untracked source", encoding="utf-8")
            (root / "lean-toolchain").write_text("leanprover/lean4:test", encoding="utf-8")
            with patch.object(frontend, "ROOT", root):
                modules = frontend.module_hashes()
                sources = frontend.source_hashes()
            self.assertEqual(len(modules), 4)
            self.assertTrue(any(name.endswith(".ir") for name in modules))
            self.assertTrue(any(name.endswith(".olean.private") for name in modules))
            self.assertTrue(any(name.endswith(".olean.server") for name in modules))
            self.assertIn("Leant2/New.lean", sources)
            self.assertIn("lean-toolchain", sources)


if __name__ == "__main__":
    unittest.main()
