"""Pure Python fixture checks; Lean reference validation and synthesis are separate gates."""
import importlib.util
from pathlib import Path
import unittest

ROOT = next(parent for parent in Path(__file__).resolve().parents if (parent / "tools/run_extended.py").is_file())
SPEC = importlib.util.spec_from_file_location("tree_extended", ROOT / "tools/run_extended.py")
HARNESS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(HARNESS)
MANIFEST = Path(__file__).with_name("tree-composition.json")


class TreeCompositionFixtures(unittest.TestCase):
    def setUp(self):
        self.cases = HARNESS.load_cases(MANIFEST)

    def test_original_query_is_preserved_verbatim(self):
        original = next(case for case in HARNESS.load_cases(ROOT / "tests/benchmarks/extended.json")
                        if case["id"] == "probe11_tree_inorder")
        case = self.cases[0]
        for field in ("prelude", "type", "contract"):
            self.assertEqual(case[field], original[field])
        query = next(line for line in HARNESS.transcript(case).splitlines() if line.startswith(":synth"))
        original_query = next(line for line in HARNESS.transcript(original).splitlines() if line.startswith(":synth"))
        self.assertEqual(query, original_query)

    def test_three_cases_include_two_different_recursive_shapes_and_false(self):
        self.assertEqual(len(self.cases), 3)
        self.assertEqual([case["expect"] for case in self.cases], ["candidate", "candidate", "none"])
        self.assertIn("leaf : ExtendedTree A", self.cases[0]["prelude"])
        self.assertIn("tip : Nat → CompositionLeafTree", self.cases[1]["prelude"])
        self.assertIn("fork : CompositionLeafTree → CompositionLeafTree → CompositionLeafTree", self.cases[1]["prelude"])
        self.assertEqual(self.cases[2]["contract"], "False")
        self.assertEqual(self.cases[2]["type"], self.cases[0]["type"])

    def test_reference_and_universal_obligations_are_withheld_until_replay(self):
        for case in self.cases[:2]:
            transcript = HARNESS.transcript(case)
            query_start = transcript.index(":synth")
            query = next(line for line in transcript.splitlines() if line.startswith(":synth"))
            self.assertEqual(transcript.count(":synth"), 1)
            self.assertNotIn(case["reference"], transcript)
            self.assertNotIn("def reference", transcript)
            self.assertNotIn("∀", query)
            self.assertEqual(len(case["kernel_checks"]), 2)
            self.assertNotEqual(case["replay"], case["contract"])
            for check in case["kernel_checks"]:
                rendered = check["type"].replace("{f}", "it1")
                self.assertGreater(transcript.index("example : " + rendered), query_start)
                self.assertNotIn("decide", check["proof"])
                self.assertIn("reference_proof", check)
            for forbidden in case["forbidden_providers"]:
                self.assertLess(transcript.index(f"providers.contains `{forbidden}"), query_start)
            self.assertNotIn("List.append", case["forbidden_providers"])
            self.assertIn(f"example : {case['type']} := it1", transcript)

    def test_equations_require_both_recursive_results_in_order(self):
        inorder = self.cases[0]["kernel_checks"][1]["type"]
        self.assertEqual(inorder, "∀ (l r : ExtendedTree Nat) (x : Nat), {f} (.node l x r) = {f} l ++ (x :: {f} r)")
        leaf_tree = self.cases[1]["kernel_checks"]
        self.assertEqual(leaf_tree[0]["type"], "∀ x : Nat, {f} (.tip x) = [x]")
        self.assertEqual(leaf_tree[1]["type"], "∀ l r : CompositionLeafTree, {f} (.fork l r) = {f} l ++ {f} r")

    def test_fixture_validation_contains_explicit_reference_equations(self):
        source = HARNESS.fixture_source(self.cases)
        self.assertEqual(source.count("def reference :"), 2)
        for case in self.cases[:2]:
            self.assertIn(f"def reference : {case['type']} := {case['reference']}", source)
            for check in case["kernel_checks"]:
                self.assertIn("example : " + check["type"].replace("{f}", "reference") + " := " +
                              check["reference_proof"].replace("{f}", "reference"), source)
        self.assertNotIn("Fixture_composition_tree_false", source)


if __name__ == "__main__":
    unittest.main()
