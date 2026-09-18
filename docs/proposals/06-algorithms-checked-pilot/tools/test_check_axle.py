"""Offline regression tests for the replay client's response checks, not Lean tests."""
import copy
import unittest
from check_axle import assess

SOURCE = "import Lean\n"
GOOD = {"okay": True, "content": SOURCE + "\n", "failed_declarations": [],
        "lean_messages": {"errors": [], "warnings": [],
                          "infos": ["'Example.term' does not depend on any axioms"]},
        "tool_messages": {"errors": [], "warnings": ["Non-default header advisory"]}}

class AssessmentTests(unittest.TestCase):
    def test_exact_success(self):
        self.assertTrue(assess(SOURCE, GOOD, {"Example.term": []})["pass"])
    def test_header_replaced(self):
        r = copy.deepcopy(GOOD); r["content"] = "import Mathlib\n"
        self.assertFalse(assess(SOURCE, r)["pass"])
    def test_anonymous_sorry(self):
        r = copy.deepcopy(GOOD); r["lean_messages"]["warnings"] = ["declaration uses `sorry`"]
        self.assertFalse(assess(SOURCE, r)["pass"])
    def test_named_failure(self):
        r = copy.deepcopy(GOOD); r["failed_declarations"] = ["bad"]
        self.assertFalse(assess(SOURCE, r)["pass"])
    def test_no_axiom_report(self):
        self.assertFalse(assess(SOURCE, GOOD, {"Missing": []})["pass"])
    def test_changed_axioms(self):
        r = copy.deepcopy(GOOD); r["lean_messages"]["infos"] = ["'Example.term' depends on axioms: [propext]"]
        self.assertFalse(assess(SOURCE, r, {"Example.term": []})["pass"])
        self.assertTrue(assess(SOURCE, r, {"Example.term": ["propext"]})["pass"])
    def test_ordinary_compile_failure(self):
        r = copy.deepcopy(GOOD); r["okay"] = False; r["lean_messages"]["errors"] = ["type mismatch"]
        self.assertFalse(assess(SOURCE, r)["pass"])
    def test_specific_expected_rejection(self):
        r = copy.deepcopy(GOOD); r["okay"] = False
        r["lean_messages"]["errors"] = ["code generator does not support recursor `PilotTree.rec` yet"]
        self.assertTrue(assess(SOURCE, r, expected_compiler_error="does not support recursor")["pass"])
        self.assertFalse(assess(SOURCE, GOOD, expected_compiler_error="does not support recursor")["pass"])
    def test_wrong_failure(self):
        r = copy.deepcopy(GOOD); r["okay"] = False; r["lean_messages"]["errors"] = ["unknown identifier"]
        self.assertFalse(assess(SOURCE, r, expected_compiler_error="does not support recursor")["pass"])
    def test_service_error(self):
        r = copy.deepcopy(GOOD); r["user_error"] = "Unknown environment"
        self.assertFalse(assess(SOURCE, r)["pass"])
    def test_validation_error(self):
        r = copy.deepcopy(GOOD); r["tool_messages"]["errors"] = ["incomplete declaration"]
        self.assertFalse(assess(SOURCE, r)["pass"])

if __name__ == "__main__":
    unittest.main()
