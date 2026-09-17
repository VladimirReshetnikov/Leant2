"""Offline synthetic-response tests; no Lean/compiler/network execution occurs."""
import copy
import unittest

from check_remote import validate


class ResponseValidationTests(unittest.TestCase):
    def setUp(self):
        self.source = "import Lean\n#print axioms Foo\n"
        self.response = {
            "okay": True, "failed_declarations": [], "content": self.source + "\n",
            "lean_messages": {"errors": [], "warnings": [],
                              "infos": ["info: 'Foo' does not depend on any axioms\n"]},
            "tool_messages": {"errors": [], "warnings": []},
        }

    def result(self, response):
        return validate(self.source, response, {"propext", "Quot.sound"})["passed"]

    def test_accepts_axiom_free_with_trailing_newline(self):
        self.assertTrue(self.result(self.response))

    def test_accepts_qualified_name_and_allowed_axioms(self):
        self.response["lean_messages"]["infos"] = [
            "info: 'Namespace.Foo' depends on axioms: [propext, Quot.sound]"
        ]
        self.assertTrue(self.result(self.response))

    def test_rejects_import_replacement(self):
        self.response["content"] = self.source.replace("import Lean", "import Mathlib")
        self.assertFalse(self.result(self.response))

    def test_rejects_missing_report(self):
        self.response["lean_messages"]["infos"] = []
        self.assertFalse(self.result(self.response))

    def test_rejects_anonymous_sorry_warning(self):
        self.response["lean_messages"]["warnings"] = ["declaration uses `sorry`"]
        self.assertFalse(self.result(self.response))

    def test_rejects_disallowed_choice(self):
        self.response["lean_messages"]["infos"] = [
            "info: 'Foo' depends on axioms: [Classical.choice]"
        ]
        self.assertFalse(self.result(self.response))

    def test_rejects_errors_even_with_okay_true(self):
        self.response["lean_messages"]["errors"] = ["example failed"]
        self.assertFalse(self.result(self.response))

    def test_rejects_failed_declarations(self):
        self.response["failed_declarations"] = ["Foo"]
        self.assertFalse(self.result(self.response))


if __name__ == "__main__":
    unittest.main()
