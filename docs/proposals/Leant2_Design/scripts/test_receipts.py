"""Unit tests of validation logic with synthetic replies (not Lean experiments)."""
from __future__ import annotations

import copy
import unittest

from check_remote import expected_audits, validate


class ReceiptTests(unittest.TestCase):
    def setUp(self) -> None:
        self.source = "import Lean\nnamespace Demo\n#print axioms a\n#print axioms b\nend Demo\n"
        self.names = expected_audits(self.source)
        self.reply = {
            "okay": True,
            "failed_declarations": [],
            "content": self.source,
            "lean_messages": {
                "errors": [], "warnings": [],
                "infos": ["'Demo.a' does not depend on any axioms",
                          "'Demo.b' depends on axioms: [propext]"],
            },
            "tool_messages": {"errors": [], "warnings": []},
        }

    def verdict(self, reply: dict) -> list[str]:
        return validate(reply, self.source, self.names, {"propext"})[0]

    def test_valid_inventory(self) -> None:
        self.assertEqual(self.names, ["Demo.a", "Demo.b"])
        self.assertEqual(self.verdict(self.reply), [])

    def test_missing_audit_rejected(self) -> None:
        self.reply["lean_messages"]["infos"].pop()
        self.assertTrue(self.verdict(self.reply))

    def test_disallowed_axiom(self) -> None:
        self.reply["lean_messages"]["infos"][1] = "'Demo.b' depends on axioms: [sorryAx]"
        self.assertTrue(self.verdict(self.reply))

    def test_changed_source(self) -> None:
        self.reply["content"] = self.source.replace("import Lean", "import Mathlib")
        self.assertTrue(self.verdict(self.reply))

    def test_sorry_warning(self) -> None:
        self.reply["lean_messages"]["warnings"] = ["declaration uses `sorry`"]
        self.assertTrue(self.verdict(self.reply))

    def test_failed_declaration(self) -> None:
        self.reply["failed_declarations"] = ["Demo.a"]
        self.assertTrue(self.verdict(self.reply))

    def test_false_successflag(self) -> None:
        self.reply["okay"] = False
        self.assertTrue(self.verdict(self.reply))

    def test_missing_echo(self) -> None:
        del self.reply["content"]
        self.assertTrue(self.verdict(self.reply))


if __name__ == "__main__":
    unittest.main()
