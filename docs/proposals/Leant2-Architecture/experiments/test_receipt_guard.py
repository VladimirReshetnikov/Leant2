#!/usr/bin/env python3
"""Local unit tests of the AXLE response guard; fixtures are synthetic."""
import copy
import unittest
from check_axle import validate_reply


class ReceiptGuardTests(unittest.TestCase):
    def setUp(self):
        self.source = 'import Lean\n'
        self.expected = {'Example.good'}
        self.reply = {
            'okay': True, 'content': self.source + '\n', 'failed_declarations': [],
            'lean_messages': {'errors': [], 'warnings': [], 'infos': [
                "info: 'Example.good' does not depend on any axioms\n"]},
            'tool_messages': {'errors': []},
        }

    def check(self, reply):
        return validate_reply(reply, self.source, self.expected, {'propext'})

    def test_valid(self):
        self.assertEqual(self.check(self.reply), [])

    def test_sorry(self):
        self.reply['lean_messages']['infos'] = [
            "info: 'Example.good' depends on axioms: [sorryAx]"]
        self.assertTrue(self.check(self.reply))

    def test_missing_audit(self):
        self.reply['lean_messages']['infos'] = []
        self.assertTrue(self.check(self.reply))

    def test_changed_source(self):
        self.reply['content'] = 'import Mathlib\n'
        self.assertTrue(self.check(self.reply))

    def test_failed_declaration(self):
        self.reply['failed_declarations'] = ['Example.good']
        self.assertTrue(self.check(self.reply))

    def test_lean_error(self):
        self.reply['lean_messages']['errors'] = ['unsolved goals']
        self.assertTrue(self.check(self.reply))

    def test_allow_propext_but_not_empty_profile(self):
        self.reply['lean_messages']['infos'] = [
            "info: 'Example.good' depends on axioms: [propext]"]
        self.assertEqual(self.check(self.reply), [])
        self.assertTrue(validate_reply(self.reply, self.source, self.expected, set()))

    def test_okay_false(self):
        self.reply['okay'] = False
        self.assertTrue(self.check(self.reply))

    def test_no_expected_refuses_vacuous_success(self):
        self.assertTrue(validate_reply(self.reply, self.source, set(), {'propext'}))


if __name__ == '__main__':
    unittest.main(verbosity=2)
