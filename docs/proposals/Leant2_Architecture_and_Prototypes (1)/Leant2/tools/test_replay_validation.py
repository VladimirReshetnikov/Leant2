#!/usr/bin/env python3
"""Offline unit tests of the receipt validator; these do NOT run Lean."""
import copy
import unittest
from replay_axle import validate_response

SOURCE = 'import Lean\nexample : True := by trivial\n'
EXPECTED = {'Example.good': []}

def fixture():
    return {'okay': True, 'failed_declarations': [], 'content': SOURCE + '\n',
            'lean_messages': {'errors': [], 'warnings': [],
                'infos': ["-:1:0: info: 'Example.good' does not depend on any axioms\n",
                          '-:2:0: info: "4.34.0"\n']},
            'tool_messages': {'errors': [], 'warnings': [], 'infos': []},
            'info': {'environment': 'lean-4.34.0', 'request_id': 'synthetic'}}

class ValidationTests(unittest.TestCase):
    def check(self, p):
        return validate_response(p, SOURCE, EXPECTED, 'lean-4.34.0')
    def test_success(self):
        self.assertTrue(self.check(fixture())['passed'])
    def test_failures(self):
        cases = []
        p = fixture(); p['okay'] = False; cases.append(p)
        p = fixture(); p['failed_declarations'] = ['x']; cases.append(p)
        p = fixture(); p['content'] = 'import Mathlib\n'; cases.append(p)
        p = fixture(); p['lean_messages']['errors'] = ['error']; cases.append(p)
        p = fixture(); p['tool_messages']['errors'] = ['error']; cases.append(p)
        p = fixture(); p['lean_messages']['warnings'] = ["declaration uses 'sorry'"]; cases.append(p)
        p = fixture(); p['lean_messages']['infos'][0] = "'Example.good' depends on axioms: [sorryAx]"; cases.append(p)
        p = fixture(); p['lean_messages']['infos'] = []; cases.append(p)
        p = fixture(); p['lean_messages']['infos'] *= 2; cases.append(p)
        p = fixture(); p['info']['environment'] = 'other'; cases.append(p)
        p = fixture(); del p['tool_messages']; cases.append(p)
        for i, p in enumerate(cases):
            with self.subTest(i=i), self.assertRaises(ValueError):
                self.check(p)

if __name__ == '__main__':
    unittest.main(verbosity=2)
