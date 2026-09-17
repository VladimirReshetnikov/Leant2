"""Offline tests of the client response parser, not Lean verification tests."""
from copy import deepcopy
import unittest
from check_axle import audit_response

class ResponseAuditTests(unittest.TestCase):
    def setUp(self):
        self.source = "import Lean\nexample : True := True.intro\n"
        self.response = {
            'okay': True, 'failed_declarations': [], 'content': self.source + '\n',
            'lean_messages': {'errors': [], 'warnings': [],
                              'infos': ["-:1:0: info: 'test' does not depend on any axioms\n"]},
            'tool_messages': {'errors': [], 'warnings': []},
            'info': {'environment': 'lean-4.34.0'}}
    def check(self, response, allowed=None):
        return audit_response(response, self.source, {'test': []} if allowed is None else allowed,
                              'lean-4.34.0')['accepted_by_response_audit']
    def test_clean(self): self.assertTrue(self.check(self.response))
    def test_no_manifest(self): self.assertFalse(self.check(self.response, {}))
    def test_missing_audit(self):
        self.response['lean_messages']['infos'] = []
        self.assertFalse(self.check(self.response))
    def test_duplicate_audit(self):
        self.response['lean_messages']['infos'] *= 2
        self.assertFalse(self.check(self.response))
    def test_sorry(self):
        self.response['lean_messages']['infos'] = ["'test' depends on axioms: [sorryAx]"]
        self.assertFalse(self.check(self.response))
    def test_custom_axiom(self):
        self.response['lean_messages']['infos'] = ["'test' depends on axioms: [forged]"]
        self.assertFalse(self.check(self.response))
    def test_approved_axiom(self):
        self.response['lean_messages']['infos'] = ["'test' depends on axioms: [propext]"]
        self.assertTrue(self.check(self.response, {'test': ['propext']}))
    def test_failed_declaration(self):
        self.response['failed_declarations'] = ['test']
        self.assertFalse(self.check(self.response))
    def test_changed_source(self):
        self.response['content'] = self.source.replace('True', 'False')
        self.assertFalse(self.check(self.response))
    def test_environment(self):
        self.response['info']['environment'] = 'other'
        self.assertFalse(self.check(self.response))
    def test_compiler_error(self):
        self.response['lean_messages']['errors'] = ['error']
        self.assertFalse(self.check(self.response))
    def test_service_error(self):
        self.response['tool_messages']['errors'] = ['error']
        self.assertFalse(self.check(self.response))
    def test_incomplete_warning(self):
        self.response['lean_messages']['warnings'] = ['declaration uses sorry']
        self.assertFalse(self.check(self.response))
    def test_okay_false(self):
        self.response['okay'] = False
        self.assertFalse(self.check(self.response))

if __name__ == '__main__': unittest.main()
