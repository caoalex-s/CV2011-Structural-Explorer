"""Audit parser controls; no Lean/runtime execution."""
import unittest
from audit import audit

class AxiomAuditTests(unittest.TestCase):
    def test_requires_all_and_only_source_theorems(self):
        source = 'theorem sound : True := trivial\n'
        good = "'PortalSoundness.sound' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(set(audit(source, good)), {'PortalSoundness.sound'})
        for log in ['', good + '\n' + good, good.replace('Quot.sound', 'sorryAx'), good.replace('sound', 'unrelated'), good + '\nwarning: ignored']:
            with self.assertRaises(ValueError):
                audit(source, log)

if __name__ == '__main__':
    unittest.main()
