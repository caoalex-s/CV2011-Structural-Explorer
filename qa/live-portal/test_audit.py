"""Audit parser controls; no Lean/runtime execution."""
import unittest
from pathlib import Path
import subprocess
import sys
import tempfile
from audit import audit

class AxiomAuditTests(unittest.TestCase):
    def test_requires_all_and_only_source_theorems(self):
        source = 'theorem sound : True := trivial\n'
        good = "'PortalSoundness.sound' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(set(audit(source, good)), {'PortalSoundness.sound'})
        for log in ['', good + '\n' + good, good.replace('Quot.sound', 'sorryAx'), good.replace('sound', 'unrelated'), good + '\nwarning: ignored']:
            with self.assertRaises(ValueError):
                audit(source, log)

    def test_emitted_audits_keep_complete_reports_on_one_line(self):
        repository = Path(__file__).resolve().parents[2]
        for arguments, imported, required in [
            ([], 'PortalSoundness', 'PortalSoundness.acceptance_actual_portal'),
            (['--frame'], 'RationalFrameSoundness',
             'RationalFrame.Interpretation.segment_load_from_piecewise_source'),
        ]:
            with self.subTest(imported=imported), tempfile.TemporaryDirectory() as folder:
                output = Path(folder) / 'Audit.lean'
                subprocess.run([sys.executable, str(Path(__file__).with_name('audit.py')),
                                *arguments, '--emit', str(output)], cwd=repository, check=True)
                lines = output.read_text(encoding='utf-8').splitlines()
                self.assertEqual(lines[:2], [f'import {imported}', 'set_option pp.width 1000'])
                self.assertIn('#print axioms ' + required, lines[2:])
                self.assertTrue(all(line.startswith('#print axioms ') for line in lines[2:]))
                self.assertEqual(len(lines[2:]), len(set(lines[2:])))

    def test_long_theorem_report_preserves_strict_dependency_validation(self):
        name = 'segment_load_from_piecewise_source'
        source = f'theorem {name} : True := trivial\n'
        report = f"'PortalSoundness.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(audit(source, report)['PortalSoundness.' + name],
                         ['Classical.choice', 'Quot.sound', 'propext'])
        for invalid in [report.replace('Quot.sound', 'sorryAx'), report[:-1],
                        report.replace(', Classical.choice', ',\n Classical.choice')]:
            with self.assertRaises(ValueError):
                audit(source, invalid)

if __name__ == '__main__':
    unittest.main()
