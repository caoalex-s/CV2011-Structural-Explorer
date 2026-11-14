"""Audit parser controls; no Lean/runtime execution."""
import unittest
from pathlib import Path
import subprocess
import sys
import tempfile
from audit import audit, INCLINED_FOUNDATION_MODULES

class AxiomAuditTests(unittest.TestCase):
    def test_foundation_audit_is_explicit_and_excludes_later_drafts(self):
        repository = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / 'Audit.lean'
            subprocess.run([sys.executable, str(Path(__file__).with_name('audit.py')),
                            '--inclined-foundation', '--emit', str(output)], cwd=repository, check=True)
            lines = output.read_text(encoding='utf-8').splitlines()
            imports = [line for line in lines if line.startswith('import ')]
            claims = [line for line in lines if line.startswith('#print axioms ')]
            self.assertEqual(imports, ['import ' + name for name in INCLINED_FOUNDATION_MODULES])
            self.assertEqual(len(imports), 8)
            self.assertEqual(len(lines), len(imports) + len(claims))
            self.assertEqual(len(claims), len(set(claims)))
            for claim in ['FrameIntervalTrigSound.degreeAxesGeneral_contains',
                          'FrameIntervalGeometrySound.original_endpoints',
                          'FrameAdmissiblePoint.all_distinct_classes_kernel',
                          'FrameReducedStability.positive_of_psd_nondegenerate']:
                self.assertIn('#print axioms ' + claim, claims)
            self.assertFalse(any('FrameResidualBound' in line or 'InclinedFrameSource' in line for line in lines))

    def test_requires_all_and_only_source_theorems(self):
        source = 'theorem sound : True := trivial\n'
        good = "'PortalSoundness.sound' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(set(audit(source, good)), {'PortalSoundness.sound'})
        for log in ['', good + '\n' + good, good.replace('Quot.sound', 'sorryAx'), good.replace('sound', 'unrelated'), good + '\nwarning: ignored']:
            with self.assertRaises(ValueError):
                audit(source, log)

    def test_emitted_audits_preserve_original_print_commands(self):
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
                self.assertEqual(lines[0], f'import {imported}')
                self.assertIn('#print axioms ' + required, lines[1:])
                self.assertTrue(all(line.startswith('#print axioms ') for line in lines[1:]))
                self.assertEqual(len(lines[1:]), len(set(lines[1:])))

    def test_long_theorem_report_preserves_strict_dependency_validation(self):
        name = 'segment_load_from_piecewise_source'
        source = f'theorem {name} : True := trivial\n'
        report = f"'PortalSoundness.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(audit(source, report)['PortalSoundness.' + name],
                         ['Classical.choice', 'Quot.sound', 'propext'])
        self.assertEqual(audit(source, report), audit(source, report.replace(', ', ',\n ')))
        for invalid in [report.replace('Quot.sound', 'sorryAx'), report[:-1]]:
            with self.assertRaises(ValueError):
                audit(source, invalid)

if __name__ == '__main__':
    unittest.main()
