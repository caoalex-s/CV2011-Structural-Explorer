"""Audit parser controls; no Lean/runtime execution."""
import unittest
from pathlib import Path
import subprocess
import sys
import tempfile
from audit import audit, INCLINED_FOUNDATION_MODULES, INCLINED_INTEGRATION_MODULES, INCLINED_ASSEMBLY_MODULES, INCLINED_OUTPUT_MODULES, INCLINED_PACKET_MODULES

class AxiomAuditTests(unittest.TestCase):
    def test_report_audit_extends_packet_scope_without_replacing_it(self):
        repository = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / 'Audit.lean'
            subprocess.run([sys.executable, str(Path(__file__).with_name('audit.py')),
                            '--inclined-report', '--emit', str(output)], cwd=repository, check=True)
            lines = output.read_text(encoding='utf-8').splitlines()
            imports = [line for line in lines if line.startswith('import ')]
            claims = [line for line in lines if line.startswith('#print axioms ')]
            self.assertEqual(imports[:54], ['import ' + name for name in INCLINED_PACKET_MODULES])
            self.assertEqual(len(imports), 56)
            self.assertEqual(len(claims), len(set(claims)))
            self.assertIn('#print axioms InclinedFrameIntervalReportSound.checkReport_sound', claims)

    def test_packet_audit_binds_successful_returns_to_source_and_query(self):
        repository = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / 'Audit.lean'
            subprocess.run([sys.executable, str(Path(__file__).with_name('audit.py')),
                            '--inclined-packet', '--emit', str(output)], cwd=repository, check=True)
            lines = output.read_text(encoding='utf-8').splitlines()
            imports = [line for line in lines if line.startswith('import ')]
            claims = [line for line in lines if line.startswith('#print axioms ')]
            self.assertEqual(imports, ['import ' + name for name in INCLINED_PACKET_MODULES])
            self.assertEqual(len(imports), 54)
            self.assertEqual(len(claims), len(set(claims)))
            for name in ['InclinedFrameIntervalBuildSound.checked_source_sound',
                         'InclinedFrameIntervalWireSound.checkPacket_sound',
                         'InclinedFrameIntervalWireSound.decodeAndCheck_sound']:
                self.assertIn('#print axioms ' + name, claims)

    def test_output_audit_includes_stability_recovery_and_accuracy(self):
        repository = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / 'Audit.lean'
            subprocess.run([sys.executable, str(Path(__file__).with_name('audit.py')),
                            '--inclined-outputs', '--emit', str(output)], cwd=repository, check=True)
            lines = output.read_text(encoding='utf-8').splitlines()
            imports = [line for line in lines if line.startswith('import ')]
            claims = [line for line in lines if line.startswith('#print axioms ')]
            self.assertEqual(imports, ['import ' + name for name in INCLINED_OUTPUT_MODULES])
            self.assertEqual(len(imports), 50)
            self.assertEqual(len(claims), len(set(claims)))
            for name in ['InclinedFrameIntervalEquilibrium.check_positive_stiffness',
                         'InclinedFrameIntervalRecoverySound.field_contains',
                         'InclinedFrameIntervalReactionsSound.reaction_contains',
                         'FrameIntervalAccuracySound.check_error',
                         'InclinedFrameIntervalOutputsSound.checked_source_outputs']:
                self.assertIn('#print axioms ' + name, claims)

    def test_assembly_audit_keeps_every_dependency_and_physical_conclusion(self):
        repository = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / 'Audit.lean'
            subprocess.run([sys.executable, str(Path(__file__).with_name('audit.py')),
                            '--inclined-assembly', '--emit', str(output)], cwd=repository, check=True)
            lines = output.read_text(encoding='utf-8').splitlines()
            imports = [line for line in lines if line.startswith('import ')]
            claims = [line for line in lines if line.startswith('#print axioms ')]
            self.assertEqual(imports, ['import ' + name for name in INCLINED_ASSEMBLY_MODULES])
            self.assertEqual(len(imports), 38)
            self.assertEqual(len(claims), len(set(claims)))
            for name in ['FrameIntervalSolveSound.check_sound',
                         'InclinedFrameIntervalAssemblySound.check_reduced_solution',
                         'InclinedFrameIntervalEquilibrium.check_physical_equilibrium',
                         'InclinedFrameReduced.positive_physical_stiffness']:
                self.assertIn('#print axioms ' + name, claims)

    def test_integration_audit_includes_source_equilibrium_and_excludes_packet_drafts(self):
        repository = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / 'Audit.lean'
            subprocess.run([sys.executable, str(Path(__file__).with_name('audit.py')),
                            '--inclined-integration', '--emit', str(output)], cwd=repository, check=True)
            lines = output.read_text(encoding='utf-8').splitlines()
            imports = [line for line in lines if line.startswith('import ')]
            claims = [line for line in lines if line.startswith('#print axioms ')]
            self.assertEqual(imports, ['import ' + name for name in INCLINED_INTEGRATION_MODULES])
            self.assertEqual(len(imports), 16)
            self.assertEqual(len(lines), len(imports) + len(claims))
            self.assertEqual(len(claims), len(set(claims)))
            for claim in ['InclinedFrameSource.checkedPartition_source',
                          'InclinedFrameGlobalBasis.range_equals_source_kernel',
                          'InclinedFrameGlobalBasis.columnIndex_injective',
                          'InclinedFrameReduced.checked_source_equilibrium',
                          'InclinedFrameReduced.enclosed_equilibrium',
                          'InclinedFrameReduced.positive_physical_stiffness']:
                self.assertIn('#print axioms ' + claim, claims)
            for excluded in ['FrameIntervalSolve', 'FrameIntervalElement', 'FrameIntervalVector']:
                self.assertFalse(any(excluded in line for line in lines))

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
