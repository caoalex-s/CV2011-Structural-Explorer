"""Audit-only tests: forbidden/missing evidence must not reach the runtime gate."""
import ast
from pathlib import Path
import unittest
from unittest.mock import patch

import audit_axioms

from audit_axioms import ALLOWED_AXIOMS, EXPECTED_THEOREMS, audit_reports

SOUND = "'WasmSmoke.accepts_sound' depends on axioms: [propext, Classical.choice, Quot.sound]"
COMPLETE = "'WasmSmoke.accepts_complete' depends on axioms: [propext]"
VALID = SOUND + "\n" + COMPLETE + "\n"

# Exact report from CI run 43444800755, frame-axioms.log. Only its layout
# differs from the previous single-line format; retain every dependency.
WRAPPED_NAME = 'RationalFrame.Interpretation.segment_load_from_piecewise_source'
WRAPPED = """'RationalFrame.Interpretation.segment_load_from_piecewise_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]"""


class AxiomAuditChecks(unittest.TestCase):
    def test_actual_archived_wrapped_report(self):
        expected = {WRAPPED_NAME, 'WasmSmoke.accepts_complete'}
        with patch.object(audit_axioms, 'EXPECTED_THEOREMS', expected):
            reports = audit_reports(WRAPPED + '\n' + COMPLETE)
        self.assertEqual(set(reports), expected)
        self.assertEqual(set(reports[WRAPPED_NAME]), ALLOWED_AXIOMS)

    def test_wrapped_reports_reject_incomplete_or_extra_evidence(self):
        valid = WRAPPED + '\n' + COMPLETE
        malformed = [
            WRAPPED,  # Missing required theorem.
            valid.replace('Quot.sound]', 'Quot.sound'),  # Truncated list.
            valid + '\ntrailing garbage',
            valid.replace('Quot.sound]', 'Quot.sound] extra'),
            valid.replace('propext,\n', 'propext\n'),  # Missing comma.
            valid.replace('Classical.choice,', 'Classical.choice,,'),
            valid.replace('[propext,', '[[propext,'),
            valid.replace('Quot.sound]', 'Quot.sound]]'),
            valid.replace('Quot.sound]', 'Quot.sound,]'),
            valid.replace('Quot.sound', 'sorryAx'),
            valid.replace('Quot.sound', 'Lean.ofReduceBool'),
            valid.replace('Quot.sound', 'Unreviewed.assumption'),
            valid.replace('Quot.sound', 'propext'),  # Duplicate axiom.
            valid + '\n' + WRAPPED,  # Duplicate theorem.
            valid.replace(WRAPPED_NAME, 'Other.unknown'),
            WRAPPED + COMPLETE,  # Missing report separator.
            valid.replace(' Classical.choice,', "'Other.sound' depends on axioms: [propext]"),
        ]
        with patch.object(audit_axioms, 'EXPECTED_THEOREMS', {WRAPPED_NAME, 'WasmSmoke.accepts_complete'}):
            for log in malformed:
                with self.subTest(log=log), self.assertRaises(ValueError):
                    audit_reports(log)

    def test_recorded_standard_reports_pass(self):
        reports = audit_reports(VALID)
        self.assertEqual(set(reports), EXPECTED_THEOREMS)
        self.assertEqual(set(reports["WasmSmoke.accepts_sound"]), ALLOWED_AXIOMS)

    def test_axiom_free_report_passes_existing_policy(self):
        log = VALID.replace("depends on axioms: [propext]", "does not depend on any axioms")
        self.assertEqual(audit_reports(log)["WasmSmoke.accepts_complete"], [])

    def test_allowlist_matches_existing_real_field_policy(self):
        root = Path(__file__).resolve().parents[2]
        tree = ast.parse((root / "scripts/audit_real_axioms.py").read_text(encoding="utf-8"))
        assignment = next(node for node in tree.body if isinstance(node, ast.Assign)
                          and any(isinstance(target, ast.Name) and target.id == "ALLOWED"
                                  for target in node.targets))
        self.assertEqual(ALLOWED_AXIOMS, ast.literal_eval(assignment.value))

    def test_forbidden_axioms_rejected(self):
        for axiom in ("sorryAx", "Lean.ofReduceBool", "Unreviewed.assumption"):
            with self.subTest(axiom=axiom), self.assertRaisesRegex(ValueError, "Unapproved axioms"):
                audit_reports(VALID.replace("Quot.sound", axiom))

    def test_missing_reports_rejected(self):
        for log in ("", SOUND, COMPLETE):
            with self.subTest(log=log), self.assertRaisesRegex(ValueError, "Missing theorem"):
                audit_reports(log)

    def test_duplicate_or_unknown_reports_rejected(self):
        for log in (VALID + SOUND, VALID + "'Other.sound' depends on axioms: [propext]",
                    VALID.replace("WasmSmoke.accepts_complete", "WasmSmoke.unknown")):
            with self.subTest(log=log), self.assertRaisesRegex(ValueError, "Repeated|Unexpected"):
                audit_reports(log)

    def test_malformed_or_warning_output_rejected(self):
        malformed = [VALID.replace("[propext]", "[propext,]"),
                     VALID.replace("[propext]", "[propext, propext]"),
                     VALID.replace("[propext]", "[propext] trailing text"),
                     VALID + "warning: declaration uses sorry\n",
                     VALID.replace("depends on axioms: [propext]", "unrecognized report")]
        for log in malformed:
            with self.subTest(log=log), self.assertRaises(ValueError):
                audit_reports(log)


if __name__ == "__main__":
    unittest.main()
