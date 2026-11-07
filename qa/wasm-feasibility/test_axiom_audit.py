"""Audit-only tests: forbidden/missing evidence must not reach the runtime gate."""
import ast
from pathlib import Path
import unittest

from audit_axioms import ALLOWED_AXIOMS, EXPECTED_THEOREMS, audit_reports

SOUND = "'WasmSmoke.accepts_sound' depends on axioms: [propext, Classical.choice, Quot.sound]"
COMPLETE = "'WasmSmoke.accepts_complete' depends on axioms: [propext]"
VALID = SOUND + "\n" + COMPLETE + "\n"


class AxiomAuditChecks(unittest.TestCase):
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
