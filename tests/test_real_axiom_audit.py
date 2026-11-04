"""Check the real-proof axiom gate against missing and unapproved reports."""
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "proofs"
AUDITOR = ROOT / "scripts" / "audit_real_axioms.py"


class RealAxiomAuditTests(unittest.TestCase):
    def test_requires_every_report_and_rejects_unapproved_axioms(self):
        names = re.findall(r"^theorem\s+(\w+)", (PROOFS / "RealBeamFields.lean").read_text(encoding="utf-8"), re.MULTILINE)
        reports = [f"'RealBeamFields.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in names]
        scratch = ROOT / ".data"
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as folder:
            logfile = Path(folder) / "axioms.log"
            def run(lines):
                logfile.write_text("\n".join(lines), encoding="utf-8")
                return subprocess.run([sys.executable, str(AUDITOR), str(logfile)], cwd=PROOFS,
                                      capture_output=True, text=True, check=False)
            self.assertEqual(run(reports).returncode, 0)
            self.assertNotEqual(run(reports[:-1]).returncode, 0)
            bad = reports.copy()
            bad[0] = bad[0].replace("propext", "sorryAx")
            self.assertNotEqual(run(bad).returncode, 0)


if __name__ == "__main__":
    unittest.main()
