"""CI-only Lean checks for the generic lesson library, including false claims.

Local execution stays disabled unless REQUIRE_LEAN explicitly opts into the
existing verified runtime. The project runs this on the Linux CI worker.
"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PROOFS = Path(__file__).resolve().parents[1] / "proofs"


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class LessonProofChecks(unittest.TestCase):
    def compile_example(self, statement):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "LessonCheck.lean"
            source.write_text("import StructuralProofs\n" + statement + "\n", encoding="utf-8")
            return subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=PROOFS,
                capture_output=True, text=True, timeout=60, check=False,
            )

    def test_scaled_section_values_and_attained_peak(self):
        result = self.compile_example("""
example : LessonBeam.shear 20 8 4 6 = -80 := by decide
example : LessonBeam.moment 20 8 4 6 = 160 := by decide
example : LessonBeam.moment 20 8 4 4 = 320 := by decide
example : LessonBeam.moment 30 8 2 7 ≤ LessonBeam.peak 30 8 2 :=
  LessonBeam.moment_maximum 30 8 2 7 (by decide) (by decide) (by decide)
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_rejects_wrong_shear_sign_and_wrong_peak(self):
        for statement in (
            "example : LessonBeam.shear 20 8 4 6 = 80 := by decide",
            "example : LessonBeam.moment 20 8 4 4 = 0 := by decide",
        ):
            with self.subTest(statement=statement):
                self.assertNotEqual(self.compile_example(statement).returncode, 0)
