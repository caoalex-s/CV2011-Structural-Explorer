"""Linux-only positive and mutation fixtures for exact local frame fields."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PROOFS = Path(__file__).resolve().parents[1] / "proofs"


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class LocalFrameFieldChecks(unittest.TestCase):
    def compile_example(self, statement):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "LocalFrameCheck.lean"
            source.write_text("import LocalFrameFields\nopen Polynomial FrameInterfaces LocalFrameFields\n" + statement + "\n", encoding="utf-8")
            return subprocess.run(["lake", "env", "lean", str(source)], cwd=PROOFS,
                                  capture_output=True, text=True, timeout=120, check=False)

    def test_affine_signed_and_zero_fields(self):
        result = self.compile_example("""
def zeroDofs : LocalDofs := fun _ => 0
example : (axialDisplacement zeroDofs 2 10 3 (-1)).eval 0 = 0 := by
  simpa [zeroDofs] using (axial_end_kinematics zeroDofs 2 10 3 (-1) (by norm_num) (by norm_num)).1
example : (rotation zeroDofs 2 10 3 (-1)).eval 2 = 0 := by
  simpa [zeroDofs] using (rotation_end_kinematics zeroDofs 2 10 3 (-1) (by norm_num) (by norm_num)).2
example : (normal zeroDofs 2 10 3 (-1)).derivative.eval 1 = -(3 + ((-1)-3)*1/2) :=
  axial_balance zeroDofs 2 10 3 (-1) 1 (by norm_num) (by norm_num)
example : (shear zeroDofs 2 10 3 (-1)).derivative.eval 1 = 3 + ((-1)-3)*1/2 :=
  transverse_balance zeroDofs 2 10 3 (-1) 1 (by norm_num) (by norm_num)
example : (shear zeroDofs 2 10 0 0).derivative.eval 1 = 0 := by
  simpa using transverse_balance zeroDofs 2 10 0 0 1 (by norm_num) (by norm_num)
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_incorrect_load_sign_is_rejected(self):
        result = self.compile_example("""
def zeroDofs : LocalDofs := fun _ => 0
example : (normal zeroDofs 2 10 3 (-1)).derivative.eval 1 = 1 := by
  have h := axial_balance zeroDofs 2 10 3 (-1) 1 (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith
""")
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0)
        self.assertRegex(output, r"unsolved goals|tactic .*failed")
        self.assertNotIn("unknown identifier", output)


if __name__ == "__main__":
    unittest.main()
