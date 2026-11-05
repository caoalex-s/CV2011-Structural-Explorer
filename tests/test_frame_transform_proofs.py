"""Linux-only checks for signed transforms and member-side spring actions."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PROOFS = Path(__file__).resolve().parents[1] / "proofs"


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class FrameTransformChecks(unittest.TestCase):
    def compile_example(self, statement):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "FrameTransformCheck.lean"
            source.write_text("import FrameTransform\nopen FrameTransform FrameInterfaces\n" + statement + "\n", encoding="utf-8")
            return subprocess.run(["lake", "env", "lean", str(source)], cwd=PROOFS,
                                  capture_output=True, text=True, timeout=120, check=False)

    def test_rotation_and_direct_side_action(self):
        result = self.compile_example("""
def v : Triple := ![1, -2, 3]
def member : LocalDofs := ![1, -2, 3, -4, 5, -6]
example : toGlobal6 0 1 (toLocal6 0 1 member) = member := inverse_transform6 0 1 member (by norm_num)
example : work6 (toLocal6 0 (-1) member) (toLocal6 0 (-1) member) = work6 member member :=
  work_invariant6 0 (-1) member member (by norm_num)
example : toGlobal 0 1 (toLocal 0 1 v) = v := inverse_transform 0 1 v (by norm_num)
example : work (toLocal 0 (-1) v) (toLocal 0 (-1) v) = work v v :=
  work_invariant 0 (-1) v v (by norm_num)
example : HasDerivAt (relativePotential 0 7 7) 0 2 := by
  simpa using potential_derivative 0 7 7 2
example : 7 = 7 := free_stationarity 7 7 2 (by simpa using potential_derivative 0 7 7 2)
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_side_load_does_not_imply_zero_member_action(self):
        result = self.compile_example("""
example : (7 : ℝ) = 0 := by
  have h : HasDerivAt (relativePotential 0 7 7) 0 2 := by
    simpa using potential_derivative 0 7 7 2
  have balance := free_stationarity 7 7 2 h
  norm_num
""")
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0)
        self.assertRegex(output, r"unsolved goals|tactic .*failed")
        self.assertNotIn("unknown identifier", output)


if __name__ == "__main__":
    unittest.main()
