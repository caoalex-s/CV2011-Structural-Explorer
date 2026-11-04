"""Compile real-field regressions only on the explicitly enabled Linux runner."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PROOFS = Path(__file__).resolve().parents[1] / "proofs"


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class RealFieldProofChecks(unittest.TestCase):
    def compile_example(self, statement):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "RealFieldCheck.lean"
            source.write_text("import RealBeamFields\nopen Polynomial RealBeamFields\n" + statement + "\n", encoding="utf-8")
            return subprocess.run(["lake", "env", "lean", str(source)], cwd=PROOFS,
                                  capture_output=True, text=True, timeout=90, check=False)

    def test_point_load_fields_and_real_derivative(self):
        result = self.compile_example("""
example : (deflectionBefore 20 4 8 20000).derivative = slopeBefore 20 4 8 20000 :=
  point_before_derivative 20 4 8 20000
example : (deflectionAfter 20 4 8 20000).eval 8 = 0 :=
  point_right_support 20 4 8 20000 (by norm_num) (by norm_num)
example : HasDerivAt (fun t : ℝ => (deflectionAfter 20 4 8 20000).eval t)
    ((slopeAfter 20 4 8 20000).eval 6) 6 := point_real_slope_after 20 4 8 20000 6
example : 20000 * (slopeBefore 20 4 8 20000).derivative.eval 2 = (pointMomentBefore 20 4 8).eval 2 :=
  point_curvature_before 20 4 8 20000 2 (by norm_num)
example : HasDerivAt (pointDisplacement 20 4 8 20000) (pointSlope 20 4 8 20000 2) 2 :=
  point_piece_slope_before 20 4 8 20000 2 (by norm_num)
example : HasDerivAt (pointDisplacement 20 4 8 20000) (pointSlope 20 4 8 20000 6) 6 :=
  point_piece_slope_after 20 4 8 20000 6 (by norm_num)
example : HasDerivAt (pointDisplacement 20 4 8 20000) (pointSlope 20 4 8 20000 4) 4 :=
  point_piece_slope_at_load 20 4 8 20000
example : Nonempty (PointBeamSolution 20 4 8 20000) :=
  point_solution_exists 20 4 8 20000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : Nonempty (PointBeamSolution 20 0 8 20000) :=
  point_solution_exists 20 0 8 20000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : Nonempty (PointBeamSolution (-15) 8 8 20000) :=
  point_solution_exists (-15) 8 8 20000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : Nonempty (CantileverSolution 20 (-7) 5 1 8 20000) :=
  cantilever_solution_exists 20 (-7) 5 1 8 20000 (by norm_num) (by norm_num)
example : Nonempty (CantileverSolution 20 7 5 1 8 20000) :=
  cantilever_solution_exists 20 7 5 1 8 20000 (by norm_num) (by norm_num)
example : (cantileverMoment 20 7 5 1 8).eval 8 = 7 :=
  cantilever_end_moment 20 7 5 1 8
example : (cantileverMoment 20 0 5 1 8).derivative.eval 8 = 20 :=
  cantilever_end_shear 20 0 5 1 8
example : HasDerivAt (fun t : ℝ => (cantileverDisplacement 20 0 5 1 8 20000).eval t)
    ((cantileverSlope 20 0 5 1 8 20000).eval 2) 2 := cantilever_real_slope 20 0 5 1 8 20000 2
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_wrong_jump_and_boundary_are_rejected(self):
        for statement in (
            "example : (shearAfterForce (0 : Field) 3).eval 2 = -3 := by norm_num [shearAfterForce]",
            "example : (deflectionAfter 20 4 8 20000).eval 8 = 1 := by norm_num [deflectionAfter, deflectionBefore, leftReaction, leftSlope]",
            "example : (pointShearAfter 20 4 8).eval 4 - (pointShearBefore 20 4 8).eval 4 = 20 := by norm_num [pointShearAfter, pointShearBefore, shearAfterForce, leftReaction]",
            "example : (cantileverMoment 20 7 5 1 8).eval 8 = -7 := by norm_num [cantileverMoment, cubicMoment, cantileverM0, cantileverM1]",
            "example : 20000 * (slopeBefore 20 4 8 20000).derivative.eval 2 = (pointMomentBefore 20 4 8).eval 2 + 1 := by norm_num [slopeBefore, pointMomentBefore, leftReaction, Polynomial.derivative_mul, Polynomial.derivative_pow]",
        ):
            with self.subTest(statement=statement):
                result = self.compile_example(statement)
                output = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0)
                self.assertRegex(output, r"unsolved goals|tactic .*failed")
                self.assertNotIn("unknown identifier", output)


if __name__ == "__main__":
    unittest.main()
