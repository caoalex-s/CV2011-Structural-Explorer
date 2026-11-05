"""Synthetic fixed-structure reuse fixtures, checked only in Linux CI."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PROOFS = Path(__file__).resolve().parents[1] / "proofs"


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class FrameReuseChecks(unittest.TestCase):
    def test_nonzero_load_particular_field(self):
        statement = """
import FrameReuse
open FrameInterfaces LocalFrameFields FrameReuse
noncomputable section

def zeroDofs : LocalDofs := fun _ => 0

example : (axialDisplacement zeroDofs 1 1 1 1).eval (1/2) = 1/8 := by
  norm_num [axialDisplacement, coordinate, zeroDofs]

example : (axialDisplacement zeroDofs 1 1 1 1).eval (1/2) ≠
    (axialDisplacement zeroDofs 1 1 1 1).eval (1/2) +
      (axialDisplacement zeroDofs 1 1 1 1).eval (1/2) := by
  norm_num [axialDisplacement, coordinate, zeroDofs]

example (d₁ d₂ : LocalDofs) :
    axialDisplacement (fun i => d₁ i + d₂ i) 1 1 1 1 =
      axialDisplacement d₁ 1 1 1 1 + axialDisplacement d₂ 1 1 1 1 -
        axialDisplacement zeroDofs 1 1 1 1 := by
  exact axial_recovery_movement_affine d₁ d₂ 1 1 1 1
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "ReuseCheck.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=PROOFS,
                capture_output=True, text=True, timeout=120, check=False,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
