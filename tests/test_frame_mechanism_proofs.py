"""Exact assembly mechanism witnesses, checked only on Linux CI."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PROOFS = Path(__file__).resolve().parents[1] / "proofs"


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class FrameMechanismChecks(unittest.TestCase):
    def test_pure_slip_mode(self):
        statement = """
import FrameDeformation
open FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly FrameEnergy FrameDeformation
noncomputable section

def freeAxial : EndConnection := ⟨.released, .rigid, .rigid⟩
def parallelModel : Model 2 2 0 2 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun i => if i = 0 then ⟨0, 1, ⟨1, 0⟩, none, none⟩
    else ⟨0, 1, ⟨1, 0⟩, some freeAxial, some freeAxial⟩
  segmentMember := fun i => i
  segmentLeft := fun i => .endSide (i, false)
  segmentRight := fun i => .endSide (i, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0

def pureSlip : Coordinate parallelModel → ℝ := fun coordinate =>
  match coordinate with
  | .inl _ => 0
  | .inr slip => if slip.val.1.1 = 1 ∧ slip.val.2 = 0 then 1 else 0

def noSupports : Fin 0 → SupportInput 2 0 := Fin.elim0

example (point : ActivePoint parallelModel) (direction : Fin 3) :
    pureSlip (.inl (point, direction)) = 0 := rfl
theorem pureSlip_nonzero : pureSlip ≠ 0 := by
  have hactive : hasSlip parallelModel (1, false) 0 := by
    constructor
    · exact ⟨1, Or.inl rfl⟩
    · change EndLaw.released ≠ EndLaw.rigid
      intro h
      cases h
  intro hzero
  have h := congrFun hzero (.inr ⟨((1, false), 0), hactive⟩)
  norm_num [pureSlip] at h
theorem pureSlip_admissible : admissible parallelModel noSupports pureSlip := by
  intro support
  exact Fin.elim0 support
theorem pureSlip_zero_deformation : deformationMap parallelModel pureSlip = 0 := by
  classical
  funext index
  cases index with
  | inl memberIndex =>
    rcases memberIndex with ⟨segment, component⟩
    fin_cases segment <;> fin_cases component <;>
      simp [deformationMap, segmentDeformation, memberDeformation, relativeRotationLeft,
        relativeRotationRight, segmentDofs, segmentMotion, sideMotion, referenceMotion,
        endMotion, toLocal6, slipValue, hasSlip, activeEnd, endConnection, directionLaw,
        referenceMember, incident, endNode, parallelModel, freeAxial, pureSlip] <;>
      split_ifs <;> norm_num
  | inr spring =>
    obtain ⟨k, hk⟩ := spring.property.2
    rcases spring.val with ⟨⟨member, ending⟩, direction⟩
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, endConnection, referenceMember, incident, endNode,
        parallelModel, freeAxial, rigidConnection] at hk
example : mechanism parallelModel noSupports pureSlip :=
  ⟨pureSlip_nonzero, pureSlip_admissible, pureSlip_zero_deformation⟩
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "PureSlip.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(["lake", "env", "lean", str(source)], cwd=PROOFS,
                                    capture_output=True, text=True, timeout=120, check=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
