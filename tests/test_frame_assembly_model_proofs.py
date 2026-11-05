"""Linux fixtures for finite member-side ownership and support builders."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PROOFS = Path(__file__).resolve().parents[1] / "proofs"


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class FrameAssemblyModelChecks(unittest.TestCase):
    def compile_example(self, statement):
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "AssemblyModelCheck.lean"
            source.write_text(
                "import FrameAssembly\nopen FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly\nnoncomputable section\n"
                + statement + "\n", encoding="utf-8"
            )
            return subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=PROOFS,
                capture_output=True, text=True, timeout=120, check=False
            )

    def test_reference_hinge_and_support_directions(self):
        result = self.compile_example("""
def joint : JointInput 2 := ⟨.pinned, 5, none⟩
def reversedModel : Model 2 2 0 0 where
  joints := fun _ => joint
  member := fun i => if i = 0 then ⟨0, 1, ⟨1, 0⟩, none, none⟩
    else ⟨1, 0, ⟨-1, 0⟩, none, none⟩
  segmentMember := Fin.elim0
  segmentLeft := Fin.elim0
  segmentRight := Fin.elim0
  segmentLength := Fin.elim0
  segmentEA := Fin.elim0
  segmentEI := Fin.elim0
  segmentVerticalStart := Fin.elim0
  segmentVerticalEnd := Fin.elim0
example : referenceMember reversedModel 1 = some 0 := by rfl
example : directionLaw (endConnection reversedModel (0, true)) 2 = .rigid := by rfl
example : directionLaw (endConnection reversedModel (1, false)) 2 = .released := by rfl
example : directionLaw (endConnection reversedModel (1, false)) 0 = .rigid := by rfl
def guide : SupportInput 2 0 := ⟨.endSide (1, false), .guided, 3/5, 4/5, false, false, false⟩
example : supportDirections guide = [![0, 0, 1], ![3/5, 4/5, 0]] := by rfl
def custom : SupportInput 2 0 := ⟨.endSide (1, false), .custom, 3/5, 4/5, true, false, true⟩
example : supportDirections custom = [![1, 0, 0], ![0, 0, 1]] := by rfl
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_distinct_member_owned_cuts(self):
        result = self.compile_example("""
example : (Sum.inr (0, 0) : Point 1 2 1) ≠ Sum.inr (1, 0) := by
  exact distinct_member_cuts 0 1 0 0 (by decide)
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_unused_cut_and_node_have_no_coordinates(self):
        result = self.compile_example("""
def sparseModel : Model 3 2 1 1 where
  joints := fun _ => ⟨.pinned, 5, none⟩
  member := fun i => if i = 0 then ⟨0, 1, ⟨1, 0⟩, none, none⟩
    else ⟨1, 0, ⟨-1, 0⟩, none, none⟩
  segmentMember := fun _ => 0
  segmentLeft := fun _ => .endSide (0, false)
  segmentRight := fun _ => .interior 0 0
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0
example : activePoint sparseModel (.inr (0, 0)) := by decide
example : ¬ activePoint sparseModel (.inr (1, 0)) := by decide
example : ¬ activePoint sparseModel (.inl 2) := by decide
example : ¬ activeEnd sparseModel (1, false) := by decide
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_wrong_support_direction_is_rejected(self):
        result = self.compile_example("""
def guide : SupportInput 2 0 := ⟨.endSide (1, false), .roller, 3/5, 4/5, false, false, false⟩
example : work (![1, 0, 0]) ((supportDirections guide).head!) = 4/5 := by
  norm_num [work, guide, supportDirections]
""")
        output = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0)
        self.assertRegex(output, r"unsolved goals|tactic .*failed")
        self.assertNotIn("unknown identifier", output)


if __name__ == "__main__":
    unittest.main()
