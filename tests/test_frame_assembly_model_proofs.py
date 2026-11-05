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
example : activePoint sparseModel (.inr (0, 0)) := ⟨0, Or.inr rfl⟩
example : ¬ activePoint sparseModel (.inr (1, 0)) := by
  rintro ⟨i, h⟩
  fin_cases i
  simp [sparseModel, locationPoint, endNode] at h
  have hm := congrArg Prod.fst h
  norm_num at hm
example : ¬ activePoint sparseModel (.inl 2) := by
  rintro ⟨i, h⟩
  fin_cases i
  simp [sparseModel, locationPoint, endNode] at h
example : ¬ activeEnd sparseModel (1, false) := by
  rintro ⟨i, h⟩
  fin_cases i
  simp [sparseModel] at h
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_contract_rejects_unrepresented_support_and_zero_spring(self):
        result = self.compile_example("""
example {nodes members cuts segments actionCount supportCount : Nat}
    (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (length EA EI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter length EA EI)
    (support : Fin supportCount)
    (unrepresented : ¬ representedLocation model (supports support).location) : False :=
  unrepresented (h.supportLocations support)
example {nodes members cuts segments actionCount supportCount : Nat}
    (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (length EA EI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter length EA EI)
    (side : MemberEnd members) (direction : Fin 3)
    (active : activeEnd model side)
    (zeroSpring : directionLaw (endConnection model side) direction = .spring 0) : False := by
  have positive := h.positiveSpring side direction 0 active zeroSpring
  norm_num at positive
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_contract_rejects_disconnected_join_and_zero_support_axis(self):
        result = self.compile_example("""
example {nodes members cuts segments actionCount supportCount : Nat}
    (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter length EA EI)
    (member : Fin members) (a b : Fin cuts) (different : a ≠ b)
    (ha : representedLocation model (.interior member a))
    (hb : representedLocation model (.interior member b))
    (samePosition : cutParameter member a = cutParameter member b) : False := by
  have sameLocation := h.canonicalLocations member (.interior member a) (.interior member b)
    rfl rfl ha hb samePosition
  cases sameLocation
  exact different rfl
example {nodes members cuts segments actionCount supportCount : Nat}
    (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter length EA EI)
    (support : Fin supportCount) (roller : (supports support).kind = .roller)
    (zeroX : (supports support).cosine = 0) (zeroY : (supports support).sine = 0) : False := by
  have unit := h.supportNormalized support (Or.inl roller)
  rw [zeroX, zeroY] at unit
  norm_num at unit
example {nodes members cuts segments actionCount supportCount : Nat}
    (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter length EA EI)
    (q : Coordinate model → ℝ) (a b : Fin segments)
    (sameMember : model.segmentMember a = model.segmentMember b)
    (samePosition : locationParameter cutParameter (model.segmentRight a) =
      locationParameter cutParameter (model.segmentLeft b)) :
    sideMotion model q (model.segmentRight a) = sideMotion model q (model.segmentLeft b) := by
  apply congrArg (sideMotion model q)
  apply h.canonicalLocations (model.segmentMember a)
  · exact (h.ownership a).2
  · rw [sameMember]; exact (h.ownership b).1
  · exact ⟨a, Or.inr rfl⟩
  · exact ⟨b, Or.inl rfl⟩
  · exact samePosition
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_inhabited_two_segment_contract(self):
        result = self.compile_example("""
def splitModel : Model 2 1 1 2 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun _ => ⟨0, 1, ⟨1, 0⟩, none, none⟩
  segmentMember := fun _ => 0
  segmentLeft := fun i => if i = 0 then .endSide (0, false) else .interior 0 0
  segmentRight := fun i => if i = 0 then .interior 0 0 else .endSide (0, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0
def cuts : Fin 1 → Fin 1 → ℝ := fun _ _ => 1/2
def lengths : Fin 1 → ℝ := fun _ => 2
def rigidity : Fin 1 → ℝ := fun _ => 1
def loads : Fin 1 → PointAction 1 1 := fun _ => ⟨.interior 0 0, ![0, -1, 0]⟩
def supports : Fin 3 → SupportInput 1 1 := fun i =>
  if i = 0 then ⟨.endSide (0, false), .roller, 3/5, 4/5, false, false, false⟩
  else if i = 1 then ⟨.interior 0 0, .guided, 3/5, 4/5, false, false, false⟩
  else ⟨.endSide (0, true), .custom, 0, 0, true, false, true⟩
example : ExactContract splitModel loads supports cuts lengths rigidity rigidity := by
  constructor
  · intro segment
    fin_cases segment <;> simp [segmentOwnershipValid, locationBelongs, splitModel]
  · intro segment
    fin_cases segment <;> norm_num [splitModel, locationParameter, cuts]
  · intro member t ht0 ht1
    fin_cases member
    by_cases ht : t ≤ 1/2
    · refine ⟨0, ?_⟩
      norm_num [splitModel, locationParameter, cuts]
      constructor <;> linarith
    · refine ⟨1, ?_⟩
      norm_num [splitModel, locationParameter, cuts]
      constructor <;> linarith
  · intro a b hne hmember
    fin_cases a <;> fin_cases b <;> norm_num [splitModel, locationParameter, cuts] at *
  · intro member left right hl hr hleft hright hpos
    fin_cases member
    have leftCases : left = .endSide (0, false) ∨ left = .interior 0 0 ∨ left = .endSide (0, true) := by
      obtain ⟨i, hi⟩ := hleft
      fin_cases i <;> simp [splitModel] at hi <;> aesop
    have rightCases : right = .endSide (0, false) ∨ right = .interior 0 0 ∨ right = .endSide (0, true) := by
      obtain ⟨i, hi⟩ := hright
      fin_cases i <;> simp [splitModel] at hi <;> aesop
    rcases leftCases with rfl | rfl | rfl <;> rcases rightCases with rfl | rfl | rfl <;>
      norm_num [locationParameter, cuts] at *
  · intro member
    fin_cases member
    exact ⟨⟨0, Or.inl rfl⟩, ⟨1, Or.inr rfl⟩⟩
  · intro member cut h
    fin_cases member
    fin_cases cut
    norm_num [cuts]
  · intro action
    fin_cases action
    exact ⟨0, Or.inr rfl⟩
  · intro support
    fin_cases support
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨1, Or.inr rfl⟩
  · intro member
    fin_cases member
    norm_num [splitModel]
  · intro support hkind
    fin_cases support <;> norm_num [supports] at *
    rcases hkind with hkind | hkind <;> cases hkind
  · intro member
    fin_cases member
    norm_num [lengths, rigidity]
  · intro segment
    fin_cases segment <;> norm_num [splitModel, lengths, cuts, locationParameter]
  · intro segment
    fin_cases segment <;> norm_num [splitModel, rigidity]
  · intro side direction stiffness hactive hlaw
    rcases side with ⟨member, ending⟩
    fin_cases member
    cases ending <;> fin_cases direction <;>
      simp [directionLaw, endConnection, referenceMember, incident, endNode, splitModel,
        rigidConnection] at hlaw
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
