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
    (member : Fin members) (zeroC : (model.member member).orientation.cosine = 0)
    (zeroS : (model.member member).orientation.sine = 0) : False := by
  have normalized := h.orientationNormalized member
  rw [zeroC, zeroS] at normalized
  norm_num at normalized
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

    def test_inhabited_released_spring_side_contract(self):
        result = self.compile_example("""
def twoMemberModel : Model 2 2 0 2 where
  joints := fun _ => ⟨.pinned, 3, none⟩
  member := fun i => if i = 0 then ⟨0, 1, ⟨1, 0⟩, none, none⟩
    else ⟨1, 0, ⟨-1, 0⟩, some ⟨.spring 2, .released, .spring 3⟩, none⟩
  segmentMember := fun i => i
  segmentLeft := fun i => .endSide (i, false)
  segmentRight := fun i => .endSide (i, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0
def noCuts : Fin 2 → Fin 0 → ℝ := fun _ => Fin.elim0
def properties : Fin 2 → ℝ := fun _ => 1
def sideLoad : Fin 1 → PointAction 2 0 := fun _ => ⟨.endSide (1, false), ![0, 0, 4]⟩
def sideSupport : Fin 2 → SupportInput 2 0 := fun i =>
  if i = 0 then ⟨.endSide (1, false), .guided, 3/5, 4/5, false, false, false⟩
  else ⟨.endSide (0, false), .custom, 0, 0, true, true, true⟩
example : directionLaw (endConnection twoMemberModel (1, false)) 0 = .spring 2 := by rfl
example : directionLaw (endConnection twoMemberModel (1, false)) 1 = .released := by rfl
example : directionLaw (endConnection twoMemberModel (1, false)) 2 = .spring 3 := by rfl
theorem twoMember_contract : ExactContract twoMemberModel sideLoad sideSupport noCuts properties properties properties := by
  constructor
  · intro segment
    fin_cases segment <;> simp [segmentOwnershipValid, locationBelongs, twoMemberModel]
  · intro segment
    fin_cases segment <;> norm_num [twoMemberModel, locationParameter]
  · intro member t ht0 ht1
    refine ⟨member, rfl, ?_, ?_⟩
    · simpa [twoMemberModel, locationParameter] using ht0
    · simpa [twoMemberModel, locationParameter] using ht1
  · intro a b hne hmember
    fin_cases a <;> fin_cases b <;> norm_num [twoMemberModel, locationParameter] at *
  · intro member left right hl hr hleft hright hpos
    cases left with
    | interior m cut => exact Fin.elim0 cut
    | endSide leftSide =>
      cases right with
      | interior m cut => exact Fin.elim0 cut
      | endSide rightSide =>
        rcases leftSide with ⟨lm, lb⟩
        rcases rightSide with ⟨rm, rb⟩
        simp only [locationBelongs] at hl hr
        subst lm
        subst rm
        cases lb <;> cases rb <;> norm_num [locationParameter] at *
  · intro member
    constructor
    · exact ⟨member, Or.inl rfl⟩
    · exact ⟨member, Or.inr rfl⟩
  · intro member cut
    exact Fin.elim0 cut
  · intro action
    fin_cases action
    exact ⟨1, Or.inl rfl⟩
  · intro support
    fin_cases support
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨0, Or.inl rfl⟩
  · intro member
    fin_cases member <;> norm_num [twoMemberModel]
  · intro support hkind
    fin_cases support <;> norm_num [sideSupport] at *
    rcases hkind with hkind | hkind <;> cases hkind
  · intro member
    norm_num [properties]
  · intro segment
    fin_cases segment <;> norm_num [twoMemberModel, properties, locationParameter]
  · intro segment
    norm_num [twoMemberModel, properties]
  · intro side direction stiffness hactive hlaw
    have law00 : endConnection twoMemberModel (0, false) = rigidConnection := by rfl
    have law01 : endConnection twoMemberModel (0, true) = rigidConnection := by rfl
    have law10 : endConnection twoMemberModel (1, false) = ⟨.spring 2, .released, .spring 3⟩ := by rfl
    have law11 : endConnection twoMemberModel (1, true) = ⟨.rigid, .rigid, .released⟩ := by rfl
    rcases side with ⟨member, ending⟩
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, law00, law01, law10, law11, rigidConnection] at hlaw
    all_goals subst stiffness <;> norm_num

def springMode : Coordinate twoMemberModel → ℝ := fun coordinate =>
  match coordinate with
  | .inl _ => 0
  | .inr slip => if slip.val.1 = (1, false) ∧ slip.val.2 = 0 then 1 else 0

theorem springMode_positive : 0 < springEnergy twoMemberModel springMode := by
  classical
  have hactive : hasSlip twoMemberModel (1, false) 0 := by
    constructor
    · exact ⟨1, Or.inl rfl⟩
    · change EndLaw.spring 2 ≠ EndLaw.rigid
      intro h
      cases h
  have hslip : slipValue twoMemberModel springMode (1, false) 0 = 1 := by
    simp [slipValue, hactive, springMode]
  have hnonnegative := contract_nonnegative_springs twoMemberModel sideLoad sideSupport noCuts
    properties properties properties twoMember_contract
  let term := fun (m : Fin 2) (e : Bool) (i : Fin 3) =>
    springStiffness (directionLaw (endConnection twoMemberModel (m, e)) i) *
      (slipValue twoMemberModel springMode (m, e) i)^2 / 2
  have hterm (m : Fin 2) (e : Bool) (i : Fin 3) : 0 ≤ term m e i := by
    exact div_nonneg (mul_nonneg (hnonnegative m e i) (sq_nonneg _)) (by norm_num)
  have hi : term 1 false 0 ≤ ∑ i : Fin 3, term 1 false i :=
    Finset.single_le_sum (fun i _ => hterm 1 false i) (Finset.mem_univ 0)
  have he : (∑ i : Fin 3, term 1 false i) ≤ ∑ e : Bool, ∑ i : Fin 3, term 1 e i :=
    Finset.single_le_sum (fun e _ => Finset.sum_nonneg (fun i _ => hterm 1 e i)) (Finset.mem_univ false)
  have hm : (∑ e : Bool, ∑ i : Fin 3, term 1 e i) ≤
      ∑ m : Fin 2, ∑ e : Bool, ∑ i : Fin 3, term m e i :=
    Finset.single_le_sum (fun m _ => Finset.sum_nonneg
      (fun e _ => Finset.sum_nonneg (fun i _ => hterm m e i))) (Finset.mem_univ 1)
  have hpositive : 0 < term 1 false 0 := by
    change 0 < springStiffness (EndLaw.spring 2) * (slipValue twoMemberModel springMode (1, false) 0)^2 / 2
    rw [hslip]
    norm_num [springStiffness]
  change 0 < ∑ m : Fin 2, ∑ e : Bool, ∑ i : Fin 3, term m e i
  linarith

/-- Omitting this positive spring term changes the actual total energy. -/
example : totalEnergy twoMemberModel springMode ≠
    totalEnergy twoMemberModel springMode - springEnergy twoMemberModel springMode := by
  have h := springMode_positive
  linarith

def duplicateSupports : Fin 2 → SupportInput 2 0 := fun _ =>
  ⟨.endSide (1, false), .roller, 1, 0, false, false, false⟩
def row0 : ConstraintIndex duplicateSupports := ⟨0, ⟨0, by norm_num [duplicateSupports, supportDirections]⟩⟩
def row1 : ConstraintIndex duplicateSupports := ⟨1, ⟨0, by norm_num [duplicateSupports, supportDirections]⟩⟩
def reactionFirst : Module.Dual ℝ (ConstraintIndex duplicateSupports → ℝ) :=
  2 • LinearMap.proj row0 + 3 • LinearMap.proj row1
def reactionSecond : Module.Dual ℝ (ConstraintIndex duplicateSupports → ℝ) :=
  4 • LinearMap.proj row0 + 1 • LinearMap.proj row1
example : (constraintMap twoMemberModel duplicateSupports).dualMap reactionFirst =
    (constraintMap twoMemberModel duplicateSupports).dualMap reactionSecond := by
  ext variation
  simp [reactionFirst, reactionSecond, row0, row1, constraintMap, supportRowLinear, duplicateSupports,
    supportDirections, smul_eq_mul]
  ring
example : reactionFirst - reactionSecond ∈ LinearMap.ker (constraintMap twoMemberModel duplicateSupports).dualMap := by
  apply (reaction_gauge twoMemberModel duplicateSupports reactionFirst reactionSecond).mp
  ext variation
  simp [reactionFirst, reactionSecond, row0, row1, constraintMap, supportRowLinear, duplicateSupports,
    supportDirections, smul_eq_mul]
  ring
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_split_and_unsplit_axial_member(self):
        result = self.compile_example("""
def whole : LocalDofs := ![0, 0, 0, 2, 0, 0]
def leftHalf : LocalDofs := ![0, 0, 0, 1, 0, 0]
def rightHalf : LocalDofs := ![1, 0, 0, 2, 0, 0]
example : LocalFrameFields.endActions whole 2 2 1 0 0 0 0 = ![-2, 0, 0, 2, 0, 0] := by
  funext i
  rw [LocalFrameFields.end_actions_from_fields whole 2 2 1 0 0 0 0 (by norm_num) (by norm_num) (by norm_num)]
  fin_cases i <;> norm_num [whole, LocalFrameFields.stiffness, LocalFrameFields.consistentLoad, Fin.sum_univ_succ]
theorem leftHalf_actions : LocalFrameFields.endActions leftHalf 1 2 1 0 0 0 0 = ![-2, 0, 0, 2, 0, 0] := by
  funext i
  rw [LocalFrameFields.end_actions_from_fields leftHalf 1 2 1 0 0 0 0 (by norm_num) (by norm_num) (by norm_num)]
  fin_cases i <;> norm_num [leftHalf, LocalFrameFields.stiffness, LocalFrameFields.consistentLoad, Fin.sum_univ_succ]
theorem rightHalf_actions : LocalFrameFields.endActions rightHalf 1 2 1 0 0 0 0 = ![-2, 0, 0, 2, 0, 0] := by
  funext i
  rw [LocalFrameFields.end_actions_from_fields rightHalf 1 2 1 0 0 0 0 (by norm_num) (by norm_num) (by norm_num)]
  fin_cases i <;> norm_num [rightHalf, LocalFrameFields.stiffness, LocalFrameFields.consistentLoad, Fin.sum_univ_succ]
example : LocalFrameFields.endActions leftHalf 1 2 1 0 0 0 0 3 +
    LocalFrameFields.endActions rightHalf 1 2 1 0 0 0 0 0 = 0 := by
  rw [leftHalf_actions, rightHalf_actions]
  change (2 : ℝ) + (-2) = 0
  norm_num
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_partial_affine_load_with_cut_action_and_support(self):
        result = self.compile_example("""
def partialModel : Model 2 1 1 2 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun _ => ⟨0, 1, ⟨1, 0⟩, none, none⟩
  segmentMember := fun _ => 0
  segmentLeft := fun i => if i = 0 then .endSide (0, false) else .interior 0 0
  segmentRight := fun i => if i = 0 then .interior 0 0 else .endSide (0, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun i => if i = 0 then 0 else 2
  segmentVerticalEnd := fun i => if i = 0 then 0 else 4

def unitUp : Coordinate partialModel → ℝ := fun coordinate =>
  match coordinate with
  | .inl (_, direction) => if direction = 1 then 1 else 0
  | .inr _ => 0

def cutLoad : Fin 1 → PointAction 1 1 := fun _ => ⟨.interior 0 0, ![0, -1, 0]⟩
def cutSupport : SupportInput 1 1 := ⟨.interior 0 0, .roller, 0, 1, false, false, false⟩

def partialSupports : Fin 1 → SupportInput 1 1 := fun _ => cutSupport
def partialCuts : Fin 1 → Fin 1 → ℝ := fun _ _ => 1/2
def partialLengths : Fin 1 → ℝ := fun _ => 2
def partialRigidities : Fin 1 → ℝ := fun _ => 1

example : ExactContract partialModel cutLoad partialSupports partialCuts partialLengths
    partialRigidities partialRigidities := by
  constructor
  · intro segment
    fin_cases segment <;> simp [segmentOwnershipValid, locationBelongs, partialModel]
  · intro segment
    fin_cases segment <;> norm_num [partialModel, locationParameter, partialCuts]
  · intro member t ht0 ht1
    fin_cases member
    by_cases ht : t ≤ 1/2
    · refine ⟨0, ?_⟩
      norm_num [partialModel, locationParameter, partialCuts]
      constructor <;> linarith
    · refine ⟨1, ?_⟩
      norm_num [partialModel, locationParameter, partialCuts]
      constructor <;> linarith
  · intro a b hne hmember
    fin_cases a <;> fin_cases b <;> norm_num [partialModel, locationParameter, partialCuts] at *
  · intro member left right hl hr hleft hright hpos
    fin_cases member
    have leftCases : left = .endSide (0, false) ∨ left = .interior 0 0 ∨ left = .endSide (0, true) := by
      obtain ⟨i, hi⟩ := hleft
      fin_cases i <;> simp [partialModel] at hi <;> aesop
    have rightCases : right = .endSide (0, false) ∨ right = .interior 0 0 ∨ right = .endSide (0, true) := by
      obtain ⟨i, hi⟩ := hright
      fin_cases i <;> simp [partialModel] at hi <;> aesop
    rcases leftCases with rfl | rfl | rfl <;> rcases rightCases with rfl | rfl | rfl <;>
      norm_num [locationParameter, partialCuts] at *
  · intro member
    fin_cases member
    exact ⟨⟨0, Or.inl rfl⟩, ⟨1, Or.inr rfl⟩⟩
  · intro member cut h
    fin_cases member
    fin_cases cut
    norm_num [partialCuts]
  · intro action
    fin_cases action
    exact ⟨0, Or.inr rfl⟩
  · intro support
    fin_cases support
    exact ⟨0, Or.inr rfl⟩
  · intro member
    fin_cases member
    norm_num [partialModel]
  · intro support hkind
    fin_cases support
    norm_num [partialSupports, cutSupport]
  · intro member
    fin_cases member
    norm_num [partialLengths, partialRigidities]
  · intro segment
    fin_cases segment <;> norm_num [partialModel, partialLengths, partialCuts, locationParameter]
  · intro segment
    fin_cases segment <;> norm_num [partialModel, partialRigidities]
  · intro side direction stiffness hactive hlaw
    rcases side with ⟨member, ending⟩
    fin_cases member
    cases ending <;> fin_cases direction <;>
      simp [directionLaw, endConnection, referenceMember, incident, endNode, partialModel,
        rigidConnection] at hlaw

theorem hpoint0 : activePoint partialModel (.inl 0) := ⟨0, Or.inl rfl⟩
theorem hpoint1 : activePoint partialModel (.inl 1) := ⟨1, Or.inr rfl⟩
theorem hpointCut : activePoint partialModel (.inr (0, 0)) := ⟨0, Or.inr rfl⟩

example : segmentLoad partialModel 0 = 0 := by
  funext i
  fin_cases i <;> norm_num [segmentLoad, partialModel, LocalFrameFields.consistentLoad]
example : (segmentLoad partialModel 1) 1 = 13/10 := by
  norm_num [segmentLoad, partialModel, LocalFrameFields.consistentLoad]
example : (segmentLoad partialModel 1) 4 = 17/10 := by
  have h : segmentLoad partialModel 1 = ![0, 13/10, 7/30, 0, 17/10, -(4/15)] := by
    funext i
    fin_cases i <;> norm_num [segmentLoad, partialModel, LocalFrameFields.consistentLoad]
  rw [h]
  change (17/10 : ℝ) = 17/10
  rfl
example : pointActionWork partialModel (cutLoad 0) unitUp = -1 := by
  have hc : activePoint partialModel (.inr 0) := hpointCut
  norm_num [pointActionWork, FrameTransform.work, sideMotion, referenceMotion,
    cutLoad, unitUp, hc] <;> norm_num
example : supportRow partialModel cutSupport (![0, 1, 0]) unitUp = 1 := by
  have hc : activePoint partialModel (.inr 0) := hpointCut
  norm_num [supportRow, FrameTransform.work, sideMotion, referenceMotion,
    cutSupport, unitUp, hc] <;> norm_num
theorem external_up : externalFunctional partialModel cutLoad unitUp = 2 := by
  rw [external_functional_apply]
  classical
  have hp0 := hpoint0
  have hp1 := hpoint1
  have hpc := hpointCut
  dsimp [partialModel] at hp0 hp1 hpc
  simp [externalWork, segmentLoad, segmentDofs, segmentMotion, sideMotion, referenceMotion,
    endMotion, toLocal6, slipValue, partialModel, endNode, cutLoad, unitUp,
    LocalFrameFields.consistentLoad, pointActionWork, FrameTransform.work,
    hp0, hp1, hpc, Fin.sum_univ_succ]
  norm_num
example : residualWork partialModel cutLoad 0 unitUp = -2 := by
  have hext : externalWork partialModel cutLoad unitUp = 2 := by
    rw [← external_functional_apply]
    exact external_up
  have hzero (segment : Fin 2) : segmentDofs partialModel 0 segment = 0 :=
    (segmentDofsLinear partialModel segment).map_zero
  have hslip (member : Fin 1) (ending : Bool) (direction : Fin 3) :
      slipValue partialModel 0 (member, ending) direction = 0 :=
    (slipLinear partialModel (member, ending) direction).map_zero
  simp [residualWork, internalVirtualWork, hzero, hslip, hext]
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_released_rotation_side_action_and_support_ownership(self):
        result = self.compile_example("""
def hingeModel : Model 2 2 0 2 where
  joints := fun _ => ⟨.pinned, 1, none⟩
  member := fun i => if i = 0 then ⟨0, 1, ⟨1, 0⟩, none, none⟩
    else ⟨1, 0, ⟨-1, 0⟩, none, none⟩
  segmentMember := fun i => i
  segmentLeft := fun i => .endSide (i, false)
  segmentRight := fun i => .endSide (i, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0

def sideRotation : Coordinate hingeModel → ℝ := fun coordinate =>
  match coordinate with
  | .inl _ => 0
  | .inr slip => if slip.val.1 = (1, false) ∧ slip.val.2 = 2 then 1 else 0

def releasedCouple : PointAction 2 0 := ⟨.endSide (1, false), ![0, 0, 5]⟩
def hubCouple : PointAction 2 0 := ⟨.endSide (0, true), ![0, 0, 5]⟩
def releasedSupport : SupportInput 2 0 := ⟨.endSide (1, false), .fixed, 0, 0, false, false, false⟩
def hubSupport : SupportInput 2 0 := ⟨.endSide (0, true), .fixed, 0, 0, false, false, false⟩

theorem rotationReleased : directionLaw (endConnection hingeModel (1, false)) 2 = .released := by rfl
theorem rotationSlip : hasSlip hingeModel (1, false) 2 := by
  constructor
  · exact ⟨1, Or.inl rfl⟩
  · rw [rotationReleased]
    intro h
    cases h

theorem releasedSideMotion : sideMotion hingeModel sideRotation (.endSide (1, false)) = ![0, 0, 1] := by
  classical
  funext i
  fin_cases i <;> simp [sideMotion, referenceMotion, endMotion, slipValue, sideRotation,
    hingeModel, endNode, rotationSlip] <;> try split_ifs <;> try norm_num <;> try contradiction
  all_goals exact rotationSlip

theorem hubSideMotion : sideMotion hingeModel sideRotation (.endSide (0, true)) = 0 := by
  classical
  funext i
  fin_cases i <;> simp [sideMotion, referenceMotion, endMotion, slipValue, sideRotation,
    hingeModel, endNode] <;> split_ifs <;> norm_num

example : pointActionWork hingeModel releasedCouple sideRotation = 5 := by
  simp [pointActionWork, releasedCouple, FrameTransform.work, releasedSideMotion]
example : pointActionWork hingeModel hubCouple sideRotation = 0 := by
  simp [pointActionWork, hubCouple, FrameTransform.work, hubSideMotion]
example : supportRow hingeModel releasedSupport (![0, 0, 1]) sideRotation = 1 := by
  simp [supportRow, releasedSupport, FrameTransform.work, releasedSideMotion]
example : supportRow hingeModel hubSupport (![0, 0, 1]) sideRotation = 0 := by
  simp [supportRow, hubSupport, FrameTransform.work, hubSideMotion]
example : pointActionWork hingeModel releasedCouple sideRotation ≠
    pointActionWork hingeModel hubCouple sideRotation := by
  simp [pointActionWork, releasedCouple, hubCouple, FrameTransform.work,
    releasedSideMotion, hubSideMotion]
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_rigid_joint_with_reversed_member(self):
        result = self.compile_example("""
def rigidJoined : Model 2 2 0 2 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun i => if i = 0 then ⟨0, 1, ⟨1, 0⟩, none, none⟩
    else ⟨1, 0, ⟨-1, 0⟩, none, none⟩
  segmentMember := fun i => i
  segmentLeft := fun i => .endSide (i, false)
  segmentRight := fun i => .endSide (i, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0

example (q : Coordinate rigidJoined → ℝ) :
    sideMotion rigidJoined q (.endSide (0, true)) = sideMotion rigidJoined q (.endSide (1, false)) := by
  have law0 : endConnection rigidJoined (0, true) = rigidConnection := by rfl
  have law1 : endConnection rigidJoined (1, false) = rigidConnection := by rfl
  have h0 : slipValue rigidJoined q (0, true) = 0 := by
    funext i
    fin_cases i <;> simp [slipValue, hasSlip, directionLaw, law0, rigidConnection]
  have h1 : slipValue rigidJoined q (1, false) = 0 := by
    funext i
    fin_cases i <;> simp [slipValue, hasSlip, directionLaw, law1, rigidConnection]
  change endMotion 1 0 (referenceMotion rigidJoined q (.inl 1)) (slipValue rigidJoined q (0, true)) =
    endMotion (-1) 0 (referenceMotion rigidJoined q (.inl 1)) (slipValue rigidJoined q (1, false))
  rw [h0, h1]
  change endMotion 1 0 (referenceMotion rigidJoined q (.inl 1)) (fun _ => 0) =
    endMotion (-1) 0 (referenceMotion rigidJoined q (.inl 1)) (fun _ => 0)
  rw [rigid_end, rigid_end]
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
