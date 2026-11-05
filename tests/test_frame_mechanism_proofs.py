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
  have law00 : endConnection parallelModel (0, false) = rigidConnection := by rfl
  have law01 : endConnection parallelModel (0, true) = rigidConnection := by rfl
  have law10 : endConnection parallelModel (1, false) = freeAxial := by rfl
  have law11 : endConnection parallelModel (1, true) = freeAxial := by rfl
  have hs10 : hasSlip parallelModel (1, false) 0 := by
    constructor
    · exact ⟨1, Or.inl rfl⟩
    · change EndLaw.released ≠ EndLaw.rigid
      intro h
      cases h
  have hs11 : hasSlip parallelModel (1, true) 0 := by
    constructor
    · exact ⟨1, Or.inr rfl⟩
    · change EndLaw.released ≠ EndLaw.rigid
      intro h
      cases h
  funext index
  cases index with
  | inl memberIndex =>
    rcases memberIndex with ⟨segment, component⟩
    fin_cases segment <;> fin_cases component <;>
      simp [deformationMap, segmentDeformation, memberDeformation, relativeRotationLeft,
        relativeRotationRight, segmentDofs, segmentMotion, sideMotion, referenceMotion,
        endMotion, toLocal6, slipValue, endNode, parallelModel,
        pureSlip, hs10, hs11] <;>
      split_ifs <;> norm_num <;> contradiction
  | inr spring =>
    rcases spring with ⟨⟨⟨member, ending⟩, direction⟩, hactive, k, hk⟩
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, freeAxial, rigidConnection, law00, law01, law10, law11] at hk
example : mechanism parallelModel noSupports pureSlip :=
  ⟨pureSlip_nonzero, pureSlip_admissible, pureSlip_zero_deformation⟩

def noActions : Fin 0 → PointAction 2 0 := Fin.elim0
def noCuts : Fin 2 → Fin 0 → ℝ := fun _ => Fin.elim0
def unitProperties : Fin 2 → ℝ := fun _ => 1

theorem pureSlip_contract : ExactContract parallelModel noActions noSupports noCuts
    unitProperties unitProperties unitProperties := by
  constructor
  · intro segment
    fin_cases segment <;> simp [segmentOwnershipValid, locationBelongs, parallelModel]
  · intro segment
    fin_cases segment <;> norm_num [parallelModel, locationParameter]
  · intro member t ht0 ht1
    refine ⟨member, rfl, ?_, ?_⟩
    · simpa [parallelModel, locationParameter] using ht0
    · simpa [parallelModel, locationParameter] using ht1
  · intro a b hne hmember
    fin_cases a <;> fin_cases b <;> norm_num [parallelModel, locationParameter] at *
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
    exact ⟨⟨member, Or.inl rfl⟩, ⟨member, Or.inr rfl⟩⟩
  · intro member cut
    exact Fin.elim0 cut
  · intro action
    exact Fin.elim0 action
  · intro support
    exact Fin.elim0 support
  · intro member
    fin_cases member <;> norm_num [parallelModel]
  · intro support
    exact Fin.elim0 support
  · intro member
    norm_num [unitProperties]
  · intro segment
    fin_cases segment <;> norm_num [parallelModel, unitProperties, locationParameter]
  · intro segment
    norm_num [parallelModel, unitProperties]
  · intro side direction stiffness hactive hlaw
    have law00 : endConnection parallelModel (0, false) = rigidConnection := by rfl
    have law01 : endConnection parallelModel (0, true) = rigidConnection := by rfl
    have law10 : endConnection parallelModel (1, false) = freeAxial := by rfl
    have law11 : endConnection parallelModel (1, true) = freeAxial := by rfl
    rcases side with ⟨member, ending⟩
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, law00, law01, law10, law11, rigidConnection, freeAxial] at hlaw

example : totalEnergy parallelModel pureSlip = 0 :=
  deformation_zero_implies_energy_zero parallelModel noActions noSupports noCuts
    unitProperties unitProperties unitProperties pureSlip_contract pureSlip pureSlip_zero_deformation

example : ∃ q, equilibrium parallelModel noActions noSupports q := by
  apply (equilibrium_exists_iff_load_compatible parallelModel noActions noSupports noCuts
    unitProperties unitProperties unitProperties pureSlip_contract).mpr
  intro variation hadmissible hdeformation
  simp [externalWork, segmentLoad, parallelModel, LocalFrameFields.consistentLoad,
    Fin.sum_univ_succ]
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "PureSlip.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(["lake", "env", "lean", str(source)], cwd=PROOFS,
                                    capture_output=True, text=True, timeout=120, check=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


    def test_disconnected_member_rigid_motion(self):
        statement = """
import FrameDeformation
open FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly FrameEnergy FrameDeformation
noncomputable section

def disconnectedModel : Model 4 2 0 2 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun i => if i = 0 then ⟨0, 1, ⟨1, 0⟩, none, none⟩
    else ⟨2, 3, ⟨1, 0⟩, none, none⟩
  segmentMember := fun i => i
  segmentLeft := fun i => .endSide (i, false)
  segmentRight := fun i => .endSide (i, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0

def detachedTranslation : Coordinate disconnectedModel → ℝ := fun coordinate =>
  match coordinate with
  | .inl (point, direction) =>
      if (point.val = .inl 2 ∨ point.val = .inl 3) ∧ direction = 0 then 1 else 0
  | .inr _ => 0

def noSupports : Fin 0 → SupportInput 2 0 := Fin.elim0

example : detachedTranslation ≠ 0 := by
  have hactive : activePoint disconnectedModel (.inl 2) := ⟨1, Or.inl rfl⟩
  intro hzero
  have h := congrFun hzero (.inl (⟨.inl 2, hactive⟩, 0))
  norm_num [detachedTranslation] at h
example : admissible disconnectedModel noSupports detachedTranslation := by
  intro support
  exact Fin.elim0 support
example : deformationMap disconnectedModel detachedTranslation = 0 := by
  classical
  have law00 : endConnection disconnectedModel (0, false) = rigidConnection := by rfl
  have law01 : endConnection disconnectedModel (0, true) = rigidConnection := by rfl
  have law10 : endConnection disconnectedModel (1, false) = rigidConnection := by rfl
  have law11 : endConnection disconnectedModel (1, true) = rigidConnection := by rfl
  have ha0 : activePoint disconnectedModel (.inl 0) := ⟨0, Or.inl rfl⟩
  have ha1 : activePoint disconnectedModel (.inl 1) := ⟨0, Or.inr rfl⟩
  have ha2 : activePoint disconnectedModel (.inl 2) := ⟨1, Or.inl rfl⟩
  have ha3 : activePoint disconnectedModel (.inl 3) := ⟨1, Or.inr rfl⟩
  funext index
  cases index with
  | inl memberIndex =>
    rcases memberIndex with ⟨segment, component⟩
    fin_cases segment <;> fin_cases component <;>
      simp [deformationMap, segmentDeformation, memberDeformation, relativeRotationLeft,
        relativeRotationRight, segmentDofs, segmentMotion, sideMotion, referenceMotion,
        endMotion, toLocal6, slipValue, endNode, disconnectedModel, detachedTranslation,
        ha0, ha1, ha2, ha3] <;> split_ifs <;> norm_num <;> contradiction
  | inr spring =>
    rcases spring with ⟨⟨⟨member, ending⟩, direction⟩, hactive, k, hk⟩
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, rigidConnection, law00, law01, law10, law11] at hk
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "Disconnected.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(["lake", "env", "lean", str(source)], cwd=PROOFS,
                                    capture_output=True, text=True, timeout=120, check=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


    def test_fixed_fixed_member_stable_and_indeterminate(self):
        statement = """
import FrameDeformation
open FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly FrameEnergy FrameDeformation
noncomputable section

def fixedModel : Model 2 1 0 1 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun _ => ⟨0, 1, ⟨1, 0⟩, none, none⟩
  segmentMember := fun _ => 0
  segmentLeft := fun _ => .endSide (0, false)
  segmentRight := fun _ => .endSide (0, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0

def fixedSupports : Fin 2 → SupportInput 1 0 := fun i =>
  if i = 0 then ⟨.endSide (0, false), .fixed, 0, 0, false, false, false⟩
  else ⟨.endSide (0, true), .fixed, 0, 0, false, false, false⟩

def fixedNoActions : Fin 0 → PointAction 1 0 := Fin.elim0
def fixedNoCuts : Fin 1 → Fin 0 → ℝ := fun _ => Fin.elim0
def fixedProperties : Fin 1 → ℝ := fun _ => 1

example : ExactContract fixedModel fixedNoActions fixedSupports fixedNoCuts
    fixedProperties fixedProperties fixedProperties := by
  constructor
  · intro segment
    fin_cases segment <;> simp [segmentOwnershipValid, locationBelongs, fixedModel]
  · intro segment
    fin_cases segment <;> norm_num [fixedModel, locationParameter]
  · intro member t ht0 ht1
    fin_cases member
    exact ⟨0, rfl, by simpa [fixedModel, locationParameter] using ht0,
      by simpa [fixedModel, locationParameter] using ht1⟩
  · intro a b hne hmember
    fin_cases a <;> fin_cases b <;> contradiction
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
    fin_cases member
    exact ⟨⟨0, Or.inl rfl⟩, ⟨0, Or.inr rfl⟩⟩
  · intro member cut
    exact Fin.elim0 cut
  · intro action
    exact Fin.elim0 action
  · intro support
    fin_cases support
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨0, Or.inr rfl⟩
  · intro member
    fin_cases member
    norm_num [fixedModel]
  · intro support hkind
    fin_cases support <;> simp [fixedSupports] at hkind
  · intro member
    norm_num [fixedProperties]
  · intro segment
    fin_cases segment
    norm_num [fixedModel, fixedProperties, locationParameter]
  · intro segment
    norm_num [fixedModel, fixedProperties]
  · intro side direction stiffness hactive hlaw
    have law0 : endConnection fixedModel (0, false) = rigidConnection := by rfl
    have law1 : endConnection fixedModel (0, true) = rigidConnection := by rfl
    rcases side with ⟨member, ending⟩
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, law0, law1, rigidConnection] at hlaw

theorem fixed_movements_zero (q : Coordinate fixedModel → ℝ)
    (h : admissible fixedModel fixedSupports q) : q = 0 := by
  classical
  have hleft : sideMotion fixedModel q (.endSide (0, false)) = 0 := by
    funext i
    fin_cases i
    · have hx := h 0 (![1, 0, 0]) (by simp [fixedSupports, supportDirections])
      simpa [supportRow, FrameTransform.work, fixedSupports] using hx
    · have hy := h 0 (![0, 1, 0]) (by simp [fixedSupports, supportDirections])
      simpa [supportRow, FrameTransform.work, fixedSupports] using hy
    · have ht := h 0 (![0, 0, 1]) (by simp [fixedSupports, supportDirections])
      simpa [supportRow, FrameTransform.work, fixedSupports] using ht
  have hright : sideMotion fixedModel q (.endSide (0, true)) = 0 := by
    funext i
    fin_cases i
    · have hx := h 1 (![1, 0, 0]) (by simp [fixedSupports, supportDirections])
      simpa [supportRow, FrameTransform.work, fixedSupports] using hx
    · have hy := h 1 (![0, 1, 0]) (by simp [fixedSupports, supportDirections])
      simpa [supportRow, FrameTransform.work, fixedSupports] using hy
    · have ht := h 1 (![0, 0, 1]) (by simp [fixedSupports, supportDirections])
      simpa [supportRow, FrameTransform.work, fixedSupports] using ht
  have law0 : endConnection fixedModel (0, false) = rigidConnection := by rfl
  have law1 : endConnection fixedModel (0, true) = rigidConnection := by rfl
  have hslipLeft : slipValue fixedModel q (0, false) = 0 := by
    funext i
    fin_cases i <;> simp [slipValue, hasSlip, directionLaw, law0, rigidConnection]
  have hslipRight : slipValue fixedModel q (0, true) = 0 := by
    funext i
    fin_cases i <;> simp [slipValue, hasSlip, directionLaw, law1, rigidConnection]
  have hrefLeft : referenceMotion fixedModel q (.inl 0) = 0 := by
    have hv := hleft
    change endMotion 1 0 (referenceMotion fixedModel q (.inl 0)) (slipValue fixedModel q (0, false)) = 0 at hv
    rw [hslipLeft] at hv
    change endMotion 1 0 (referenceMotion fixedModel q (.inl 0)) (fun _ => 0) = 0 at hv
    rw [rigid_end] at hv
    exact hv
  have hrefRight : referenceMotion fixedModel q (.inl 1) = 0 := by
    have hv := hright
    change endMotion 1 0 (referenceMotion fixedModel q (.inl 1)) (slipValue fixedModel q (0, true)) = 0 at hv
    rw [hslipRight] at hv
    change endMotion 1 0 (referenceMotion fixedModel q (.inl 1)) (fun _ => 0) = 0 at hv
    rw [rigid_end] at hv
    exact hv
  funext coordinate
  cases coordinate with
  | inr slip =>
    rcases slip with ⟨⟨⟨member, ending⟩, direction⟩, hactive, hslip⟩
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, law0, law1, rigidConnection] at hslip
  | inl pointDirection =>
    rcases pointDirection with ⟨⟨point, hactive⟩, direction⟩
    cases point with
    | inr cutPoint => exact Fin.elim0 cutPoint.2
    | inl node =>
      fin_cases node
      · have hx := congrFun hrefLeft direction
        change (if hp : activePoint fixedModel (.inl 0) then q (.inl (⟨.inl 0, hp⟩, direction)) else 0) = 0 at hx
        rw [dif_pos hactive] at hx
        exact hx
      · have hx := congrFun hrefRight direction
        change (if hp : activePoint fixedModel (.inl 1) then q (.inl (⟨.inl 1, hp⟩, direction)) else 0) = 0 at hx
        rw [dif_pos hactive] at hx
        exact hx

example : ∀ q, admissible fixedModel fixedSupports q → deformationMap fixedModel q = 0 → q = 0 := by
  intro q h _
  exact fixed_movements_zero q h

example : ∃ stress : Module.Dual ℝ (Sum (Fin 1 × Fin 3) (SpringIndex fixedModel) → ℝ),
    stress ∈ selfStressSpace fixedModel fixedSupports ∧ stress ≠ 0 := by
  let stress : Module.Dual ℝ (Sum (Fin 1 × Fin 3) (SpringIndex fixedModel) → ℝ) := LinearMap.proj (.inl (0, 0))
  refine ⟨stress, ?_, ?_⟩
  · change (restrictedDeformation fixedModel fixedSupports).dualMap stress = 0
    ext motion
    have hz := fixed_movements_zero motion.val
      ((admissible_iff_constraint_kernel fixedModel fixedSupports motion.val).mpr motion.property)
    have hmotion : motion = 0 := Subtype.ext hz
    change stress (restrictedDeformation fixedModel fixedSupports motion) = 0
    rw [hmotion, map_zero, map_zero]
  · intro hzero
    have h := congrArg (fun f : Module.Dual ℝ (Sum (Fin 1 × Fin 3) (SpringIndex fixedModel) → ℝ) => f (fun _ => 1)) hzero
    norm_num [stress] at h
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "Indeterminate.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(["lake", "env", "lean", str(source)], cwd=PROOFS,
                                    capture_output=True, text=True, timeout=120, check=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
