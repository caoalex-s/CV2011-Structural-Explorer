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

    def test_core_and_slot_changes_are_rejected(self):
        statement = """
import FrameReuse
open FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly FrameReuse
noncomputable section

def base : Model 2 1 0 1 where
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

def changedEI : Model 2 1 0 1 := { base with segmentEI := fun _ => 2 }
def changedLength : Model 2 1 0 1 := { base with segmentLength := fun _ => 2 }
def changedOrientation : Model 2 1 0 1 := { base with
  member := fun _ => ⟨0, 1, ⟨0, 1⟩, none, none⟩ }
def changedRelease : Model 2 1 0 1 := { base with
  member := fun _ => ⟨0, 1, ⟨1, 0⟩, some ⟨.released, .rigid, .rigid⟩, none⟩ }

example : ¬ sameCore base changedEI := by
  intro h
  have v := congrArg (fun m : Model 2 1 0 1 => m.segmentEI 0) h
  norm_num [sameCore, structuralCore, base, changedEI] at v
example : ¬ sameCore base changedLength := by
  intro h
  have v := congrArg (fun m : Model 2 1 0 1 => m.segmentLength 0) h
  norm_num [sameCore, structuralCore, base, changedLength] at v
example : ¬ sameCore base changedOrientation := by
  intro h
  have v := congrArg (fun m : Model 2 1 0 1 => (m.member 0).orientation.cosine) h
  norm_num [sameCore, structuralCore, base, changedOrientation] at v
example : ¬ sameCore base changedRelease := by
  intro h
  have v := congrArg (fun m : Model 2 1 0 1 => (m.member 0).explicitStart) h
  simp [sameCore, structuralCore, base, changedRelease] at v

def supports : Fin 1 → SupportInput 1 0 := fun _ => ⟨.endSide (0, false), .roller, 0, 1, false, false, false⟩
def shiftedSupport : Fin 1 → SupportInput 1 0 := fun _ => ⟨.endSide (0, true), .roller, 0, 1, false, false, false⟩
def slots : Fin 1 → Location 1 0 := fun _ => .endSide (0, false)
def shiftedSlot : Fin 1 → Location 1 0 := fun _ => .endSide (0, true)
example : ¬ sameStructure base base supports shiftedSupport slots slots := by
  rintro ⟨_, h, _⟩
  have v := congrArg (fun f : Fin 1 → SupportInput 1 0 => (f 0).location) h
  simp [supports, shiftedSupport] at v
example : ¬ sameStructure base base supports supports slots shiftedSlot := by
  rintro ⟨_, _, h⟩
  have v := congrFun h 0
  simp [slots, shiftedSlot] at v

def rotatedSupport : Fin 1 → SupportInput 1 0 := fun _ => ⟨.endSide (0, false), .roller, 1, 0, false, false, false⟩
example : ¬ sameStructure base base supports rotatedSupport slots slots := by
  rintro ⟨_, h, _⟩
  have v := congrArg (fun f : Fin 1 → SupportInput 1 0 => (f 0).cosine) h
  norm_num [supports, rotatedSupport] at v

def twoMembers : Model 3 2 0 0 where
  joints := fun _ => ⟨.semiRigid, 2, none⟩
  member := fun i => if i = 0 then ⟨0, 1, ⟨1, 0⟩, none, none⟩ else ⟨0, 2, ⟨0, 1⟩, none, none⟩
  segmentMember := Fin.elim0
  segmentLeft := Fin.elim0
  segmentRight := Fin.elim0
  segmentLength := Fin.elim0
  segmentEA := Fin.elim0
  segmentEI := Fin.elim0
  segmentVerticalStart := Fin.elim0
  segmentVerticalEnd := Fin.elim0
def changedSpring : Model 3 2 0 0 := { twoMembers with joints := fun _ => ⟨.semiRigid, 3, none⟩ }
def changedReference : Model 3 2 0 0 := { twoMembers with joints := fun _ => ⟨.semiRigid, 2, some 1⟩ }
def reorderedMembers : Model 3 2 0 0 := { twoMembers with
  member := fun i => if i = 0 then ⟨0, 2, ⟨0, 1⟩, none, none⟩ else ⟨0, 1, ⟨1, 0⟩, none, none⟩ }
example : ¬ sameCore twoMembers changedSpring := by
  intro h
  have v := congrArg (fun m : Model 3 2 0 0 => (m.joints 0).rotationStiffness) h
  norm_num [sameCore, structuralCore, twoMembers, changedSpring] at v
example : ¬ sameCore twoMembers changedReference := by
  intro h
  have v := congrArg (fun m : Model 3 2 0 0 => (m.joints 0).requestedReference) h
  simp [sameCore, structuralCore, twoMembers, changedReference] at v
example : ¬ sameCore twoMembers reorderedMembers := by
  intro h
  have v := congrArg (fun m : Model 3 2 0 0 => (m.member 0).endNode) h
  simp [sameCore, structuralCore, twoMembers, reorderedMembers] at v

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
def noSupports : Fin 0 → SupportInput 1 1 := Fin.elim0
def noSlots : Fin 0 → Location 1 1 := Fin.elim0
def cutHalf : Fin 1 → Fin 1 → ℝ := fun _ _ => 1/2
def cutThird : Fin 1 → Fin 1 → ℝ := fun _ _ => 1/3
example : ¬ sameReuseBoundary splitModel splitModel noSupports noSupports noSlots noSlots cutHalf cutThird := by
  rintro ⟨_, h⟩
  have v := congrFun (congrFun h 0) 0
  norm_num [cutHalf, cutThird] at v
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "ReuseCoreCheck.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=PROOFS,
                capture_output=True, text=True, timeout=120, check=False,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_actual_signed_load_changes_with_fixed_structure(self):
        statement = """
import FrameReuse
open FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly FrameReuse
noncomputable section

def beam : Model 2 1 0 1 where
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

def slots : Fin 1 → Location 1 0 := fun _ => .endSide (0, true)
def loadZero : Fin 1 → Triple := fun _ => ![0, 0, 0]
def loadSigned : Fin 1 → Triple := fun _ => ![0, -2, 3]
def support : Fin 1 → SupportInput 1 0 := fun _ => ⟨.endSide (0, false), .fixed, 0, 1, false, false, false⟩
def rotationMode : Coordinate beam → ℝ := fun index =>
  match index with
  | .inl (_, direction) => if direction = 2 then 1 else 0
  | .inr _ => 0
def up : Coordinate beam → ℝ := fun index =>
  match index with
  | .inl (_, direction) => if direction = 1 then 1 else 0
  | .inr _ => 0

theorem node0active : activePoint beam (.inl 0) := ⟨0, Or.inl rfl⟩
theorem node1active : activePoint beam (.inl 1) := ⟨0, Or.inr rfl⟩
example : sameCore (withLoads beam 0 0) (withLoads beam (fun _ => 1) (fun _ => 1)) := by
  exact same_core_with_loads beam 0 0 (fun _ => 1) (fun _ => 1)
example (q v : Coordinate beam → ℝ) :
    stiffnessWork (withLoads beam 0 0) q v = stiffnessWork (withLoads beam (fun _ => 1) (fun _ => 1)) q v := by
  exact stiffness_unchanged beam 0 0 (fun _ => 1) (fun _ => 1) q v
example (q : Coordinate beam → ℝ) :
    constraintMap (withLoads beam 0 0) support q = constraintMap (withLoads beam (fun _ => 1) (fun _ => 1)) support q := by
  exact constraint_map_unchanged beam 0 0 (fun _ => 1) (fun _ => 1) support q
example : externalWork (withLoads beam 0 0) (pointActions slots loadZero) up = 0 := by
  simp [externalWork, segmentLoad, withLoads, LocalFrameFields.consistentLoad,
    pointActions, pointActionWork, loadZero, FrameTransform.work, Fin.sum_univ_succ]
example : externalWork (withLoads beam (fun _ => 1) (fun _ => 1)) (pointActions slots loadSigned) up = -1 := by
  have h0 : activePoint (withLoads beam (fun _ => 1) (fun _ => 1)) (.inl 0) := node0active
  have h1 : activePoint (withLoads beam (fun _ => 1) (fun _ => 1)) (.inl 1) := node1active
  dsimp [withLoads, beam] at h0 h1
  simp [externalWork, segmentLoad, segmentDofs, segmentMotion, sideMotion, referenceMotion,
    endMotion, toLocal6, slipValue, withLoads, beam, endNode, pointActions, slots, loadSigned, up,
    LocalFrameFields.consistentLoad, pointActionWork, FrameTransform.work, h0, h1, Fin.sum_univ_succ]
  norm_num
example : externalWork (withLoads beam (fun _ => 1) (fun _ => 1)) (pointActions slots loadSigned) rotationMode = 3 := by
  have h0 : activePoint (withLoads beam (fun _ => 1) (fun _ => 1)) (.inl 0) := node0active
  have h1 : activePoint (withLoads beam (fun _ => 1) (fun _ => 1)) (.inl 1) := node1active
  dsimp [withLoads, beam] at h0 h1
  simp [externalWork, segmentLoad, segmentDofs, segmentMotion, sideMotion, referenceMotion,
    endMotion, toLocal6, slipValue, withLoads, beam, endNode, pointActions, slots, loadSigned, rotationMode,
    LocalFrameFields.consistentLoad, pointActionWork, FrameTransform.work, h0, h1, Fin.sum_univ_succ] <;> norm_num
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "ReuseLoadCheck.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=PROOFS,
                capture_output=True, text=True, timeout=120, check=False,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_duplicate_support_reaction_gauge_and_combination(self):
        statement = """
import FrameReuse
open FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly FrameReuse
noncomputable section

def beam : Model 2 1 0 1 where
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

def duplicateSupports : Fin 2 → SupportInput 1 0 := fun _ =>
  ⟨.endSide (0, false), .roller, 1, 0, false, false, false⟩
def row0 : ConstraintIndex duplicateSupports := ⟨0, ⟨0, by norm_num [duplicateSupports, supportDirections]⟩⟩
def row1 : ConstraintIndex duplicateSupports := ⟨1, ⟨0, by norm_num [duplicateSupports, supportDirections]⟩⟩
def reactionFirst : Module.Dual ℝ (ConstraintIndex duplicateSupports → ℝ) :=
  2 • LinearMap.proj row0 + 3 • LinearMap.proj row1
def reactionSecond : Module.Dual ℝ (ConstraintIndex duplicateSupports → ℝ) :=
  4 • LinearMap.proj row0 + 1 • LinearMap.proj row1
example : (constraintMap beam duplicateSupports).dualMap reactionFirst =
    (constraintMap beam duplicateSupports).dualMap reactionSecond := by
  ext variation
  simp [reactionFirst, reactionSecond, row0, row1, constraintMap, supportRowLinear, duplicateSupports,
    supportDirections, smul_eq_mul]
  ring
example : reactionFirst - reactionSecond ∈ LinearMap.ker (constraintMap beam duplicateSupports).dualMap := by
  apply (reaction_gauge beam duplicateSupports reactionFirst reactionSecond).mp
  ext variation
  simp [reactionFirst, reactionSecond, row0, row1, constraintMap, supportRowLinear, duplicateSupports,
    supportDirections, smul_eq_mul]
  ring
example : reactionFirst ≠ reactionSecond := by
  intro h
  let probe : ConstraintIndex duplicateSupports → ℝ := fun row => if row.1 = 0 then 1 else 0
  have hvalue := congrArg (fun reaction : Module.Dual ℝ (ConstraintIndex duplicateSupports → ℝ) => reaction probe) h
  norm_num [reactionFirst, reactionSecond, row0, row1, probe] at hvalue
example (first second : ConstraintIndex duplicateSupports → ℝ) (a b : ℝ) :
    aggregateReaction beam duplicateSupports (a • first + b • second) =
      a • aggregateReaction beam duplicateSupports first + b • aggregateReaction beam duplicateSupports second := by
  exact combined_aggregate_reaction beam duplicateSupports first second a b
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "ReuseGaugeCheck.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=PROOFS,
                capture_output=True, text=True, timeout=120, check=False,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_cantilever_signed_displacements_and_fields(self):
        statement = """
import FrameReuse
open FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly FrameDeformation FrameReuse
noncomputable section

def beam : Model 2 1 0 1 where
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

def support : Fin 1 → SupportInput 1 0 := fun _ =>
  ⟨.endSide (0, false), .fixed, 0, 1, false, false, false⟩
def axialMotion : Coordinate beam → ℝ := fun index =>
  match index with
  | .inl (point, direction) => if point.val = .inl 1 ∧ direction = 0 then 1 else 0
  | .inr _ => 0
def momentMotion : Coordinate beam → ℝ := fun index =>
  match index with
  | .inl (point, direction) => if point.val = .inl 1 then
      if direction = 1 then 1/2 else if direction = 2 then 1 else 0 else 0
  | .inr _ => 0

theorem point0 : activePoint beam (.inl 0) := ⟨0, Or.inl rfl⟩
theorem point1 : activePoint beam (.inl 1) := ⟨0, Or.inr rfl⟩
theorem dofs_axial : segmentDofs beam axialMotion 0 = ![0, 0, 0, 1, 0, 0] := by
  have h1 := point1
  dsimp [beam] at h1
  funext i
  fin_cases i <;> simp [segmentDofs, segmentMotion, sideMotion, referenceMotion, endMotion,
    toLocal6, slipValue, axialMotion, beam, endNode, h1]
theorem dofs_moment : segmentDofs beam momentMotion 0 = ![0, 0, 0, 0, 1/2, 1] := by
  have h1 := point1
  dsimp [beam] at h1
  funext i
  fin_cases i <;> simp [segmentDofs, segmentMotion, sideMotion, referenceMotion, endMotion,
    toLocal6, slipValue, momentMotion, beam, endNode, h1]

theorem axial_actions : LocalFrameFields.endActions (segmentDofs beam axialMotion 0) 1 1 1 0 0 0 0 = ![-1, 0, 0, 1, 0, 0] := by
  rw [dofs_axial]
  funext i
  fin_cases i <;> norm_num [LocalFrameFields.endActions, LocalFrameFields.normal, LocalFrameFields.shear,
    LocalFrameFields.moment, LocalFrameFields.rotation, LocalFrameFields.axialDisplacement,
    LocalFrameFields.transverseDisplacement, LocalFrameFields.coordinate, Polynomial.derivative_mul,
    Polynomial.derivative_pow] <;> simp <;> norm_num
theorem moment_actions : LocalFrameFields.endActions (segmentDofs beam momentMotion 0) 1 1 1 0 0 0 0 = ![0, 0, -1, 0, 0, 1] := by
  rw [dofs_moment]
  funext i
  fin_cases i <;> norm_num [LocalFrameFields.endActions, LocalFrameFields.normal, LocalFrameFields.shear,
    LocalFrameFields.moment, LocalFrameFields.rotation, LocalFrameFields.axialDisplacement,
    LocalFrameFields.transverseDisplacement, LocalFrameFields.coordinate, Polynomial.derivative_mul,
    Polynomial.derivative_pow] <;> simp <;> norm_num
example : segmentDofs beam ((2:ℝ) • axialMotion - momentMotion) 0 = ![0, 0, 0, 2, -1/2, -1] := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ momentMotion, segment_dofs_combination, dofs_axial, dofs_moment]
  funext i
  fin_cases i <;> norm_num

def axialLoad : Fin 1 → PointAction 1 0 := fun _ => ⟨.endSide (0, true), ![1, 0, 0]⟩
def momentLoad : Fin 1 → PointAction 1 0 := fun _ => ⟨.endSide (0, true), ![0, 0, 1]⟩
theorem positive : positiveSegments beam := by intro segment; fin_cases segment; norm_num [beam]
theorem law0 : endConnection beam (0, false) = rigidConnection := by rfl
theorem law1 : endConnection beam (0, true) = rigidConnection := by rfl

theorem left_axial : sideMotion beam axialMotion (.endSide (0, false)) = 0 := by
  funext i
  fin_cases i <;> simp [sideMotion, referenceMotion, endMotion, slipValue, axialMotion, beam, endNode]
theorem left_moment : sideMotion beam momentMotion (.endSide (0, false)) = 0 := by
  funext i
  fin_cases i <;> simp [sideMotion, referenceMotion, endMotion, slipValue, momentMotion, beam, endNode]

theorem admissible_of_left_zero (q : Coordinate beam → ℝ)
    (h : sideMotion beam q (.endSide (0, false)) = 0) : admissible beam support q := by
  intro index direction hd
  fin_cases index
  simp [support, supportDirections] at hd
  rcases hd with rfl | rfl | rfl <;> simp [supportRow, FrameTransform.work, support, h]

theorem axial_equilibrium : equilibrium beam axialLoad support axialMotion := by
  constructor
  · exact admissible_of_left_zero axialMotion left_axial
  · intro v hv
    have hx := hv 0 (![1, 0, 0]) (by simp [support, supportDirections])
    have hx0 : segmentDofs beam v 0 0 = 0 := by
      simpa [supportRow, FrameTransform.work, support, segmentDofs, segmentMotion, toLocal6, beam] using hx
    have hp : pointActionWork beam (axialLoad 0) v = segmentDofs beam v 0 3 := by
      simp [pointActionWork, FrameTransform.work, axialLoad, segmentDofs, segmentMotion, toLocal6, beam]
    have ha : recoveredEndActions beam axialMotion 0 = ![-1, 0, 0, 1, 0, 0] := by
      simpa [recoveredEndActions, beam] using axial_actions
    rw [residual_work_from_end_actions beam axialLoad axialMotion v positive]
    simp [Fin.sum_univ_succ, ha, hp, springStiffness, directionLaw, law0, law1, rigidConnection, hx0]

theorem moment_equilibrium : equilibrium beam momentLoad support momentMotion := by
  constructor
  · exact admissible_of_left_zero momentMotion left_moment
  · intro v hv
    have ht := hv 0 (![0, 0, 1]) (by simp [support, supportDirections])
    have ht0 : segmentDofs beam v 0 2 = 0 := by
      simpa [supportRow, FrameTransform.work, support, segmentDofs, segmentMotion, toLocal6, beam] using ht
    have hp : pointActionWork beam (momentLoad 0) v = segmentDofs beam v 0 5 := by
      simp [pointActionWork, FrameTransform.work, momentLoad, segmentDofs, segmentMotion, toLocal6, beam]
    have ha : recoveredEndActions beam momentMotion 0 = ![0, 0, -1, 0, 0, 1] := by
      simpa [recoveredEndActions, beam] using moment_actions
    rw [residual_work_from_end_actions beam momentLoad momentMotion v positive]
    simp [Fin.sum_univ_succ, ha, hp, springStiffness, directionLaw, law0, law1, rigidConnection, ht0]

def slots : Fin 1 → Location 1 0 := fun _ => .endSide (0, true)
def forceComponents : Fin 1 → Triple := fun _ => ![1, 0, 0]
def momentComponents : Fin 1 → Triple := fun _ => ![0, 0, 1]

/-- A separately written record has the same core but a different actual load. -/
def loadedBeam : Model 2 1 0 1 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun _ => ⟨0, 1, ⟨1, 0⟩, none, none⟩
  segmentMember := fun _ => 0
  segmentLeft := fun _ => .endSide (0, false)
  segmentRight := fun _ => .endSide (0, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 2
  segmentVerticalEnd := fun _ => -3

theorem coresMatch : sameCore beam loadedBeam := by rfl
example (q v : Coordinate beam → ℝ) :
    sideMotion beam q (.endSide (0, true)) = sideMotion loadedBeam (sameCoreMotionEquiv beam loadedBeam coresMatch q) (.endSide (0, true)) ∧
    segmentDofs beam q 0 = segmentDofs loadedBeam (sameCoreMotionEquiv beam loadedBeam coresMatch q) 0 ∧
    constraintMap beam support q = constraintMap loadedBeam support (sameCoreMotionEquiv beam loadedBeam coresMatch q) ∧
    stiffnessWork beam q v = stiffnessWork loadedBeam (sameCoreMotionEquiv beam loadedBeam coresMatch q) (sameCoreMotionEquiv beam loadedBeam coresMatch v) ∧
    (admissible beam support q ↔ admissible loadedBeam support (sameCoreMotionEquiv beam loadedBeam coresMatch q)) := by
  exact same_core_actual_transport beam loadedBeam coresMatch support q v (.endSide (0, true)) 0
example (q : Coordinate beam → ℝ) (index : Sum (Fin 1 × Fin 3) (SpringIndex beam)) :
    deformationMap beam q index = deformationMap loadedBeam (sameCoreMotionEquiv beam loadedBeam coresMatch q)
      (Sum.map id (sameCoreSpringEquiv beam loadedBeam coresMatch) index) := by
  exact same_core_deformation_transport beam loadedBeam coresMatch q index

def noCuts : Fin 1 → Fin 0 → ℝ := fun _ => Fin.elim0
def properties : Fin 1 → ℝ := fun _ => 1

theorem cantileverContract : ExactContract (withLoads beam 0 0) (pointActions slots 0) support noCuts
    properties properties properties := by
  constructor
  · intro segment
    fin_cases segment <;> simp [segmentOwnershipValid, locationBelongs, withLoads, beam]
  · intro segment
    fin_cases segment <;> norm_num [withLoads, beam, locationParameter]
  · intro member t ht0 ht1
    fin_cases member
    exact ⟨0, rfl, by simpa [withLoads, beam, locationParameter] using ht0,
      by simpa [withLoads, beam, locationParameter] using ht1⟩
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
    fin_cases action
    exact ⟨0, Or.inr rfl⟩
  · intro index
    fin_cases index
    exact ⟨0, Or.inl rfl⟩
  · intro member
    fin_cases member
    norm_num [withLoads, beam]
  · intro index hkind
    fin_cases index
    simp [support] at hkind
  · intro member
    norm_num [properties]
  · intro segment
    fin_cases segment
    norm_num [withLoads, beam, properties, locationParameter]
  · intro segment
    norm_num [withLoads, beam, properties]
  · intro side direction stiffness hactive hlaw
    change directionLaw (endConnection beam side) direction = .spring stiffness at hlaw
    rcases side with ⟨member, ending⟩
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, law0, law1, rigidConnection] at hlaw
/-- The fixed left end removes all three rigid-body motions of this member. -/
theorem cantileverStable : ∀ q, admissible (withLoads beam 0 0) support q →
    deformationMap (withLoads beam 0 0) q = 0 → q = 0 := by
  classical
  intro q h hD
  have hleft : sideMotion beam q (.endSide (0, false)) = 0 := by
    funext i
    fin_cases i
    · have hx := h 0 (![1, 0, 0]) (by simp [support, supportDirections])
      simpa [supportRow, FrameTransform.work, support] using hx
    · have hy := h 0 (![0, 1, 0]) (by simp [support, supportDirections])
      simpa [supportRow, FrameTransform.work, support] using hy
    · have ht := h 0 (![0, 0, 1]) (by simp [support, supportDirections])
      simpa [supportRow, FrameTransform.work, support] using ht
  have left0 : segmentDofs beam q 0 0 = 0 := by
    simpa [segmentDofs, segmentMotion, toLocal6, beam] using congrFun hleft 0
  have left1 : segmentDofs beam q 0 1 = 0 := by
    simpa [segmentDofs, segmentMotion, toLocal6, beam] using congrFun hleft 1
  have left2 : segmentDofs beam q 0 2 = 0 := by
    simpa [segmentDofs, segmentMotion, toLocal6, beam] using congrFun hleft 2
  have right0 : segmentDofs beam q 0 3 = 0 := by
    have hd := congrFun hD (.inl (0, 0))
    change memberDeformation (segmentDofs beam q 0) 1 0 = 0 at hd
    simpa [memberDeformation, left0] using hd
  have right1 : segmentDofs beam q 0 4 = 0 := by
    have hd := congrFun hD (.inl (0, 1))
    change memberDeformation (segmentDofs beam q 0) 1 1 = 0 at hd
    simp [memberDeformation, FrameEnergy.relativeRotationLeft, left1, left2] at hd
    linarith
  have right2 : segmentDofs beam q 0 5 = 0 := by
    have hd := congrFun hD (.inl (0, 2))
    change memberDeformation (segmentDofs beam q 0) 1 2 = 0 at hd
    simpa [memberDeformation, FrameEnergy.relativeRotationRight, left1, right1] using hd
  have hright : sideMotion beam q (.endSide (0, true)) = 0 := by
    funext i
    fin_cases i
    · simpa [segmentDofs, segmentMotion, toLocal6, beam] using right0
    · simpa [segmentDofs, segmentMotion, toLocal6, beam] using right1
    · simpa [segmentDofs, segmentMotion, toLocal6, beam] using right2
  have law0 : endConnection beam (0, false) = rigidConnection := by rfl
  have law1 : endConnection beam (0, true) = rigidConnection := by rfl
  have hslipLeft : slipValue beam q (0, false) = 0 := by
    funext i
    fin_cases i <;> simp [slipValue, hasSlip, directionLaw, law0, rigidConnection]
  have hslipRight : slipValue beam q (0, true) = 0 := by
    funext i
    fin_cases i <;> simp [slipValue, hasSlip, directionLaw, law1, rigidConnection]
  have hrefLeft : referenceMotion beam q (.inl 0) = 0 := by
    have hv := hleft
    change endMotion 1 0 (referenceMotion beam q (.inl 0)) (slipValue beam q (0, false)) = 0 at hv
    rw [hslipLeft] at hv
    change endMotion 1 0 (referenceMotion beam q (.inl 0)) (fun _ => 0) = 0 at hv
    rw [rigid_end] at hv
    exact hv
  have hrefRight : referenceMotion beam q (.inl 1) = 0 := by
    have hv := hright
    change endMotion 1 0 (referenceMotion beam q (.inl 1)) (slipValue beam q (0, true)) = 0 at hv
    rw [hslipRight] at hv
    change endMotion 1 0 (referenceMotion beam q (.inl 1)) (fun _ => 0) = 0 at hv
    rw [rigid_end] at hv
    exact hv
  funext coordinate
  cases coordinate with
  | inr slip =>
    rcases slip with ⟨⟨⟨member, ending⟩, direction⟩, hactive, hslip⟩
    change directionLaw (endConnection beam (member, ending)) direction ≠ .rigid at hslip
    fin_cases member <;> cases ending <;> fin_cases direction <;>
      simp [directionLaw, law0, law1, rigidConnection] at hslip
  | inl pointDirection =>
    rcases pointDirection with ⟨⟨point, hactive⟩, direction⟩
    cases point with
    | inr cutPoint => exact Fin.elim0 cutPoint.2
    | inl node =>
      fin_cases node
      · have hx := congrFun hrefLeft direction
        change (if hp : activePoint beam (.inl 0) then q (.inl (⟨.inl 0, hp⟩, direction)) else 0) = 0 at hx
        have ha : activePoint beam (.inl 0) := ⟨0, Or.inl rfl⟩
        rw [dif_pos ha] at hx
        simpa using hx
      · have hx := congrFun hrefRight direction
        change (if hp : activePoint beam (.inl 1) then q (.inl (⟨.inl 1, hp⟩, direction)) else 0) = 0 at hx
        have ha : activePoint beam (.inl 1) := ⟨0, Or.inr rfl⟩
        rw [dif_pos ha] at hx
        simpa using hx


theorem boundaryMatches : sameReuseBoundary beam loadedBeam support support slots slots noCuts noCuts :=
  ⟨⟨coresMatch, rfl, rfl⟩, rfl⟩
example : ExactContract loadedBeam (pointActions slots forceComponents) support noCuts properties properties properties := by
  exact (same_boundary_contract_transport beam loadedBeam support slots noCuts properties properties properties
    0 forceComponents boundaryMatches).mp cantileverContract
example : ∀ q, admissible loadedBeam support q → deformationMap loadedBeam q = 0 → q = 0 := by
  exact (same_boundary_no_mechanism_transport beam loadedBeam support slots noCuts boundaryMatches).mp cantileverStable

def axialCase : LoadCase 1 1 := ⟨⟨0, 0⟩, forceComponents⟩
example : stableSolutionLinear beam slots support noCuts properties properties properties
    cantileverContract cantileverStable axialCase = axialMotion := by
  apply equilibrium_unique_if_no_mechanism (caseModel beam axialCase) (caseActions slots axialCase)
    support noCuts properties properties properties
    (case_contract beam slots support noCuts properties properties properties cantileverContract axialCase)
    (case_stable beam support cantileverStable axialCase)
  · exact stable_solution_equilibrium beam slots support noCuts properties properties properties
      cantileverContract cantileverStable axialCase
  · exact axial_equilibrium

theorem combined_equilibrium : equilibrium (withLoads beam (fun i => (2:ℝ)*(0 : Fin 1 → ℝ) i+(-1)*(0 : Fin 1 → ℝ) i)
      (fun i => (2:ℝ)*(0 : Fin 1 → ℝ) i+(-1)*(0 : Fin 1 → ℝ) i))
    (pointActions slots (fun j i => (2:ℝ)*forceComponents j i+(-1)*momentComponents j i)) support
      ((2:ℝ) • axialMotion + (-1:ℝ) • momentMotion) := by
  exact equilibrium_combination beam 2 (-1) 0 0 0 0 slots forceComponents momentComponents support
    axialMotion momentMotion axial_equilibrium moment_equilibrium

example : ∃ first second combined : ConstraintIndex support → ℝ,
    groupedGroundAction beam support combined ⟨.inl 0, point0⟩ 0 =
      2 * groupedGroundAction beam support first ⟨.inl 0, point0⟩ 0 -
        groupedGroundAction beam support second ⟨.inl 0, point0⟩ 0 := by
  obtain ⟨_, first, hfirst⟩ := (equilibrium_iff_reaction_coefficients beam axialLoad support axialMotion positive).mp axial_equilibrium
  obtain ⟨_, second, hsecond⟩ := (equilibrium_iff_reaction_coefficients beam momentLoad support momentMotion positive).mp moment_equilibrium
  let combinedModel := withLoads beam (fun i => (2:ℝ)*(0 : Fin 1 → ℝ) i+(-1)*(0 : Fin 1 → ℝ) i)
    (fun i => (2:ℝ)*(0 : Fin 1 → ℝ) i+(-1)*(0 : Fin 1 → ℝ) i)
  let combinedLoad := pointActions slots (fun j i => (2:ℝ)*forceComponents j i+(-1)*momentComponents j i)
  have hpositive : positiveSegments combinedModel := positive
  obtain ⟨_, combined, hcombined⟩ :=
    (equilibrium_iff_reaction_coefficients combinedModel combinedLoad support
      ((2:ℝ) • axialMotion + (-1:ℝ) • momentMotion) hpositive).mp combined_equilibrium
  refine ⟨first, second, combined, ?_⟩
  have haggregate := aggregate_reaction_from_residuals beam 2 (-1) 0 0 0 0 slots
    forceComponents momentComponents support axialMotion momentMotion first second combined positive
    hfirst hsecond hcombined
  have hgroup := grouped_reaction_from_residuals beam support first second combined 2 (-1)
    haggregate ⟨.inl 0, point0⟩ 0
  linarith
"""
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "ReuseCantileverCheck.lean"
            source.write_text(statement, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=PROOFS,
                capture_output=True, text=True, timeout=120, check=False,
            )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
