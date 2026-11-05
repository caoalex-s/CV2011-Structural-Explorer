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
example : externalWork (withLoads beam 0 0) (pointActions slots loadZero) up = 0 := by
  simp [externalWork, segmentLoad, withLoads, LocalFrameFields.consistentLoad,
    pointActions, pointActionWork, loadZero, FrameTransform.work]
example : externalWork (withLoads beam (fun _ => 1) (fun _ => 1)) (pointActions slots loadSigned) up = -1 := by
  have h0 := node0active
  have h1 := node1active
  dsimp [beam] at h0 h1
  simp [externalWork, segmentLoad, segmentDofs, segmentMotion, sideMotion, referenceMotion,
    endMotion, toLocal6, slipValue, withLoads, beam, endNode, pointActions, slots, loadSigned, up,
    LocalFrameFields.consistentLoad, pointActionWork, FrameTransform.work, h0, h1, Fin.sum_univ_succ]
  norm_num
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
