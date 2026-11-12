import RationalFrameFreeSpace
import RationalFrameContract

/-! Stable solutions and singular witnesses are interpreted in the actual
    frame deformation space. Zero residual under zero load is never used as
    a stability argument; the positive reduced factor is essential. -/
namespace RationalFrame.Stability
open FrameAssemblyModel FrameAssembly FrameDeformation Interpretation
noncomputable section

theorem no_mechanism (data : Compiled) (valid : PartitionValid data) (certificate : Certificate)
    (factor : FactorValid (stiffnessMatrix data) (freeIndices data) certificate)
    (z : Coordinate (model data valid) → ℝ)
    (restrained : admissible (model data valid) (supports data valid) z)
    (undeformed : deformationMap (model data valid) z = 0) : z = 0 := by
  by_contra nonzero
  let q : Fin data.dofs → ℝ := fun i => z (coordinateEquiv data valid i)
  have represented : motion data valid q = z := motion_complete data valid z
  have finiteNonzero : q ≠ 0 := by
    intro zero
    apply nonzero
    rw [← represented, zero]
    simp [motion]
  have fixed := (Constraints.admissible_finite data valid q)
  rw [represented] at fixed
  have positive := FreeSpace.physical_positive data valid certificate factor q
    (fixed.mp restrained) finiteNonzero
  rw [represented] at positive
  have zeroEnergy := deformation_zero_implies_energy_zero _ _ _ _ _ _ _
    (Contract.exact_contract data valid) z undeformed
  rw [stiffness_work_energy _ z (positive_segments data valid), zeroEnergy] at positive
  norm_num at positive

theorem unique_equilibrium (data : Compiled) (valid : PartitionValid data) (certificate : Certificate)
    (factor : FactorValid (stiffnessMatrix data) (freeIndices data) certificate)
    (q r : Coordinate (model data valid) → ℝ)
    (left : equilibrium (model data valid) (actions data valid) (supports data valid) q)
    (right : equilibrium (model data valid) (actions data valid) (supports data valid) r) : q = r :=
  equilibrium_unique_if_no_mechanism _ _ _ _ _ _ _ (Contract.exact_contract data valid)
    (no_mechanism data valid certificate factor) q r left right

theorem checked_unique (data : Compiled) (valid : PartitionValid data)
    (query : Query) (certificate : Certificate)
    (restrained : Admissible data certificate.motion)
    (solution : SolutionValid data query certificate) :
    let q := motion data valid (fun i => (certificate.motion[i.val]! : ℝ))
    equilibrium (model data valid) (actions data valid) (supports data valid) q ∧
      ∀ other, equilibrium (model data valid) (actions data valid) (supports data valid) other → other = q := by
  have exists := Equations.checked_equilibrium data valid query certificate restrained solution
  exact ⟨exists, fun other checked => unique_equilibrium data valid certificate solution.1 other _ checked exists⟩

/-- A checked full-K null vector is a nonzero admissible deformation-free
    motion of the original frame, including the zero-load case. -/
theorem checked_mechanism (data : Compiled) (valid : PartitionValid data) (certificate : Certificate)
    (restrained : Admissible data certificate.motion) (mechanism : MechanismValid data certificate) :
    let z := motion data valid (fun i => (certificate.motion[i.val]! : ℝ))
    admissible (model data valid) (supports data valid) z ∧ z ≠ 0 ∧
      deformationMap (model data valid) z = 0 := by
  let q : Fin data.dofs → ℝ := fun i => (certificate.motion[i.val]! : ℝ)
  have admissibleMotion := (Constraints.admissible_finite data valid q).mpr
    (fun i hi => by exact_mod_cast restrained.2 i hi)
  refine ⟨admissibleMotion, ?_, ?_⟩
  · intro zero
    apply mechanism.1
    intro i
    have value := congrFun zero (coordinateEquiv data valid i)
    rw [motion_coordinate] at value
    exact_mod_cast value
  · apply (stiffness_null_iff_deformation_zero _ _ _ _ _ _ _
      (Contract.exact_contract data valid) _).mp
    intro variation
    let finiteVariation : Fin data.dofs → ℝ := fun i => variation (coordinateEquiv data valid i)
    have represented : motion data valid finiteVariation = variation := motion_complete data valid variation
    rw [← represented, Work.stiffness_work]
    apply Finset.sum_eq_zero
    intro i _
    have zeroRow := mechanism.2.1 i
    rw [Equations.matrix_dot] at zeroRow
    have castRow := congrArg (fun value : Rat => (value : ℝ)) zeroRow
    push_cast at castRow
    rw [castRow, mul_zero]

end
end RationalFrame.Stability
