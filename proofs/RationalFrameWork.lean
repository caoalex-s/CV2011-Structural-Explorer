import RationalFrameAssembly
import RationalFrameConstraints

/-! Finite work expansions connect checked array equations with equilibrium
    on every actual frame variation, not just the tested coordinate vectors. -/
namespace RationalFrame.Work
open FrameAssemblyModel FrameAssembly FrameDeformation Interpretation
noncomputable section

theorem motion_expansion (data : Compiled) (valid : PartitionValid data) (q : Fin data.dofs → ℝ) :
    motion data valid q = ∑ i : Fin data.dofs,
      q i • coordinateBasis (model data valid) (coordinateEquiv data valid i) := by
  classical
  funext coordinate
  obtain ⟨j, rfl⟩ := (coordinateEquiv data valid).surjective coordinate
  rw [motion_coordinate]
  simp [coordinateBasis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem functional_expansion (data : Compiled) (valid : PartitionValid data)
    (functional : Module.Dual ℝ (Coordinate (model data valid) → ℝ)) (q : Fin data.dofs → ℝ) :
    functional (motion data valid q) = ∑ i : Fin data.dofs,
      q i * functional (coordinateBasis (model data valid) (coordinateEquiv data valid i)) := by
  rw [motion_expansion, map_sum]
  simp [map_smul, smul_eq_mul]

theorem stiffness_work (data : Compiled) (valid : PartitionValid data)
    (q variation : Fin data.dofs → ℝ) :
    stiffnessWork (model data valid) (motion data valid q) (motion data valid variation) =
      ∑ i : Fin data.dofs, variation i *
        (∑ j : Fin data.dofs, (RationalFrame.stiffnessEntry data i.val j.val : ℝ) * q j) := by
  rw [← stiffness_operator_apply, functional_expansion]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [stiffness_operator_apply, stiffness_work_symmetric, ← stiffness_operator_apply,
    functional_expansion]
  apply Finset.sum_congr rfl
  intro j _
  rw [stiffness_operator_apply, stiffness_work_symmetric]
  rw [Assembly.stiffness_entry data valid i j]
  simp [FrameAssembly.stiffnessEntry, mul_comm]

theorem external_work (data : Compiled) (valid : PartitionValid data) (variation : Fin data.dofs → ℝ) :
    externalWork (model data valid) (actions data valid) (motion data valid variation) =
      ∑ i : Fin data.dofs, variation i * (RationalFrame.forceEntry data i.val : ℝ) := by
  rw [← external_functional_apply, functional_expansion]
  apply Finset.sum_congr rfl
  intro i _
  rw [external_functional_apply, Assembly.force_entry data valid i]
  rfl

theorem residual_work (data : Compiled) (valid : PartitionValid data)
    (q variation : Fin data.dofs → ℝ) :
    residualWork (model data valid) (actions data valid) (motion data valid q) (motion data valid variation) =
      ∑ i : Fin data.dofs, variation i *
        ((∑ j : Fin data.dofs, (RationalFrame.stiffnessEntry data i.val j.val : ℝ) * q j) -
          (RationalFrame.forceEntry data i.val : ℝ)) := by
  change stiffnessWork _ _ _ - externalWork _ _ _ = _
  rw [stiffness_work, external_work]
  simp only [mul_sub, Finset.sum_sub_distrib]

end
end RationalFrame.Work
