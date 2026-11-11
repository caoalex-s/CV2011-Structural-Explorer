import RationalFrameWork

/-! Array witnesses and their full finite real equations. These lemmas make
    the row counts and in-bounds accesses explicit before transporting any
    checked residual or null-vector equation to actual virtual work. -/
namespace RationalFrame.Equations
open FrameAssemblyModel FrameAssembly Interpretation
noncomputable section

theorem matrix_size (data : Compiled) : (stiffnessMatrix data).size = data.dofs := by
  simp [stiffnessMatrix]

theorem matrix_row (data : Compiled) (i : Fin data.dofs) :
    (stiffnessMatrix data)[i.val]! =
      ((List.range data.dofs).map (fun j => RationalFrame.stiffnessEntry data i.val j)).toArray := by
  simp [stiffnessMatrix, i.isLt]

theorem matrix_entry (data : Compiled) (i j : Fin data.dofs) :
    ((stiffnessMatrix data)[i.val]!)[j.val]! = RationalFrame.stiffnessEntry data i.val j.val := by
  rw [matrix_row]
  simp [j.isLt]

theorem force_entry (data : Compiled) (i : Fin data.dofs) :
    (forceVector data)[i.val]! = RationalFrame.forceEntry data i.val := by
  simp [forceVector, i.isLt]

theorem matrix_dot (data : Compiled) (q : Array Rat) (i : Fin data.dofs) :
    arrayDot (stiffnessMatrix data)[i.val]! q =
      ∑ j : Fin data.dofs, RationalFrame.stiffnessEntry data i.val j.val * q[j.val]! := by
  rw [arrayDot, matrix_row]
  simp [Algebra.sumFin_eq_sum]

theorem residual_entry (data : Compiled) (q : Array Rat) (i : Fin data.dofs) :
    (residual (stiffnessMatrix data) (forceVector data) q)[i.val]! =
      (∑ j : Fin data.dofs, RationalFrame.stiffnessEntry data i.val j.val * q[j.val]!) -
        RationalFrame.forceEntry data i.val := by
  simp only [residual]
  simp [matrix_size, i.isLt, matrix_dot, force_entry]

theorem checked_equilibrium (data : Compiled) (valid : PartitionValid data)
    (query : Query) (certificate : Certificate)
    (restrained : Admissible data certificate.motion)
    (solution : SolutionValid data query certificate) :
    equilibrium (model data valid) (actions data valid) (supports data valid)
      (motion data valid (fun i => (certificate.motion[i.val]! : ℝ))) := by
  have admissibleMotion := (Constraints.admissible_iff_mask data valid
    (fun i => (certificate.motion[i]! : ℝ))).mpr
      (fun i hi => by exact_mod_cast restrained.2 i hi)
  refine ⟨admissibleMotion, ?_⟩
  intro variation variationAdmissible
  let finiteVariation : Fin data.dofs → ℝ := fun i => variation (coordinateEquiv data valid i)
  have variationEquals : motion data valid finiteVariation = variation := motion_complete data valid variation
  rw [← variationEquals, Work.residual_work]
  apply Finset.sum_eq_zero
  intro i _
  by_cases blockedHere : blocked data i.val = true
  · have mask := (Constraints.admissible_iff_mask data valid
        (fun index => if h : index < data.dofs then finiteVariation ⟨index, h⟩ else 0))
    have movementEquals :
        (fun j : Fin data.dofs => if h : j.val < data.dofs then finiteVariation ⟨j.val, h⟩ else 0) =
          finiteVariation := by funext j; simp [j.isLt]
    rw [movementEquals, variationEquals] at mask
    have zeroHere := mask.mp variationAdmissible i blockedHere
    have zeroValue : finiteVariation i = 0 := by simpa [i.isLt] using zeroHere
    rw [zeroValue, zero_mul]
  · have freeHere : blocked data i.val = false := Bool.eq_false_iff.mpr blockedHere
    have zeroResidual := solution.2.2.2.2 i freeHere
    rw [solution.2.1, residual_entry] at zeroResidual
    have castResidual := congrArg (fun value : Rat => (value : ℝ)) zeroResidual
    push_cast at castResidual
    rw [castResidual, mul_zero]

end
end RationalFrame.Equations
