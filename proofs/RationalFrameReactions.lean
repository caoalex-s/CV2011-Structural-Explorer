import RationalFrameEquations

/-! Reported reactions are the actual grouped ground actions. Repeated
    support rows may have different multiplier shares with the same sum. -/
namespace RationalFrame.Reactions
open FrameAssemblyModel FrameAssembly Interpretation
noncomputable section

theorem residual_coordinate (data : Compiled) (valid : PartitionValid data)
    (values : Array Rat) (i : Fin data.dofs) :
    ((residual (stiffnessMatrix data) (forceVector data) values)[i.val]! : ℝ) =
      residualFunctional (model data valid) (actions data valid)
        (motion data valid (fun j => (values[j.val]! : ℝ)))
        (coordinateBasis (model data valid) (coordinateEquiv data valid i)) := by
  rw [Equations.residual_entry]
  change _ = residualWork _ _ _ _
  rw [Assembly.basis_motion, Work.residual_work]
  simp [Fin.ext_iff]

theorem checked_grouped_reactions (data : Compiled) (valid : PartitionValid data)
    (query : Query) (certificate : Certificate)
    (restrained : Admissible data certificate.motion)
    (solution : SolutionValid data query certificate) :
    ∃ coefficients : ConstraintIndex (supports data valid) → ℝ,
      ∀ (point : ActivePoint (model data valid)) (direction : Fin 3),
        (certificate.reactions[((coordinateEquiv data valid).symm (.inl (point, direction))).val]! : ℝ) =
          groupedGroundAction (model data valid) (supports data valid) coefficients point direction := by
  have equilibrium := Equations.checked_equilibrium data valid query certificate restrained solution
  obtain ⟨_, coefficients, aggregate⟩ := (equilibrium_iff_reaction_coefficients _ _ _ _
    (positive_segments data valid)).mp equilibrium
  refine ⟨coefficients, ?_⟩
  intro point direction
  rw [solution.2.1, residual_coordinate, aggregate]
  simp [groupedGroundAction]

end
end RationalFrame.Reactions
