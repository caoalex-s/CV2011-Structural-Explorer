import Mathlib

/-! A finite-dimensional inverse-residual certificate. The source bridge must
    establish the operator/residual bounds for the actual constrained system.
    This proves solvability and error, not physical stability by itself. -/
namespace FrameResidualBound
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem injective_of_defect (A R : E →ₗ[ℝ] E) (q : ℝ) (hq : q < 1)
    (hdefect : ∀ x, ‖x - R (A x)‖ ≤ q * ‖x‖) : Function.Injective A := by
  intro x y hxy
  have hz : A (x-y) = 0 := by simp [map_sub, hxy]
  have h := hdefect (x-y)
  rw [hz, map_zero, sub_zero] at h
  have heq : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp heq)

theorem exists_unique_solution (A R : E →ₗ[ℝ] E) (q : ℝ) (hq : q < 1)
    (hdefect : ∀ x, ‖x - R (A x)‖ ≤ q * ‖x‖) (b : E) :
    ∃! x, A x = b := by
  have hinj := injective_of_defect A R q hq hdefect
  have hsurj : Function.Surjective A := (LinearMap.injective_iff_surjective).mp hinj
  obtain ⟨x, hx⟩ := hsurj b
  exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩

theorem solution_error (A R : E →ₗ[ℝ] E) (q eta : ℝ) (hq : q < 1)
    (hdefect : ∀ x, ‖x - R (A x)‖ ≤ q * ‖x‖)
    (b estimate solution : E) (hsolution : A solution = b)
    (hresidual : ‖R (b - A estimate)‖ ≤ eta) :
    ‖solution-estimate‖ ≤ eta / (1-q) := by
  have identity : solution-estimate =
      (solution-estimate - R (A (solution-estimate))) + R (b-A estimate) := by
    rw [map_sub, hsolution]
    abel
  have htriangle := norm_add_le
    (solution-estimate - R (A (solution-estimate))) (R (b-A estimate))
  rw [← identity] at htriangle
  have hbound := hdefect (solution-estimate)
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  nlinarith

end
end FrameResidualBound
