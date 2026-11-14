import Mathlib

/-! Algebra needed to turn a verified reduced inverse into physical stability.
    The source bridge must separately establish the symmetric PSD stiffness
    form and the admissible basis. Invertibility alone is not sufficient. -/
namespace FrameReducedStability
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A zero-energy direction of a symmetric PSD form is orthogonal to every
    direction. The chosen test vector avoids division by a possibly zero energy. -/
theorem null_orthogonal (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsymmetric : ∀ x y, B x y = B y x)
    (hpositive : ∀ x, 0 ≤ B x x) {x : E} (hzero : B x x = 0) :
    ∀ y, B x y = 0 := by
  intro y
  have hy := hpositive y
  have htest := hpositive ((B y y + 1) • x - B x y • y)
  have hexpand :
      B ((B y y + 1) • x - B x y • y) ((B y y + 1) • x - B x y • y) =
      -(B y y + 2) * (B x y)^2 := by
    simp [map_sub, map_smul, smul_eq_mul, hsymmetric y x, hzero]
    ring
  rw [hexpand] at htest
  have hproduct := mul_nonneg hy (sq_nonneg (B x y))
  nlinarith [sq_nonneg (B x y)]

theorem positive_of_psd_nondegenerate (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsymmetric : ∀ x y, B x y = B y x)
    (hpositive : ∀ x, 0 ≤ B x x)
    (hnondegenerate : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∀ x, x ≠ 0 → 0 < B x x := by
  intro x hx
  have hnonzero : B x x ≠ 0 := by
    intro hz
    exact hx (hnondegenerate x (null_orthogonal B hsymmetric hpositive hz))
  exact lt_of_le_of_ne (hpositive x) (Ne.symm hnonzero)

/-- Pulling global stiffness back through an admissible basis preserves PSD.
    The injectivity/nondegeneracy obligations are deliberately not inferred here. -/
theorem pullback_nonnegative {F : Type*} [AddCommGroup F] [Module ℝ F]
    (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : E →ₗ[ℝ] F)
    (hpositive : ∀ d, 0 ≤ B d d) : ∀ x, 0 ≤ B (P x) (P x) := by
  intro x
  exact hpositive (P x)

end
end FrameReducedStability
