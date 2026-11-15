import FrameResidualBound
import FrameReducedStability

/-! Infinity-norm row bounds for the actual finite reduced matrix. These lemmas
    connect interval entry bounds to the abstract inverse-residual argument.
    They do not assert source ownership, assembly correspondence or stability. -/
namespace FrameMatrixResidual
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def action (matrix : ι → ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x i := ∑ j, matrix i j * x j
  map_add' x y := by
    funext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' scalar x := by
    funext i
    simp [Finset.mul_sum, mul_left_comm, mul_assoc]

def defect (matrix inverse : ι → ι → ℝ) (i j : ι) : ℝ :=
  (if i = j then 1 else 0) - ∑ k, inverse i k * matrix k j

theorem row_sum_bound (matrix : ι → ι → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hrows : ∀ i, (∑ j, |matrix i j|) ≤ q) (x : ι → ℝ) :
    ‖action matrix x‖ ≤ q * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg x))).mpr
  intro i
  change ‖∑ j, matrix i j * x j‖ ≤ q * ‖x‖
  calc
    ‖∑ j, matrix i j * x j‖ ≤ ∑ j, ‖matrix i j * x j‖ := norm_sum_le _ _
    _ = ∑ j, |matrix i j| * |x j| := by simp [Real.norm_eq_abs, abs_mul]
    _ ≤ ∑ j, |matrix i j| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
    _ = (∑ j, |matrix i j|) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ q * ‖x‖ := mul_le_mul_of_nonneg_right (hrows i) (norm_nonneg x)

theorem defect_action (matrix inverse : ι → ι → ℝ) (x : ι → ℝ) :
    action (defect matrix inverse) x = x - action inverse (action matrix x) := by
  funext i
  have hproduct : (∑ j, (∑ k, inverse i k * matrix k j) * x j) =
      ∑ k, inverse i k * (∑ j, matrix k j * x j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∑ j, ((if i = j then 1 else 0) - ∑ k, inverse i k * matrix k j) * x j) =
    x i - ∑ k, inverse i k * (∑ j, matrix k j * x j)
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hproduct]
  simp

theorem defect_norm_bound (matrix inverse : ι → ι → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hrows : ∀ i, (∑ j, |defect matrix inverse i j|) ≤ q) :
    ∀ x, ‖x - action inverse (action matrix x)‖ ≤ q * ‖x‖ := by
  intro x
  rw [← defect_action]
  exact row_sum_bound _ q hq hrows x

/-- Entrywise residual and row-sum checks imply unique solvability and a bound
    on every reduced displacement coordinate, including an empty reduced space. -/
theorem enclosed_solution (matrix inverse : ι → ι → ℝ)
    (force estimate : ι → ℝ) (q eta : ℝ)
    (hqzero : 0 ≤ q) (hqone : q < 1) (hetazero : 0 ≤ eta)
    (hrows : ∀ i, (∑ j, |defect matrix inverse i j|) ≤ q)
    (hresidual : ∀ i, |action inverse (force - action matrix estimate) i| ≤ eta) :
    ∃! solution, action matrix solution = force ∧
      ∀ i, estimate i - eta/(1-q) ≤ solution i ∧ solution i ≤ estimate i + eta/(1-q) := by
  have hdefect := defect_norm_bound matrix inverse q hqzero hrows
  have hresidualNorm : ‖action inverse (force - action matrix estimate)‖ ≤ eta := by
    apply (pi_norm_le_iff_of_nonneg hetazero).mpr
    intro i
    simpa [Real.norm_eq_abs] using hresidual i
  obtain ⟨solution, hsolution, hunique⟩ := FrameResidualBound.exists_unique_solution
    (action matrix) (action inverse) q hqone hdefect force
  have herror := FrameResidualBound.solution_error (action matrix) (action inverse)
    q eta hqone hdefect force estimate solution hsolution hresidualNorm
  refine ⟨solution, ⟨hsolution, ?_⟩, ?_⟩
  · intro i
    have hcomponent : |solution i - estimate i| ≤ eta/(1-q) := by
      have h := le_trans (norm_le_pi_norm (solution-estimate) i) herror
      simpa [Real.norm_eq_abs] using h
    have hb := abs_le.mp hcomponent
    constructor <;> linarith
  · intro other hother
    exact hunique other hother.1

/-- The verified inverse establishes positive definiteness only after the
    matrix is identified with the actual symmetric PSD reduced stiffness form.
    Source admissibility and independent columns must be proved before using
    this result as stability of the original constrained frame. -/
theorem positive_stiffness_of_defect
    (matrix inverse : ι → ι → ℝ)
    (form : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] ℝ)
    (q : ℝ) (hqzero : 0 ≤ q) (hqone : q < 1)
    (hrows : ∀ i, (∑ j, |defect matrix inverse i j|) ≤ q)
    (hrepresentation : ∀ x y, form x y = ∑ i, y i * action matrix x i)
    (hsymmetric : ∀ x y, form x y = form y x)
    (hpositive : ∀ x, 0 ≤ form x x) :
    ∀ x, x ≠ 0 → 0 < form x x := by
  have hinjective := FrameResidualBound.injective_of_defect (action matrix) (action inverse)
    q hqone (defect_norm_bound matrix inverse q hqzero hrows)
  apply FrameReducedStability.positive_of_psd_nondegenerate form hsymmetric hpositive
  intro x hnull
  have hzero : action matrix x = 0 := by
    funext i
    have hcomponent := hnull (Pi.single i 1)
    rw [hrepresentation] at hcomponent
    simpa [Pi.single_apply] using hcomponent
  apply hinjective
  simpa using hzero

end
end FrameMatrixResidual
