import RationalFrameChecker
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Finite LDL algebra for the generic checker. The structural interpretation
    must additionally establish that the checked reduced matrix is the actual
    constrained frame operator. These lemmas alone make no such claim. -/
open scoped BigOperators Matrix
namespace RationalFrame.Algebra
noncomputable section

/-- Back substitution proves that a unit upper triangular map has no kernel.
    The induction is on distance from the last row, so n=0 is included. -/
theorem unitUpper_kernel {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℝ)
    (triangle : ∀ i j, j < i → matrix i j = 0)
    (diagonal : ∀ i, matrix i i = 1) (x : Fin n → ℝ)
    (null : matrix *ᵥ x = 0) : x = 0 := by
  have entry : ∀ k : Nat, ∀ i : Fin n, n - 1 - i.val = k → x i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      have offDiagonal (j : Fin n) (hne : j ≠ i) : matrix i j * x j = 0 := by
        by_cases hji : j < i
        · rw [triangle i j hji, zero_mul]
        · have hij : i.val < j.val := by
            have hne' : j.val ≠ i.val := fun heq => hne (Fin.ext heq)
            have := i.isLt
            have := j.isLt
            change ¬ j.val < i.val at hji
            omega
          have hmeasure : n - 1 - j.val < k := by omega
          rw [ih _ hmeasure j rfl, mul_zero]
      have row := congrFun null i
      change (∑ j : Fin n, matrix i j * x j) = 0 at row
      rw [Finset.sum_eq_single i] at row
      · simpa [diagonal] using row
      · intro j _ hne
        exact offDiagonal j hne
      · simp
  funext i
  exact entry _ i rfl

theorem unitUpper_injective {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℝ)
    (triangle : ∀ i j, j < i → matrix i j = 0)
    (diagonal : ∀ i, matrix i i = 1) : Function.Injective matrix.mulVec := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply unitUpper_kernel matrix triangle diagonal
  simp [Matrix.mulVec_sub, hxy]

/-- A checked unit-lower/positive-diagonal factor gives strict positivity,
    including the vacuous fully restrained (zero free coordinate) case. -/
theorem positiveLDL {n : Nat} (lower : Matrix (Fin n) (Fin n) ℝ) (pivot : Fin n → ℝ)
    (triangle : ∀ i j, i < j → lower i j = 0)
    (diagonal : ∀ i, lower i i = 1) (positive : ∀ i, 0 < pivot i) :
    (lower * Matrix.diagonal pivot * lower.transpose).PosDef := by
  have htranspose : Function.Injective lower.transpose.mulVec :=
    unitUpper_injective lower.transpose (fun i j h => triangle j i h) diagonal
  have hinjective : Function.Injective lower.vecMul := by
    intro x y h
    apply htranspose
    simpa only [Matrix.mulVec, Matrix.vecMul, Matrix.transpose_apply,
      dotProduct, mul_comm] using h
  have hp := (Matrix.PosDef.diagonal positive).mul_mul_conjTranspose_same hinjective
  simpa [Matrix.conjTranspose] using hp

end
end RationalFrame.Algebra
