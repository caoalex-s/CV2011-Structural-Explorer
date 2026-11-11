import RationalFrameChecker
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Finite LDL algebra for the generic checker. The structural interpretation
    must additionally establish that the checked reduced matrix is the actual
    constrained frame operator. These lemmas alone make no such claim. -/
open scoped BigOperators Matrix
namespace RationalFrame.Algebra
noncomputable section

theorem sumFin_eq_sum (n : Nat) (f : Fin n → Rat) : sumFin n f = ∑ i, f i := by
  rw [Fin.sum_univ_def]
  rfl

/-- The source-derived mask enumerates every free coordinate and no other one. -/
theorem freeIndices_complete (model : Compiled) (i : Nat) :
    i ∈ (freeIndices model).toList ↔ i < model.dofs ∧ blocked model i = false := by
  simp [freeIndices, List.mem_filter, Bool.not_eq_true]

theorem freeIndices_no_duplicates (model : Compiled) : (freeIndices model).toList.Nodup := by
  simpa [freeIndices] using (show (List.range model.dofs).Nodup from List.nodup_range).filter (fun i => !blocked model i)

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
    simpa only [Matrix.mulVec_transpose] using h
  have hd : (Matrix.diagonal pivot).PosDef := by
    refine ⟨Matrix.isHermitian_diagonal_of_self_adjoint _ (by rfl), ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hsum : 0 < ∑ j : Fin n, pivot j * (x j)^2 :=
      Finset.sum_pos' (fun j _ => mul_nonneg (positive j).le (sq_nonneg (x j)))
        ⟨i, Finset.mem_univ i, mul_pos (positive i) (sq_pos_of_ne_zero hi)⟩
    simpa [Matrix.mulVec_diagonal, dotProduct, pow_two, mul_assoc, mul_comm, mul_left_comm] using hsum
  have hp := hd.mul_mul_conjTranspose_same hinjective
  simpa [Matrix.conjTranspose] using hp

/-- This uses the actual predicate's rational factor entries, cast exactly to
    reals. It does not posit a separate inverse, factor, or matrix equality. -/
theorem checked_factor_positive (matrix : Array (Array Rat)) (free : Array Nat) (certificate : Certificate)
    (checked : FactorValid matrix free certificate) :
    (fun i j : Fin free.size => ((matrix[free[i.val]!]!)[free[j.val]!]! : ℝ)).PosDef := by
  rcases checked with ⟨_, _, _, hdiagonal, htriangle, hfactor⟩
  let lower : Matrix (Fin free.size) (Fin free.size) ℝ :=
    fun i j => ((certificate.lower[i.val]!)[j.val]! : ℝ)
  let pivot : Fin free.size → ℝ := fun i => (certificate.diagonal[i.val]! : ℝ)
  have htri : ∀ i j, i < j → lower i j = 0 := by
    intro i j hij
    exact_mod_cast htriangle i j hij
  have hunit : ∀ i, lower i i = 1 := by
    intro i
    exact_mod_cast (hdiagonal i).2
  have hpos : ∀ i, 0 < pivot i := by
    intro i
    exact_mod_cast (hdiagonal i).1
  have heq : (fun i j : Fin free.size => ((matrix[free[i.val]!]!)[free[j.val]!]! : ℝ)) =
      lower * Matrix.diagonal pivot * lower.transpose := by
    ext i j
    have h := congrArg (fun value : Rat => (value : ℝ)) (hfactor i j)
    rw [sumFin_eq_sum] at h
    push_cast at h
    simpa [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.transpose_apply, lower, pivot] using h.symm
  rw [heq]
  exact positiveLDL lower pivot htri hunit hpos

end
end RationalFrame.Algebra
