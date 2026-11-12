import RationalFrameEquations
import Mathlib.Data.List.Nodup

/-! The reduced coordinate list enumerates the entire actual free space
    without repetitions. Its positive LDL certificate therefore controls
    every admissible physical motion, including the empty free-space case. -/
namespace RationalFrame.FreeSpace
open FrameAssemblyModel Interpretation
noncomputable section

theorem index_properties (data : Compiled) (i : Fin (freeIndices data).size) :
    (freeIndices data)[i.val]! < data.dofs ∧ blocked data (freeIndices data)[i.val]! = false := by
  apply (Algebra.freeIndices_complete data _).mp
  simp [getElem!_pos]

def index (data : Compiled) (i : Fin (freeIndices data).size) : Fin data.dofs :=
  ⟨(freeIndices data)[i.val]!, (index_properties data i).1⟩

theorem index_injective (data : Compiled) : Function.Injective (index data) := by
  intro i j same
  apply Fin.ext
  have sameValues := congrArg Fin.val same
  have noDuplicates := Algebra.freeIndices_no_duplicates data
  apply noDuplicates.getElem_inj_iff.mp
  simpa [index, getElem!_pos] using sameValues

theorem index_complete (data : Compiled) (i : Fin data.dofs) :
    (∃ j : Fin (freeIndices data).size, index data j = i) ↔ blocked data i.val = false := by
  constructor
  · rintro ⟨j, rfl⟩
    exact (index_properties data j).2
  · intro unblocked
    have member := (Algebra.freeIndices_complete data i.val).mpr ⟨i.isLt, unblocked⟩
    obtain ⟨j, hj, same⟩ := List.mem_iff_getElem.mp member
    have inBounds : j < (freeIndices data).size := by simpa using hj
    refine ⟨⟨j, inBounds⟩, ?_⟩
    apply Fin.ext
    simpa [index, getElem!_pos, inBounds] using same

theorem sum_free (data : Compiled) (values : Fin data.dofs → ℝ)
    (zeroBlocked : ∀ i, blocked data i.val = true → values i = 0) :
    (∑ i : Fin data.dofs, values i) = ∑ j : Fin (freeIndices data).size, values (index data j) := by
  symm
  apply Fintype.sum_of_injective (index data) (index_injective data)
  · intro i absent
    apply zeroBlocked i
    have notFree : blocked data i.val ≠ false := by
      intro free
      obtain ⟨j, same⟩ := (index_complete data i).mpr free
      exact absent j same
    cases h : blocked data i.val <;> simp_all
  · intro j
    rfl

theorem quadratic_reduction (data : Compiled) (q : Fin data.dofs → ℝ)
    (zeroBlocked : ∀ i, blocked data i.val = true → q i = 0) :
    (∑ i : Fin data.dofs, q i *
      (∑ j : Fin data.dofs, (RationalFrame.stiffnessEntry data i.val j.val : ℝ) * q j)) =
    ∑ i : Fin (freeIndices data).size, q (index data i) *
      (∑ j : Fin (freeIndices data).size,
        (RationalFrame.stiffnessEntry data (index data i).val (index data j).val : ℝ) * q (index data j)) := by
  rw [sum_free data _ (by intro i hi; rw [zeroBlocked i hi, zero_mul])]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply sum_free data
  intro j hj
  rw [zeroBlocked j hj, mul_zero]

theorem restricted_nonzero (data : Compiled) (q : Fin data.dofs → ℝ)
    (zeroBlocked : ∀ i, blocked data i.val = true → q i = 0) (nonzero : q ≠ 0) :
    (fun i : Fin (freeIndices data).size => q (index data i)) ≠ 0 := by
  intro vanishes
  apply nonzero
  funext i
  by_cases fixed : blocked data i.val = true
  · exact zeroBlocked i fixed
  · have free : blocked data i.val = false := by cases h : blocked data i.val <;> simp_all
    obtain ⟨j, rfl⟩ := (index_complete data i).mpr free
    exact congrFun vanishes j

/-- Positive reduced factors control every nonzero mask-admissible motion.
    The matrix entries here are exactly those computed by the public checker. -/
theorem factor_positive (data : Compiled) (certificate : Certificate)
    (factor : FactorValid (stiffnessMatrix data) (freeIndices data) certificate)
    (q : Fin data.dofs → ℝ)
    (zeroBlocked : ∀ i, blocked data i.val = true → q i = 0) (nonzero : q ≠ 0) :
    0 < ∑ i : Fin data.dofs, q i *
      (∑ j : Fin data.dofs, (RationalFrame.stiffnessEntry data i.val j.val : ℝ) * q j) := by
  rw [quadratic_reduction data q zeroBlocked]
  let reduced : Fin (freeIndices data).size → ℝ := fun i => q (index data i)
  have positive := Algebra.checked_factor_positive (stiffnessMatrix data) (freeIndices data) certificate factor
  have value := positive.2 reduced (restricted_nonzero data q zeroBlocked nonzero)
  have entry (i j : Fin (freeIndices data).size) :
      (((stiffnessMatrix data)[(freeIndices data)[i.val]!]!)[(freeIndices data)[j.val]!]! : ℝ) =
        (RationalFrame.stiffnessEntry data (index data i).val (index data j).val : ℝ) :=
    congrArg (fun value : Rat => (value : ℝ)) (Equations.matrix_entry data (index data i) (index data j))
  simpa only [dotProduct, Matrix.mulVec, entry, star_trivial, reduced] using value

theorem physical_positive (data : Compiled) (valid : PartitionValid data) (certificate : Certificate)
    (factor : FactorValid (stiffnessMatrix data) (freeIndices data) certificate)
    (q : Fin data.dofs → ℝ)
    (zeroBlocked : ∀ i, blocked data i.val = true → q i = 0) (nonzero : q ≠ 0) :
    0 < FrameAssembly.stiffnessWork (model data valid) (motion data valid q) (motion data valid q) := by
  rw [Work.stiffness_work]
  exact factor_positive data certificate factor q zeroBlocked nonzero

end
end RationalFrame.FreeSpace
