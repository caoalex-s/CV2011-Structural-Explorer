import LocalFrameFields

/-!
Strain energy and rigid motions for one local Euler–Bernoulli frame segment.
The theorem relating this energy to the field integrals and virtual work is a
separate obligation; a matrix identity alone does not establish that link.
-/
open FrameInterfaces LocalFrameFields

namespace FrameEnergy

noncomputable section

def relativeRotationLeft (d : LocalDofs) (L : ℝ) : ℝ := d 2 - (d 4-d 1)/L

def relativeRotationRight (d : LocalDofs) (L : ℝ) : ℝ := d 5 - (d 4-d 1)/L

/-- Candidate homogeneous strain energy in terms of axial extension and end
rotations relative to the member chord. -/
def energy (d : LocalDofs) (L EA EI : ℝ) : ℝ :=
  let left := relativeRotationLeft d L
  let right := relativeRotationRight d L
  EA/(2*L)*(d 3-d 0)^2 + (2*EI/L)*(left^2+left*right+right^2)

def rigidMotion (A B omega L : ℝ) : LocalDofs := ![A, B, omega, A, B+L*omega, omega]

/-- The candidate energy equals half the stiffness quadratic form. -/
theorem energy_stiffness_identity (d : LocalDofs) (L EA EI : ℝ) (hL : L ≠ 0) :
    energy d L EA EI = (∑ i : Fin 6, ∑ j : Fin 6, d i * stiffness L EA EI i j * d j) / 2 := by
  simp [energy, relativeRotationLeft, relativeRotationRight, stiffness, Fin.sum_univ_succ]
  field_simp
  ring

/-- Positive rigidities and length make the quadratic energy nonnegative. -/
theorem energy_nonnegative (d : LocalDofs) (L EA EI : ℝ)
    (hL : 0 < L) (hEA : 0 < EA) (hEI : 0 < EI) : 0 ≤ energy d L EA EI := by
  have hquad : 0 ≤ (relativeRotationLeft d L)^2 + relativeRotationLeft d L * relativeRotationRight d L +
      (relativeRotationRight d L)^2 := by
    nlinarith [sq_nonneg (relativeRotationLeft d L + relativeRotationRight d L),
      sq_nonneg (relativeRotationLeft d L), sq_nonneg (relativeRotationRight d L)]
  unfold energy
  exact add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) hquad)

/-- All three physical rigid motions have zero candidate strain energy. -/
theorem rigid_energy_zero (A B omega L EA EI : ℝ) (hL : L ≠ 0) :
    energy (rigidMotion A B omega L) L EA EI = 0 := by
  simp [energy, relativeRotationLeft, relativeRotationRight, rigidMotion]
  field_simp
  ring


/-- The candidate energy vanishes only for the three rigid motions. -/
theorem energy_zero_rigid (d : LocalDofs) (L EA EI : ℝ)
    (hL : 0 < L) (hEA : 0 < EA) (hEI : 0 < EI)
    (hzero : energy d L EA EI = 0) :
    ∃ A B omega, d = rigidMotion A B omega L := by
  let left := relativeRotationLeft d L
  let right := relativeRotationRight d L
  have hquad : 0 ≤ left^2 + left*right + right^2 := by
    nlinarith [sq_nonneg (left+right), sq_nonneg left, sq_nonneg right]
  have hA : 0 < EA/(2*L) := by positivity
  have hB : 0 < 2*EI/L := by positivity
  have htermA : 0 ≤ EA/(2*L)*(d 3-d 0)^2 := mul_nonneg hA.le (sq_nonneg _)
  have htermB : 0 ≤ (2*EI/L)*(left^2+left*right+right^2) := mul_nonneg hB.le hquad
  have hsum : EA/(2*L)*(d 3-d 0)^2 + (2*EI/L)*(left^2+left*right+right^2) = 0 := by
    simpa [energy, left, right] using hzero
  have haxialTerm : EA/(2*L)*(d 3-d 0)^2 = 0 := by linarith
  have hbendingTerm : (2*EI/L)*(left^2+left*right+right^2) = 0 := by linarith
  have haxialSquare : (d 3-d 0)^2 = 0 := (mul_eq_zero.mp haxialTerm).resolve_left (ne_of_gt hA)
  have hquadratic : left^2+left*right+right^2 = 0 := (mul_eq_zero.mp hbendingTerm).resolve_left (ne_of_gt hB)
  have haxial : d 3 = d 0 := by nlinarith
  have hleft : left = 0 := by nlinarith [sq_nonneg (left+2*right), sq_nonneg left]
  have hright : right = 0 := by nlinarith [sq_nonneg (2*left+right), sq_nonneg right]
  have hθ : d 5 = d 2 := by
    dsimp [left, right, relativeRotationLeft, relativeRotationRight] at hleft hright
    linarith
  have hchord : d 4 = d 1 + L*d 2 := by
    dsimp [left, relativeRotationLeft] at hleft
    have hLne : L ≠ 0 := ne_of_gt hL
    field_simp at hleft
    nlinarith
  refine ⟨d 0, d 1, d 2, ?_⟩
  funext i
  fin_cases i <;> simp [rigidMotion, haxial, hθ, hchord]



/-- The candidate stiffness annihilates each rigid-motion vector. -/
theorem rigid_stiffness_zero (A B omega L EA EI : ℝ) (hL : L ≠ 0) (i : Fin 6) :
    (∑ j : Fin 6, stiffness L EA EI i j * rigidMotion A B omega L j) = 0 := by
  fin_cases i <;> simp [stiffness, rigidMotion, Fin.sum_univ_succ] <;> field_simp <;> ring

/-- The kernel is exactly the parameterised three-rigid-motion family. -/
theorem stiffness_kernel_rigid (d : LocalDofs) (L EA EI : ℝ)
    (hL : 0 < L) (hEA : 0 < EA) (hEI : 0 < EI) :
    (∀ i : Fin 6, ∑ j : Fin 6, stiffness L EA EI i j * d j = 0) ↔
      ∃ A B omega, d = rigidMotion A B omega L := by
  constructor
  · intro hkernel
    have henergy : energy d L EA EI = 0 := by
      rw [energy_stiffness_identity d L EA EI (ne_of_gt hL)]
      simp [← Finset.mul_sum, hkernel]
    exact energy_zero_rigid d L EA EI hL hEA hEI henergy
  · rintro ⟨A, B, omega, rfl⟩ i
    exact rigid_stiffness_zero A B omega L EA EI (ne_of_gt hL) i


end
end FrameEnergy
