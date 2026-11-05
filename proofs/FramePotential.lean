import FrameVirtualWork
import FrameTransform

/-! The member-side potential uses the actual element energy and load vector.
Only the selected local coordinate varies; the remaining end movements are fixed. -/
open MeasureTheory intervalIntegral
open FrameInterfaces LocalFrameFields FrameEnergy FrameVirtualWork FrameTransform

namespace FramePotential
noncomputable section

def varyingDofs (d : LocalDofs) (i : Fin 6) (delta : ℝ) : LocalDofs :=
  fun j => d j + if j = i then delta else 0

def memberPotential (d : LocalDofs) (i : Fin 6)
    (L EA EI p₀ p₁ q₀ q₁ k pSide delta : ℝ) : ℝ :=
  energy (varyingDofs d i delta) L EA EI -
    (∑ j : Fin 6, consistentLoad L p₀ p₁ q₀ q₁ j * varyingDofs d i delta j) +
    k*delta^2/2 - pSide*delta

set_option maxHeartbeats 8000000 in
/-- The derivative is the derived member end action plus spring and side terms. -/
theorem member_potential_derivative (d : LocalDofs) (i : Fin 6)
    (L EA EI p₀ p₁ q₀ q₁ k pSide delta : ℝ)
    (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0) :
    HasDerivAt (memberPotential d i L EA EI p₀ p₁ q₀ q₁ k pSide)
      (endActions (varyingDofs d i delta) L EA EI p₀ p₁ q₀ q₁ i + k*delta-pSide) delta := by
  let a := (stiffness L EA EI i i + k)/2
  let b := (∑ j : Fin 6, stiffness L EA EI i j*d j) -
    consistentLoad L p₀ p₁ q₀ q₁ i - pSide
  let c := energy d L EA EI - ∑ j : Fin 6, consistentLoad L p₀ p₁ q₀ q₁ j*d j
  have h := (((hasDerivAt_id delta).pow 2).const_mul a).add
    ((hasDerivAt_id delta).const_mul b) |>.add (hasDerivAt_const delta c)
  convert h using 1
  · funext x
    dsimp [memberPotential, varyingDofs, a, b, c, energy, relativeRotationLeft,
      relativeRotationRight]
    fin_cases i <;> simp [stiffness, consistentLoad, Fin.sum_univ_succ] <;> field_simp <;> ring
  · rw [end_actions_from_fields _ _ _ _ _ _ _ _ hL hEA hEI]
    dsimp [varyingDofs, a, b]
    fin_cases i <;> simp [stiffness, consistentLoad, Fin.sum_univ_succ] <;> field_simp <;> ring

/-- At a stationary member-side slip, the actual element end action balances
both the spring force and any action applied directly on that side. -/
theorem member_spring_stationarity (d : LocalDofs) (i : Fin 6)
    (L EA EI p₀ p₁ q₀ q₁ k pSide delta : ℝ)
    (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0)
    (h : HasDerivAt (memberPotential d i L EA EI p₀ p₁ q₀ q₁ k pSide) 0 delta) :
    endActions (varyingDofs d i delta) L EA EI p₀ p₁ q₀ q₁ i + k*delta = pSide := by
  have hd := (member_potential_derivative d i L EA EI p₀ p₁ q₀ q₁ k pSide delta hL hEA hEI).unique h
  linarith

theorem member_free_stationarity (d : LocalDofs) (i : Fin 6)
    (L EA EI p₀ p₁ q₀ q₁ pSide delta : ℝ)
    (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0)
    (h : HasDerivAt (memberPotential d i L EA EI p₀ p₁ q₀ q₁ 0 pSide) 0 delta) :
    endActions (varyingDofs d i delta) L EA EI p₀ p₁ q₀ q₁ i = pSide := by
  simpa using member_spring_stationarity d i L EA EI p₀ p₁ q₀ q₁ 0 pSide delta hL hEA hEI h


/-- Zero-load homogeneous strain work minus distributed load work equals
virtual work of the end actions derived from the exact loaded fields. -/
theorem physical_work_end_actions (d e : LocalDofs)
    (L EA EI p₀ p₁ q₀ q₁ : ℝ) (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0) :
    (∫ x in (0 : ℝ)..L, physicalStrainDensity d e L EA EI x) -
      (∫ x in (0 : ℝ)..L, physicalLoadDensity e L EA EI p₀ p₁ q₀ q₁ x) =
      ∑ i : Fin 6, e i * endActions d L EA EI p₀ p₁ q₀ q₁ i := by
  rw [physical_stiffness_work d e L EA EI hL,
    physical_consistent_load_work e L EA EI p₀ p₁ q₀ q₁ hL]
  simp_rw [end_actions_from_fields d L EA EI p₀ p₁ q₀ q₁ hL hEA hEI]
  simp [Fin.sum_univ_succ]
  ring

/-- Matrix action Tᵀ K T, formed from the same local stiffness. -/
def globalStiffnessAction (c s L EA EI : ℝ) (d : LocalDofs) : LocalDofs :=
  toGlobal6 c s (fun i => ∑ j : Fin 6, stiffness L EA EI i j * toLocal6 c s d j)

/-- Congruence preserves local strain energy in global coordinates. -/
theorem global_stiffness_energy (c s L EA EI : ℝ) (d : LocalDofs) (hL : L ≠ 0) :
    work6 (globalStiffnessAction c s L EA EI d) d =
      2 * energy (toLocal6 c s d) L EA EI := by
  rw [globalStiffnessAction, transpose_work6, energy_stiffness_identity _ _ _ _ hL]
  simp [work6, Fin.sum_univ_succ]
  ring

end
end FramePotential
