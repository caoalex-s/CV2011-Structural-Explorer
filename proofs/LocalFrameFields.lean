import FrameInterfaces

/-!
One prismatic Euler–Bernoulli segment under affine local distributed loads.
The member coordinate x runs from 0 to L. The local force intensities qx and qy
are positive in the local axial and transverse directions. This library does not
certify the browser's geometry, support assembly, or floating-point solver.
-/
open Polynomial
open FrameInterfaces RealBeamFields

namespace LocalFrameFields

noncomputable section

/-- Dimensionless polynomial coordinate x/L, with L nonzero in theorems. -/
def coordinate (L : ℝ) : Field := C (1/L) * X

/-- Exact axial displacement including the affine-load particular solution. -/
def axialDisplacement (d : LocalDofs) (L EA p₀ p₁ : ℝ) : Field :=
  let z := coordinate L
  C (d 0) * (1-z) + C (d 3) * z + C (L^2 / (6*EA)) *
    (C p₀ * (2*z - 3*z^2 + z^3) + C p₁ * (z-z^3))

/-- Exact transverse displacement, including the affine-load particular field. -/
def transverseDisplacement (d : LocalDofs) (L EI q₀ q₁ : ℝ) : Field :=
  let z := coordinate L
  C (d 1) * (1-3*z^2+2*z^3) + C (L*d 2) * (z-2*z^2+z^3) +
  C (d 4) * (3*z^2-2*z^3) + C (L*d 5) * (z^3-z^2) +
  C (L^4/(120*EI)) * z^2*(z-1)^2 * (C (q₁-q₀)*(z+2)+C (5*q₀))

def rotation (d : LocalDofs) (L EI q₀ q₁ : ℝ) : Field :=
  (transverseDisplacement d L EI q₀ q₁).derivative

def normal (d : LocalDofs) (L EA p₀ p₁ : ℝ) : Field :=
  C EA * (axialDisplacement d L EA p₀ p₁).derivative

def moment (d : LocalDofs) (L EI q₀ q₁ : ℝ) : Field :=
  C EI * (rotation d L EI q₀ q₁).derivative

def shear (d : LocalDofs) (L EI q₀ q₁ : ℝ) : Field :=
  (moment d L EI q₀ q₁).derivative

/-- Applied end actions on the element. These signs are distinct from the
internal-force signs on the retained left segment. -/
def endActions (d : LocalDofs) (L EA EI p₀ p₁ q₀ q₁ : ℝ) : LocalActions :=
  ![-(normal d L EA p₀ p₁).eval 0, (shear d L EI q₀ q₁).eval 0,
    -(moment d L EI q₀ q₁).eval 0, (normal d L EA p₀ p₁).eval L,
    -(shear d L EI q₀ q₁).eval L, (moment d L EI q₀ q₁).eval L]

/-- The imposed axial coordinates are recovered at both member ends. -/
theorem axial_end_kinematics (d : LocalDofs) (L EA p₀ p₁ : ℝ)
    (hL : L ≠ 0) (_hEA : EA ≠ 0) :
    (axialDisplacement d L EA p₀ p₁).eval 0 = d 0 ∧
    (axialDisplacement d L EA p₀ p₁).eval L = d 3 := by
  constructor <;> simp [axialDisplacement, coordinate]
  all_goals field_simp
  all_goals ring

/-- The imposed transverse translations are recovered at both member ends. -/
theorem transverse_end_kinematics (d : LocalDofs) (L EI q₀ q₁ : ℝ)
    (hL : L ≠ 0) (_hEI : EI ≠ 0) :
    (transverseDisplacement d L EI q₀ q₁).eval 0 = d 1 ∧
    (transverseDisplacement d L EI q₀ q₁).eval L = d 4 := by
  constructor <;> simp [transverseDisplacement, coordinate]
  all_goals field_simp
  all_goals ring

/-- The imposed physical end rotations are recovered from v′. -/
theorem rotation_end_kinematics (d : LocalDofs) (L EI q₀ q₁ : ℝ)
    (hL : L ≠ 0) (_hEI : EI ≠ 0) :
    (rotation d L EI q₀ q₁).eval 0 = d 2 ∧
    (rotation d L EI q₀ q₁).eval L = d 5 := by
  constructor <;>
    simp [rotation, transverseDisplacement, coordinate, Polynomial.derivative_mul,
      Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  all_goals field_simp
  all_goals ring

/-- The field derivatives are derivatives of real functions. -/
theorem real_rotation (d : LocalDofs) (L EI q₀ q₁ x : ℝ) :
    HasDerivAt (fun t : ℝ => (transverseDisplacement d L EI q₀ q₁).eval t)
      ((rotation d L EI q₀ q₁).eval x) x := by
  exact real_derivative _ _

/-- The real axial derivative and the constitutive force agree. -/
theorem real_axial_constitutive (d : LocalDofs) (L EA p₀ p₁ x : ℝ) :
    EA * deriv (fun t : ℝ => (axialDisplacement d L EA p₀ p₁).eval t) x =
      (normal d L EA p₀ p₁).eval x := by
  simp [normal]

/-- The real rotation derivative and elastic bending moment agree. -/
theorem real_bending_constitutive (d : LocalDofs) (L EI q₀ q₁ x : ℝ) :
    EI * deriv (fun t : ℝ => (rotation d L EI q₀ q₁).eval t) x =
      (moment d L EI q₀ q₁).eval x := by
  simp [moment]

/-- The real bending-moment derivative is the selected shear field. -/
theorem real_moment_balance (d : LocalDofs) (L EI q₀ q₁ x : ℝ) :
    HasDerivAt (fun t : ℝ => (moment d L EI q₀ q₁).eval t)
      ((shear d L EI q₀ q₁).eval x) x := by
  exact real_derivative _ _

/-- On the retained member, distributed axial load gives N′ = −qx. -/
theorem axial_balance (d : LocalDofs) (L EA p₀ p₁ x : ℝ)
    (hL : L ≠ 0) (hEA : EA ≠ 0) :
    (normal d L EA p₀ p₁).derivative.eval x = -(p₀ + (p₁-p₀)*x/L) := by
  simp [normal, axialDisplacement, coordinate, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  field_simp
  ring

/-- On the retained member, transverse load gives V′ = qy. -/
theorem transverse_balance (d : LocalDofs) (L EI q₀ q₁ x : ℝ)
    (hL : L ≠ 0) (hEI : EI ≠ 0) :
    (shear d L EI q₀ q₁).derivative.eval x = q₀ + (q₁-q₀)*x/L := by
  simp [shear, moment, rotation, transverseDisplacement, coordinate,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  field_simp
  ring

/-- Both endpoint action triples follow the stated cut-face sign convention. -/
theorem left_end_action_signs (d : LocalDofs) (L EA EI p₀ p₁ q₀ q₁ : ℝ) :
    (normal d L EA p₀ p₁).eval 0 = -(endActions d L EA EI p₀ p₁ q₀ q₁) 0 ∧
    (shear d L EI q₀ q₁).eval 0 = (endActions d L EA EI p₀ p₁ q₀ q₁) 1 ∧
    (moment d L EI q₀ q₁).eval 0 = -(endActions d L EA EI p₀ p₁ q₀ q₁) 2 := by
  simp [endActions]

theorem right_end_action_signs (d : LocalDofs) (L EA EI p₀ p₁ q₀ q₁ : ℝ) :
    (normal d L EA p₀ p₁).eval L = (endActions d L EA EI p₀ p₁ q₀ q₁) 3 ∧
    (shear d L EI q₀ q₁).eval L = -(endActions d L EA EI p₀ p₁ q₀ q₁) 4 ∧
    (moment d L EI q₀ q₁).eval L = (endActions d L EA EI p₀ p₁ q₀ q₁) 5 := by
  simp [endActions]


/-- Standard local six-degree stiffness in the documented end-action order. -/
def stiffness (L EA EI : ℝ) : Fin 6 → Fin 6 → ℝ :=
  ![![EA/L, 0, 0, -EA/L, 0, 0],
    ![0, 12*EI/L^3, 6*EI/L^2, 0, -12*EI/L^3, 6*EI/L^2],
    ![0, 6*EI/L^2, 4*EI/L, 0, -6*EI/L^2, 2*EI/L],
    ![-EA/L, 0, 0, EA/L, 0, 0],
    ![0, -12*EI/L^3, -6*EI/L^2, 0, 12*EI/L^3, -6*EI/L^2],
    ![0, 6*EI/L^2, 2*EI/L, 0, -6*EI/L^2, 4*EI/L]]

/-- Consistent nodal actions for affine local distributed intensities. -/
def consistentLoad (L p₀ p₁ q₀ q₁ : ℝ) : LocalActions :=
  ![L*(2*p₀+p₁)/6, L*(7*q₀+3*q₁)/20, L^2*(3*q₀+2*q₁)/60,
    L*(p₀+2*p₁)/6, L*(3*q₀+7*q₁)/20, -L^2*(2*q₀+3*q₁)/60]

/-- Stiffness symmetry is independent of the applied loading. -/
theorem stiffness_symmetric (L EA EI : ℝ) (i j : Fin 6) :
    stiffness L EA EI i j = stiffness L EA EI j i := by
  fin_cases i <;> fin_cases j <;> simp [stiffness]

set_option maxHeartbeats 4000000 in
/-- Recover the endpoint actions from the exact fields and compare them with
K d − f. This algebraic identity alone is not a virtual-work derivation. -/
theorem end_actions_from_fields (d : LocalDofs) (L EA EI p₀ p₁ q₀ q₁ : ℝ)
    (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0) (i : Fin 6) :
    endActions d L EA EI p₀ p₁ q₀ q₁ i =
      (∑ j : Fin 6, stiffness L EA EI i j * d j) - consistentLoad L p₀ p₁ q₀ q₁ i := by
  fin_cases i <;>
    simp [endActions, normal, shear, moment, rotation, axialDisplacement,
      transverseDisplacement, coordinate, stiffness, consistentLoad,
      Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast,
      Fin.sum_univ_succ] <;> field_simp <;> ring



/-- Two axial polynomial fields with the same axial load and both prescribed
end displacements agree, once their second derivatives agree. -/
theorem axial_prescribed_end_unique (u₁ u₂ : Field) (L : ℝ) (hL : L ≠ 0)
    (hcurvature : u₁.derivative.derivative = u₂.derivative.derivative)
    (hleft : u₁.eval 0 = u₂.eval 0) (hright : u₁.eval L = u₂.eval L) : u₁ = u₂ := by
  exact (piecewise_curvature_uniqueness u₁ u₁ u₂ u₂ 0 L hL hcurvature hcurvature
    hleft hright rfl rfl).1

/-- A polynomial whose fourth derivative vanishes is at most cubic. -/
theorem cubic_of_fourth_derivative_zero (p : Field)
    (h : p.derivative.derivative.derivative.derivative = 0) :
    ∃ c₀ c₁ c₂ c₃ : ℝ, p = C c₀ + C c₁*X + C c₂*X^2 + C c₃*X^3 := by
  obtain ⟨a, b, hab⟩ := affine_of_second_derivative_zero p.derivative.derivative h
  let residual : Field := p - C (a/2)*X^2 - C (b/6)*X^3
  have hresidual : residual.derivative.derivative = 0 := by
    simp [residual, Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_pow, Polynomial.C_eq_natCast, hab, map_mul]
    ring
  obtain ⟨c₀, c₁, hc⟩ := affine_of_second_derivative_zero residual hresidual
  refine ⟨c₀, c₁, a/2, b/6, ?_⟩
  dsimp [residual] at hc
  linear_combination hc

/-- Clamped polynomial end data and the same fourth derivative determine the
transverse field. This uses both endpoint translations and rotations. -/
theorem transverse_prescribed_end_unique (v₁ v₂ : Field) (L : ℝ) (hL : 0 < L)
    (hload : v₁.derivative.derivative.derivative.derivative =
             v₂.derivative.derivative.derivative.derivative)
    (hleft : v₁.eval 0 = v₂.eval 0) (hright : v₁.eval L = v₂.eval L)
    (hleftSlope : v₁.derivative.eval 0 = v₂.derivative.eval 0)
    (hrightSlope : v₁.derivative.eval L = v₂.derivative.eval L) : v₁ = v₂ := by
  have hzero : (v₁-v₂).derivative.derivative.derivative.derivative = 0 := by
    simp [Polynomial.derivative_sub, hload]
  obtain ⟨c₀, c₁, c₂, c₃, hc⟩ := cubic_of_fourth_derivative_zero (v₁-v₂) hzero
  have hc₀ : c₀ = 0 := by
    have h := congrArg (Polynomial.eval (0 : ℝ)) hc
    simpa [hleft] using h.symm
  have hc₁ : c₁ = 0 := by
    have h := congrArg (fun p : Field => p.derivative.eval 0) hc
    simp [Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_pow, Polynomial.C_eq_natCast, hleftSlope] at h
    exact h.symm
  have hvalue : c₂*L^2 + c₃*L^3 = 0 := by
    have h := congrArg (Polynomial.eval L) hc
    simp [hright, hc₀, hc₁] at h
    linarith
  have hslope : 2*c₂*L + 3*c₃*L^2 = 0 := by
    have h := congrArg (fun p : Field => p.derivative.eval L) hc
    simp [Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_pow, Polynomial.C_eq_natCast, hrightSlope, hc₁] at h
    linarith
  have hcube : c₃*L^3 = 0 := by nlinarith [mul_eq_mul_left L hslope]
  have hc₃ : c₃ = 0 := (mul_eq_zero.mp hcube).resolve_right (pow_ne_zero 3 (ne_of_gt hL))
  have hsquare : c₂*L^2 = 0 := by simpa [hc₃] using hvalue
  have hc₂ : c₂ = 0 := (mul_eq_zero.mp hsquare).resolve_right (pow_ne_zero 2 (ne_of_gt hL))
  have hdiff : v₁-v₂ = 0 := by simpa [hc₀, hc₁, hc₂, hc₃] using hc
  exact sub_eq_zero.mp hdiff



/-- With the same affine distributed loads and positive rigidities, prescribed
end translations and rotations determine the local polynomial fields. -/
theorem prescribed_fields_unique (u₁ u₂ v₁ v₂ : Field) (L EA EI p₀ p₁ q₀ q₁ : ℝ)
    (hL : 0 < L) (hEA : 0 < EA) (hEI : 0 < EI)
    (hu₁ : ∀ x, EA*u₁.derivative.derivative.eval x = -(p₀+(p₁-p₀)*x/L))
    (hu₂ : ∀ x, EA*u₂.derivative.derivative.eval x = -(p₀+(p₁-p₀)*x/L))
    (hv₁ : ∀ x, EI*v₁.derivative.derivative.derivative.derivative.eval x = q₀+(q₁-q₀)*x/L)
    (hv₂ : ∀ x, EI*v₂.derivative.derivative.derivative.derivative.eval x = q₀+(q₁-q₀)*x/L)
    (huLeft : u₁.eval 0 = u₂.eval 0) (huRight : u₁.eval L = u₂.eval L)
    (hvLeft : v₁.eval 0 = v₂.eval 0) (hvRight : v₁.eval L = v₂.eval L)
    (htLeft : v₁.derivative.eval 0 = v₂.derivative.eval 0)
    (htRight : v₁.derivative.eval L = v₂.derivative.eval L) : u₁ = u₂ ∧ v₁ = v₂ := by
  have hu : u₁.derivative.derivative = u₂.derivative.derivative := by
    apply Polynomial.funext
    intro x
    apply mul_left_cancel₀ (ne_of_gt hEA)
    rw [hu₁ x, hu₂ x]
  have hv : v₁.derivative.derivative.derivative.derivative =
      v₂.derivative.derivative.derivative.derivative := by
    apply Polynomial.funext
    intro x
    apply mul_left_cancel₀ (ne_of_gt hEI)
    rw [hv₁ x, hv₂ x]
  exact ⟨axial_prescribed_end_unique u₁ u₂ L (ne_of_gt hL) hu huLeft huRight,
    transverse_prescribed_end_unique v₁ v₂ L hL hv hvLeft hvRight htLeft htRight⟩


end
end LocalFrameFields
