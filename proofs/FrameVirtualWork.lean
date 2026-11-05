import FrameEnergy

/-!
Virtual work in the dimensionless coordinate z = x/L. Multiplying the unit-span
integral by L accounts for dx = L dz. The shape functions here are the linear
axial and cubic Hermite transverse parts of the exact local field. Point actions
remain member-side nodal actions and do not enter the distributed-load vector.
-/
open Polynomial MeasureTheory intervalIntegral
open FrameInterfaces RealBeamFields LocalFrameFields

namespace FrameVirtualWork

noncomputable section

def axialShape (d : LocalDofs) : Field := C (d 0)*(1-X) + C (d 3)*X

def transverseShape (d : LocalDofs) (L : ℝ) : Field :=
  C (d 1)*(1-3*X^2+2*X^3) + C (L*d 2)*(X-2*X^2+X^3) +
  C (d 4)*(3*X^2-2*X^3) + C (L*d 5)*(X^3-X^2)

def loadDensity (d : LocalDofs) (L p₀ p₁ q₀ q₁ : ℝ) : Field :=
  (C p₀*(1-X)+C p₁*X)*axialShape d +
  (C q₀*(1-X)+C q₁*X)*transverseShape d L

/-- Sixty times a polynomial primitive avoids coefficient truncation. -/
def loadPrimitive60 (d : LocalDofs) (L p₀ p₁ q₀ q₁ : ℝ) : Field :=
  C (p₀*d 0)*(20*X^3-60*X^2+60*X) +
  C (p₀*d 3+p₁*d 0)*(30*X^2-20*X^3) + C (p₁*d 3)*(20*X^3) +
  C (q₀*d 1)*(-24*X^5+75*X^4-60*X^3-30*X^2+60*X) +
  C (q₁*d 1)*(24*X^5-45*X^4+30*X^2) +
  C (L*q₀*d 2)*(-12*X^5+45*X^4-60*X^3+30*X^2) +
  C (L*q₁*d 2)*(12*X^5-30*X^4+20*X^3) +
  C (q₀*d 4)*(24*X^5-75*X^4+60*X^3) +
  C (q₁*d 4)*(-24*X^5+45*X^4) +
  C (L*q₀*d 5)*(-12*X^5+30*X^4-20*X^3) +
  C (L*q₁*d 5)*(12*X^5-15*X^4)

/-- The primitive is derived from the full affine-load virtual-work density. -/
theorem load_primitive_derivative (d : LocalDofs) (L p₀ p₁ q₀ q₁ : ℝ) :
    (loadPrimitive60 d L p₀ p₁ q₀ q₁).derivative = 60 * loadDensity d L p₀ p₁ q₀ q₁ := by
  simp [loadPrimitive60, loadDensity, axialShape, transverseShape,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast, map_mul, map_add]
  ring

/-- Integrating the load density gives the actual consistent nodal vector. -/
theorem consistent_load_virtual_work (d : LocalDofs) (L p₀ p₁ q₀ q₁ : ℝ) :
    L * (∫ x in (0 : ℝ)..1, (loadDensity d L p₀ p₁ q₀ q₁).eval x) =
      ∑ i : Fin 6, consistentLoad L p₀ p₁ q₀ q₁ i * d i := by
  have h := real_integral (loadPrimitive60 d L p₀ p₁ q₀ q₁) 0 1
  rw [load_primitive_derivative] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, intervalIntegral.integral_const_mul] at h
  calc
    L * (∫ x in (0 : ℝ)..1, (loadDensity d L p₀ p₁ q₀ q₁).eval x) =
        L/60 * (60 * (∫ x in (0 : ℝ)..1, (loadDensity d L p₀ p₁ q₀ q₁).eval x)) := by ring
    _ = L/60 * ((loadPrimitive60 d L p₀ p₁ q₀ q₁).eval 1 -
          (loadPrimitive60 d L p₀ p₁ q₀ q₁).eval 0) := by rw [h]
    _ = ∑ i : Fin 6, consistentLoad L p₀ p₁ q₀ q₁ i * d i := by
      simp [loadPrimitive60, consistentLoad, Fin.sum_univ_succ]
      ring


/-- Physical distributed-load work density on the exact virtual field with
zero virtual loading. End rotations are physical counterclockwise rotations. -/
def physicalLoadDensity (d : LocalDofs) (L EA EI p₀ p₁ q₀ q₁ x : ℝ) : ℝ :=
  (p₀+(p₁-p₀)*x/L) * (axialDisplacement d L EA 0 0).eval x +
  (q₀+(q₁-q₀)*x/L) * (transverseDisplacement d L EI 0 0).eval x

/-- The dimensionless density is the same physical load work at x=Lz. -/
theorem normalized_load_density (d : LocalDofs) (L EA EI p₀ p₁ q₀ q₁ z : ℝ)
    (hL : L ≠ 0) :
    physicalLoadDensity d L EA EI p₀ p₁ q₀ q₁ (L*z) = (loadDensity d L p₀ p₁ q₀ q₁).eval z := by
  simp [physicalLoadDensity, loadDensity, axialShape, transverseShape,
    axialDisplacement, transverseDisplacement, coordinate]
  field_simp
  ring

/-- The physical x-integral of distributed virtual work is f·d. -/
theorem physical_consistent_load_work (d : LocalDofs) (L EA EI p₀ p₁ q₀ q₁ : ℝ)
    (hL : L ≠ 0) :
    (∫ x in (0 : ℝ)..L, physicalLoadDensity d L EA EI p₀ p₁ q₀ q₁ x) =
      ∑ i : Fin 6, consistentLoad L p₀ p₁ q₀ q₁ i * d i := by
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (physicalLoadDensity d L EA EI p₀ p₁ q₀ q₁) (a := (0 : ℝ)) (b := 1) L
  simp only [mul_zero, mul_one, smul_eq_mul] at hchange
  rw [← hchange]
  have hfun : (fun z => physicalLoadDensity d L EA EI p₀ p₁ q₀ q₁ (L*z)) =
      (fun z => (loadDensity d L p₀ p₁ q₀ q₁).eval z) := by
    funext z
    exact normalized_load_density d L EA EI p₀ p₁ q₀ q₁ z hL
  rw [hfun]
  exact consistent_load_virtual_work d L p₀ p₁ q₀ q₁

/-- Coefficients of the second derivative of the Hermite field in z. -/
def curvatureConstant (d : LocalDofs) (L : ℝ) : ℝ :=
  -6*d 1 - 4*L*d 2 + 6*d 4 - 2*L*d 5

def curvatureLinear (d : LocalDofs) (L : ℝ) : ℝ :=
  12*d 1 + 6*L*d 2 - 12*d 4 + 6*L*d 5

/-- Internal virtual-work density after x=Lz. Axial and flexural rigidities
are constant on the member. -/
def strainDensity (d e : LocalDofs) (L EA EI : ℝ) : Field :=
  C (EA/L) * (axialShape d).derivative * (axialShape e).derivative +
  C (EI/L^3) * (transverseShape d L).derivative.derivative *
    (transverseShape e L).derivative.derivative

/-- Six times a primitive for the axial and bending virtual-work density. -/
def strainPrimitive6 (d e : LocalDofs) (L EA EI : ℝ) : Field :=
  let a₀ := curvatureConstant d L
  let a₁ := curvatureLinear d L
  let b₀ := curvatureConstant e L
  let b₁ := curvatureLinear e L
  C (EA/L) * C (d 3-d 0) * C (e 3-e 0) * (6*X) +
  C (EI/L^3) * (C (a₀*b₀)*(6*X) + C (a₀*b₁+a₁*b₀)*(3*X^2) + C (a₁*b₁)*(2*X^3))

set_option maxHeartbeats 4000000 in
/-- The primitive differentiates to the actual linear/Hermite strain density. -/
theorem strain_primitive_derivative (d e : LocalDofs) (L EA EI : ℝ) :
    (strainPrimitive6 d e L EA EI).derivative = 6 * strainDensity d e L EA EI := by
  simp [strainPrimitive6, strainDensity, curvatureConstant, curvatureLinear,
    axialShape, transverseShape, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.C_eq_natCast, map_mul, map_add, map_sub]
  ring

set_option maxHeartbeats 4000000 in
/-- Integrating the real strain fields yields the standard stiffness action. -/
theorem stiffness_virtual_work (d e : LocalDofs) (L EA EI : ℝ) (hL : L ≠ 0) :
    (∫ x in (0 : ℝ)..1, (strainDensity d e L EA EI).eval x) =
      ∑ i : Fin 6, e i * (∑ j : Fin 6, stiffness L EA EI i j * d j) := by
  have h := real_integral (strainPrimitive6 d e L EA EI) 0 1
  rw [strain_primitive_derivative] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, intervalIntegral.integral_const_mul] at h
  calc
    (∫ x in (0 : ℝ)..1, (strainDensity d e L EA EI).eval x) =
        1/6 * (6 * (∫ x in (0 : ℝ)..1, (strainDensity d e L EA EI).eval x)) := by ring
    _ = 1/6 * ((strainPrimitive6 d e L EA EI).eval 1 -
          (strainPrimitive6 d e L EA EI).eval 0) := by rw [h]
    _ = ∑ i : Fin 6, e i * (∑ j : Fin 6, stiffness L EA EI i j * d j) := by
      simp [strainPrimitive6, curvatureConstant, curvatureLinear, stiffness, Fin.sum_univ_succ]
      field_simp
      ring



/-- Internal virtual-work density in physical coordinates, using the exact
zero-virtual-load member fields rather than an assumed matrix equation. -/
def physicalStrainDensity (d e : LocalDofs) (L EA EI x : ℝ) : ℝ :=
  EA * (axialDisplacement d L EA 0 0).derivative.eval x *
       (axialDisplacement e L EA 0 0).derivative.eval x +
  EI * (transverseDisplacement d L EI 0 0).derivative.derivative.eval x *
       (transverseDisplacement e L EI 0 0).derivative.derivative.eval x

set_option maxHeartbeats 4000000 in
/-- A physical strain density transforms into the normalised density with dx=L dz. -/
theorem normalized_strain_density (d e : LocalDofs) (L EA EI z : ℝ) (hL : L ≠ 0) :
    L * physicalStrainDensity d e L EA EI (L*z) = (strainDensity d e L EA EI).eval z := by
  simp [physicalStrainDensity, strainDensity, axialShape, transverseShape,
    axialDisplacement, transverseDisplacement, coordinate, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.C_eq_natCast, map_mul, map_add, map_sub]
  field_simp
  ring

/-- The physical strain-field virtual work equals the standard stiffness action. -/
theorem physical_stiffness_work (d e : LocalDofs) (L EA EI : ℝ) (hL : L ≠ 0) :
    (∫ x in (0 : ℝ)..L, physicalStrainDensity d e L EA EI x) =
      ∑ i : Fin 6, e i * (∑ j : Fin 6, stiffness L EA EI i j * d j) := by
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (physicalStrainDensity d e L EA EI) (a := (0 : ℝ)) (b := 1) L
  simp only [mul_zero, mul_one, smul_eq_mul] at hchange
  calc
    (∫ x in (0 : ℝ)..L, physicalStrainDensity d e L EA EI x) =
        L * (∫ z in (0 : ℝ)..1, physicalStrainDensity d e L EA EI (L*z)) := hchange.symm
    _ = ∫ z in (0 : ℝ)..1, L * physicalStrainDensity d e L EA EI (L*z) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ z in (0 : ℝ)..1, (strainDensity d e L EA EI).eval z := by
      congr 1
      funext z
      exact normalized_strain_density d e L EA EI z hL
    _ = ∑ i : Fin 6, e i * (∑ j : Fin 6, stiffness L EA EI i j * d j) :=
      stiffness_virtual_work d e L EA EI hL


end
end FrameVirtualWork
