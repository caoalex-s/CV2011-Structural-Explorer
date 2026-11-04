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

end
end FrameVirtualWork
