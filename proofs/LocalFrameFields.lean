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
    (hL : L ≠ 0) (hEA : EA ≠ 0) :
    (axialDisplacement d L EA p₀ p₁).eval 0 = d 0 ∧
    (axialDisplacement d L EA p₀ p₁).eval L = d 3 := by
  constructor <;> simp [axialDisplacement, coordinate] <;> field_simp <;> ring

/-- The imposed transverse translations are recovered at both member ends. -/
theorem transverse_end_kinematics (d : LocalDofs) (L EI q₀ q₁ : ℝ)
    (hL : L ≠ 0) (hEI : EI ≠ 0) :
    (transverseDisplacement d L EI q₀ q₁).eval 0 = d 1 ∧
    (transverseDisplacement d L EI q₀ q₁).eval L = d 4 := by
  constructor <;> simp [transverseDisplacement, coordinate] <;> field_simp <;> ring

/-- The imposed physical end rotations are recovered from v′. -/
theorem rotation_end_kinematics (d : LocalDofs) (L EI q₀ q₁ : ℝ)
    (hL : L ≠ 0) (hEI : EI ≠ 0) :
    (rotation d L EI q₀ q₁).eval 0 = d 2 ∧
    (rotation d L EI q₀ q₁).eval L = d 5 := by
  constructor <;>
    simp [rotation, transverseDisplacement, coordinate, Polynomial.derivative_mul,
      Polynomial.derivative_pow, Polynomial.C_eq_natCast] <;> field_simp <;> ring

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

end
end LocalFrameFields
