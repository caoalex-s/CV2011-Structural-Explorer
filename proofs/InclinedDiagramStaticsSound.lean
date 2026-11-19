import RationalFrameFields
import InclinedDiagramStatics

namespace InclinedDiagram.Statics.Sound
noncomputable section

/-- Rotate both element end forces into the global drawing axes. -/
def forceX (c s axial transverse : ℝ) := c*axial - s*transverse
def forceY (c s axial transverse : ℝ) := s*axial + c*transverse

/-- Global balance of an arbitrary Euler-Bernoulli element carrying a
vertical affine load. This holds for every physical element motion. -/
theorem element_balance (motion : FrameInterfaces.LocalDofs) (ell EA EI c s f₀ f₁ : ℝ)
    (length : ell ≠ 0) (axial : EA ≠ 0) (bending : EI ≠ 0) (unit : c^2+s^2=1) :
    let actions := LocalFrameFields.endActions motion ell EA EI (s*f₀) (s*f₁) (c*f₀) (c*f₁)
    let xa := forceX c s (actions 0) (actions 1)
    let ya := forceY c s (actions 0) (actions 1)
    let xb := forceX c s (actions 3) (actions 4)
    let yb := forceY c s (actions 3) (actions 4)
    xa+xb = 0 ∧ ya+yb+ell*(f₀+f₁)/2 = 0 ∧
      actions 2+actions 5+(ell*c)*yb-(ell*s)*xb+ell*(ell*c)*(f₀+2*f₁)/6 = 0 := by
  let a := LocalFrameFields.endActions motion ell EA EI (s*f₀) (s*f₁) (c*f₀) (c*f₁)
  have recover := RationalFrame.Fields.affine_recovery motion ell EA EI
    (s*f₀) (s*f₁) (c*f₀) (c*f₁) ell length axial bending
  have n : a 3 = -a 0 - s*f₀*ell - (s*f₁-s*f₀)/ell*ell^2/2 := recover.1
  have v : a 4 = -(a 1 + c*f₀*ell + (c*f₁-c*f₀)/ell*ell^2/2) :=
    congrArg Neg.neg recover.2.1
  have m : a 5 = -a 2 + a 1*ell + c*f₀*ell^2/2 + (c*f₁-c*f₀)/ell*ell^3/6 :=
    recover.2.2.1
  have axialEnd : a 3 = -a 0-ell*s*(f₀+f₁)/2 := by rw [n]; field_simp [length]; ring
  have shearEnd : a 4 = -a 1-ell*c*(f₀+f₁)/2 := by rw [v]; field_simp [length]; ring
  have momentEnd : a 5 = -a 2+ell*a 1+ell^2*c*(2*f₀+f₁)/6 := by rw [m]; field_simp [length]; ring
  change forceX c s (a 0) (a 1) + forceX c s (a 3) (a 4) = 0 ∧
    forceY c s (a 0) (a 1) + forceY c s (a 3) (a 4) + ell*(f₀+f₁)/2=0 ∧
    a 2+a 5+ell*c*forceY c s (a 3) (a 4)-ell*s*forceX c s (a 3) (a 4)+
      ell*(ell*c)*(f₀+2*f₁)/6=0
  rw [axialEnd,shearEnd,momentEnd]
  unfold forceX forceY
  constructor
  · ring
  constructor
  · linear_combination -ell*(f₀+f₁)/2 * unit
  · linear_combination ell*(-a 1-ell*c*(f₀+f₁)/2) * unit

#print axioms element_balance
end
end InclinedDiagram.Statics.Sound
