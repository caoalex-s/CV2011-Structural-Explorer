import Mathlib

/-!
Real polynomial fields for the linear Euler–Bernoulli beam idealisation.
Polynomials have arbitrary finite degree; no coefficient is truncated. These
lemmas establish calculus and algebraic consequences of stated field equations.
They do not prove the physical idealisation, frame assembly, or a numerical
solution. A cut at a point action has distinct left and right polynomials.
-/

open Polynomial MeasureTheory intervalIntegral

namespace RealBeamFields

noncomputable section

abbrev Field := Polynomial ℝ

/-- Formal polynomial differentiation agrees with the real derivative. -/
theorem real_derivative (p : Field) (x : ℝ) :
    HasDerivAt (fun t : ℝ => p.eval t) (p.derivative.eval x) x :=
  p.hasDerivAt x

/-- Integrating a polynomial derivative recovers the change in its real field. -/
theorem real_integral (p : Field) (a b : ℝ) :
    (∫ x in a..b, p.derivative.eval x) = p.eval b - p.eval a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact p.hasDerivAt x
  · exact p.derivative.continuous.intervalIntegrable a b

/-- On a smooth interval, polynomial balance gives the real shear derivative. -/
theorem shear_balance (V w : Field) (h : V.derivative = -w) (x : ℝ) :
    HasDerivAt (fun t : ℝ => V.eval t) (-w.eval x) x := by
  simpa [h] using V.hasDerivAt x

/-- On a smooth interval, the real moment derivative equals shear. -/
theorem moment_balance (M V : Field) (h : M.derivative = V) (x : ℝ) :
    HasDerivAt (fun t : ℝ => M.eval t) (V.eval x) x := by
  simpa [h] using M.hasDerivAt x

/-- Distributed axial force is positive in the local positive-x direction. -/
theorem axial_balance (N p : Field) (h : N.derivative = -p) (x : ℝ) :
    HasDerivAt (fun t : ℝ => N.eval t) (-p.eval x) x := by
  simpa [h] using N.hasDerivAt x

/-- An axial field satisfying EA u′ = N has the corresponding real derivative. -/
theorem axial_constitutive (u N : Field) (EA x : ℝ)
    (h : C EA * u.derivative = N) :
    EA * deriv (fun t : ℝ => u.eval t) x = N.eval x := by
  have evaluated := congrArg (Polynomial.eval x) h
  simpa using evaluated

/-- Equilibrium equations are linear in the fields and downward intensity. -/
theorem shear_balance_superposition (V₁ V₂ w₁ w₂ : Field)
    (h₁ : V₁.derivative = -w₁) (h₂ : V₂.derivative = -w₂) :
    (V₁ + V₂).derivative = -(w₁ + w₂) := by
  simp [h₁, h₂, add_comm]

/-- Polynomial slope and displacement fields represent real derivatives. -/
theorem displacement_slope (v theta : Field) (h : v.derivative = theta) (x : ℝ) :
    HasDerivAt (fun t : ℝ => v.eval t) (theta.eval x) x := by
  simpa [h] using v.hasDerivAt x

/-- Point actions add a constant shear and a linear moment correction. -/
def shearAfterForce (left : Field) (force : ℝ) : Field := left + C force

def momentAfterActions (left : Field) (force couple coordinate : ℝ) : Field :=
  left + C force * (X - C coordinate) - C couple

theorem force_jump (left : Field) (force coordinate : ℝ) :
    (shearAfterForce left force).eval coordinate - left.eval coordinate = force := by
  simp [shearAfterForce]

theorem couple_jump (left : Field) (force couple coordinate : ℝ) :
    (momentAfterActions left force couple coordinate).eval coordinate - left.eval coordinate = -couple := by
  simp [momentAfterActions]

/-- Superposition preserves both polynomial field equations and the real derivative. -/
theorem slope_superposition (v₁ v₂ theta₁ theta₂ : Field)
    (h₁ : v₁.derivative = theta₁) (h₂ : v₂.derivative = theta₂) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (v₁ + v₂).eval t) ((theta₁ + theta₂).eval x) x := by
  apply displacement_slope
  simp [h₁, h₂]

/-- Elastic fields for a downward point force between endpoint supports.
The signs follow upward-positive displacement and counterclockwise slope. -/
def leftReaction (P a L : ℝ) : ℝ := P * (L - a) / L

def leftSlope (P a L EI : ℝ) : ℝ :=
  -P * (L-a) * (L^2-(L-a)^2) / (6*L*EI)

def slopeBefore (P a L EI : ℝ) : Field :=
  C (leftSlope P a L EI) + C (leftReaction P a L / (6*EI)) * (3 * X^2)

def slopeAfter (P a L EI : ℝ) : Field :=
  slopeBefore P a L EI - C (P / (6*EI)) * (3 * (X-C a)^2)

def deflectionBefore (P a L EI : ℝ) : Field :=
  C (leftSlope P a L EI) * X + C (leftReaction P a L / (6*EI)) * X^3

def deflectionAfter (P a L EI : ℝ) : Field :=
  deflectionBefore P a L EI - C (P / (6*EI)) * (X-C a)^3

/-- Before the point force, the elastic-curve derivative is physical slope. -/
theorem point_before_derivative (P a L EI : ℝ) :
    (deflectionBefore P a L EI).derivative = slopeBefore P a L EI := by
  simp [deflectionBefore, slopeBefore, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  simp only [show C (3 : ℝ) = (3 : Field) from map_natCast (Polynomial.C : ℝ →+* Field) 3]
  ring

/-- After the point force, the elastic-curve derivative is physical slope. -/
theorem point_after_derivative (P a L EI : ℝ) :
    (deflectionAfter P a L EI).derivative = slopeAfter P a L EI := by
  simp [deflectionAfter, slopeAfter, point_before_derivative, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  simp only [show C (3 : ℝ) = (3 : Field) from map_natCast (Polynomial.C : ℝ →+* Field) 3]
  ring

/-- These are derivatives of actual real functions, not formal symbols alone. -/
theorem point_real_slope_before (P a L EI x : ℝ) :
    HasDerivAt (fun t : ℝ => (deflectionBefore P a L EI).eval t)
      ((slopeBefore P a L EI).eval x) x :=
  displacement_slope _ _ (point_before_derivative P a L EI) x

theorem point_real_slope_after (P a L EI x : ℝ) :
    HasDerivAt (fun t : ℝ => (deflectionAfter P a L EI).eval t)
      ((slopeAfter P a L EI).eval x) x :=
  displacement_slope _ _ (point_after_derivative P a L EI) x

/-- The right reaction for the same endpoint-supported point-force system. -/
def rightReaction (P a L : ℝ) : ℝ := P * a / L

def pointShearBefore (P a L : ℝ) : Field := C (leftReaction P a L)
def pointShearAfter (P a L : ℝ) : Field := shearAfterForce (pointShearBefore P a L) (-P)
def pointMomentBefore (P a L : ℝ) : Field := C (leftReaction P a L) * X
def pointMomentAfter (P a L : ℝ) : Field := momentAfterActions (pointMomentBefore P a L) (-P) 0 a

/-- The named reactions balance a downward load of signed magnitude P. -/
theorem point_reaction_force (P a L : ℝ) (hL : L ≠ 0) :
    leftReaction P a L + rightReaction P a L - P = 0 := by
  simp [leftReaction, rightReaction]
  field_simp
  ring

theorem point_reaction_moment (P a L : ℝ) (hL : L ≠ 0) :
    rightReaction P a L * L - P * a = 0 := by
  simp [rightReaction]
  field_simp

/-- The named shear fields jump by the upward-positive applied force -P. -/
theorem point_shear_jump (P a L : ℝ) :
    (pointShearAfter P a L).eval a - (pointShearBefore P a L).eval a = -P := by
  exact force_jump _ _ _

theorem point_moment_continuity (P a L : ℝ) :
    (pointMomentAfter P a L).eval a = (pointMomentBefore P a L).eval a := by
  simp [pointMomentAfter, momentAfterActions]

/-- The moment and shear branches satisfy the same equilibrium equations. -/
theorem point_moment_derivative_before (P a L : ℝ) :
    (pointMomentBefore P a L).derivative = pointShearBefore P a L := by
  simp [pointMomentBefore, pointShearBefore, Polynomial.derivative_mul]

theorem point_moment_derivative_after (P a L : ℝ) :
    (pointMomentAfter P a L).derivative = pointShearAfter P a L := by
  simp [pointMomentAfter, pointMomentBefore, pointShearAfter, pointShearBefore,
    shearAfterForce, momentAfterActions, Polynomial.derivative_mul]

/-- The named elastic and equilibrium fields obey the same constitutive law. -/
theorem point_curvature_before (P a L EI x : ℝ) (hEI : EI ≠ 0) :
    EI * (slopeBefore P a L EI).derivative.eval x = (pointMomentBefore P a L).eval x := by
  simp [slopeBefore, pointMomentBefore, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  field_simp
  ring

theorem point_curvature_after (P a L EI x : ℝ) (hEI : EI ≠ 0) :
    EI * (slopeAfter P a L EI).derivative.eval x = (pointMomentAfter P a L).eval x := by
  simp [slopeAfter, slopeBefore, pointMomentAfter, pointMomentBefore, momentAfterActions,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  field_simp
  ring

/-- A physical beam chooses its polynomial on the appropriate side of the load. -/
def pointDisplacement (P a L EI x : ℝ) : ℝ :=
  if x < a then (deflectionBefore P a L EI).eval x else (deflectionAfter P a L EI).eval x

def pointSlope (P a L EI x : ℝ) : ℝ :=
  if x < a then (slopeBefore P a L EI).eval x else (slopeAfter P a L EI).eval x

theorem point_piece_slope_before (P a L EI x : ℝ) (hx : x < a) :
    HasDerivAt (pointDisplacement P a L EI) (pointSlope P a L EI x) x := by
  rw [pointSlope, if_pos hx]
  apply (point_real_slope_before P a L EI x).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hx] with t ht
  simp [pointDisplacement, ht]

theorem point_piece_slope_after (P a L EI x : ℝ) (hx : a < x) :
    HasDerivAt (pointDisplacement P a L EI) (pointSlope P a L EI x) x := by
  rw [pointSlope, if_neg (not_lt.mpr hx.le)]
  apply (point_real_slope_after P a L EI x).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with t ht
  simp [pointDisplacement, not_lt.mpr ht.le]

/-- The two displacement branches agree at the action. -/
theorem point_displacement_continuity (P a L EI : ℝ) :
    (deflectionBefore P a L EI).eval a = (deflectionAfter P a L EI).eval a := by
  simp [deflectionAfter]

/-- The two physical-slope branches agree at the action. -/
theorem point_slope_continuity (P a L EI : ℝ) :
    (slopeBefore P a L EI).eval a = (slopeAfter P a L EI).eval a := by
  simp [slopeAfter]

/-- The selected displacement is differentiable through the load: the
left and right field values and their physical slopes agree at the join. -/
theorem point_piece_slope_at_load (P a L EI : ℝ) :
    HasDerivAt (pointDisplacement P a L EI) (pointSlope P a L EI a) a := by
  rw [pointSlope, if_neg (lt_irrefl a)]
  have leftSlopeEq := point_slope_continuity P a L EI
  have hleft : HasDerivWithinAt (pointDisplacement P a L EI)
      ((slopeAfter P a L EI).eval a) (Set.Iio a) a := by
    apply ((point_real_slope_before P a L EI a).congr_deriv leftSlopeEq).hasDerivWithinAt.congr
    · intro t ht
      change t < a at ht
      simp [pointDisplacement, ht]
    · simp [pointDisplacement, ← point_displacement_continuity]
  have hright : HasDerivWithinAt (pointDisplacement P a L EI)
      ((slopeAfter P a L EI).eval a) (Set.Ici a) a := by
    apply (point_real_slope_after P a L EI a).hasDerivWithinAt.congr
    · intro t ht
      change a ≤ t at ht
      simp [pointDisplacement, not_lt.mpr ht]
    · simp [pointDisplacement]
  have h := hleft.union hright
  have hunion : Set.Iio a ∪ Set.Ici a = Set.univ := Set.Iio_union_Ici
  rw [hunion, hasDerivWithinAt_univ] at h
  exact h

/-- Left support displacement is zero. -/
theorem point_left_support (P a L EI : ℝ) :
    (deflectionBefore P a L EI).eval 0 = 0 := by
  simp [deflectionBefore]

/-- The right support displacement is zero when span and rigidity are nonzero. -/
theorem point_right_support (P a L EI : ℝ) (hL : L ≠ 0) (hEI : EI ≠ 0) :
    (deflectionAfter P a L EI).eval L = 0 := by
  simp [deflectionAfter, deflectionBefore, leftReaction, leftSlope]
  field_simp
  ring


/-- For a fixed moment field, the two integration constants in each
interval are unique if their difference is affine, displacement and slope are
continuous at the load, and both endpoint displacements are prescribed. -/
theorem affine_boundary_uniqueness (L a c₀ c₁ d₀ d₁ : ℝ) (hL : L ≠ 0)
    (hleft : c₀ = 0) (hright : d₀ + d₁*L = 0)
    (hdisplacement : c₀ + c₁*a = d₀ + d₁*a) (hslope : c₁ = d₁) :
    c₀ = 0 ∧ c₁ = 0 ∧ d₀ = 0 ∧ d₁ = 0 := by
  have hd₀ : d₀ = 0 := by nlinarith
  have hproduct : d₁*L = 0 := by nlinarith
  have hd₁ : d₁ = 0 := (mul_eq_zero.mp hproduct).resolve_right hL
  exact ⟨hleft, by linarith, hd₀, hd₁⟩

/-! A cantilever with downward end force P, counterclockwise end couple T,
and downward intensity w(x) = w₀ + w₁ x. These fields share the same
real-polynomial calculus as the point-force beam above. -/
def cantileverM0 (P T w₀ w₁ L : ℝ) : ℝ := T - P*L - w₀*L^2/2 - w₁*L^3/3
def cantileverM1 (P w₀ w₁ L : ℝ) : ℝ := P + w₀*L + w₁*L^2/2

def cubicMoment (m₀ m₁ m₂ m₃ : ℝ) : Field :=
  C m₀ + C m₁*X + C m₂*X^2 + C m₃*X^3

def cubicSlope (m₀ m₁ m₂ m₃ EI : ℝ) : Field :=
  C (1/(60*EI)) * (C m₀*(60*X) + C m₁*(30*X^2) + C m₂*(20*X^3) + C m₃*(15*X^4))

def cubicDisplacement (m₀ m₁ m₂ m₃ EI : ℝ) : Field :=
  C (1/(60*EI)) * (C m₀*(30*X^2) + C m₁*(10*X^3) + C m₂*(5*X^4) + C m₃*(3*X^5))

def cantileverMoment (P T w₀ w₁ L : ℝ) : Field :=
  cubicMoment (cantileverM0 P T w₀ w₁ L) (cantileverM1 P w₀ w₁ L) (-w₀/2) (-w₁/6)

def cantileverSlope (P T w₀ w₁ L EI : ℝ) : Field :=
  cubicSlope (cantileverM0 P T w₀ w₁ L) (cantileverM1 P w₀ w₁ L) (-w₀/2) (-w₁/6) EI

def cantileverDisplacement (P T w₀ w₁ L EI : ℝ) : Field :=
  cubicDisplacement (cantileverM0 P T w₀ w₁ L) (cantileverM1 P w₀ w₁ L) (-w₀/2) (-w₁/6) EI

/-- Fixity applies to rotation and transverse displacement at the left end. -/
theorem cantilever_fixed_end (P T w₀ w₁ L EI : ℝ) :
    (cantileverSlope P T w₀ w₁ L EI).eval 0 = 0 ∧
    (cantileverDisplacement P T w₀ w₁ L EI).eval 0 = 0 := by
  simp [cantileverSlope, cantileverDisplacement, cubicSlope, cubicDisplacement]

/-- Free-end actions agree with the end force and counterclockwise couple. -/
theorem cantilever_end_moment (P T w₀ w₁ L : ℝ) :
    (cantileverMoment P T w₀ w₁ L).eval L = T := by
  simp [cantileverMoment, cubicMoment, cantileverM0, cantileverM1]
  ring

theorem cantilever_end_shear (P T w₀ w₁ L : ℝ) :
    (cantileverMoment P T w₀ w₁ L).derivative.eval L = P := by
  simp [cantileverMoment, cubicMoment, cantileverM0, cantileverM1,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  ring

/-- The beam's actual downward intensity determines the curvature of M. -/
theorem cantilever_load_balance (P T w₀ w₁ L x : ℝ) :
    (cantileverMoment P T w₀ w₁ L).derivative.derivative.eval x = -(w₀ + w₁*x) := by
  simp [cantileverMoment, cubicMoment, cantileverM0, cantileverM1,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  ring

/-- Deflection and rotation derive from the same polynomial moment field. -/
theorem cubic_displacement_derivative (m₀ m₁ m₂ m₃ EI : ℝ) :
    (cubicDisplacement m₀ m₁ m₂ m₃ EI).derivative = cubicSlope m₀ m₁ m₂ m₃ EI := by
  simp [cubicDisplacement, cubicSlope, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  simp only [show C (2 : ℝ) = (2 : Field) from map_natCast (Polynomial.C : ℝ →+* Field) 2,
    show C (3 : ℝ) = (3 : Field) from map_natCast (Polynomial.C : ℝ →+* Field) 3,
    show C (4 : ℝ) = (4 : Field) from map_natCast (Polynomial.C : ℝ →+* Field) 4,
    show C (5 : ℝ) = (5 : Field) from map_natCast (Polynomial.C : ℝ →+* Field) 5]
  ring
  all_goals simp

theorem cubic_constitutive (m₀ m₁ m₂ m₃ EI x : ℝ) (hEI : EI ≠ 0) :
    EI * (cubicSlope m₀ m₁ m₂ m₃ EI).derivative.eval x = (cubicMoment m₀ m₁ m₂ m₃).eval x := by
  simp [cubicSlope, cubicMoment, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  field_simp
  ring

theorem cantilever_real_slope (P T w₀ w₁ L EI x : ℝ) :
    HasDerivAt (fun t : ℝ => (cantileverDisplacement P T w₀ w₁ L EI).eval t)
      ((cantileverSlope P T w₀ w₁ L EI).eval x) x := by
  apply displacement_slope
  exact cubic_displacement_derivative _ _ _ _ _


end

end RealBeamFields
