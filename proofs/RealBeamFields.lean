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
theorem shear_balance (V q : Field) (h : V.derivative = -q) (x : ℝ) :
    HasDerivAt (fun t : ℝ => V.eval t) (-q.eval x) x := by
  simpa [h] using V.hasDerivAt x

/-- On a smooth interval, the real moment derivative equals shear. -/
theorem moment_balance (M V : Field) (h : M.derivative = V) (x : ℝ) :
    HasDerivAt (fun t : ℝ => M.eval t) (V.eval x) x := by
  simpa [h] using M.hasDerivAt x

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
  simp [deflectionBefore, slopeBefore]
  ring

/-- After the point force, the elastic-curve derivative is physical slope. -/
theorem point_after_derivative (P a L EI : ℝ) :
    (deflectionAfter P a L EI).derivative = slopeAfter P a L EI := by
  simp [deflectionAfter, slopeAfter, point_before_derivative]
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

/-- The two displacement branches agree at the action. -/
theorem point_displacement_continuity (P a L EI : ℝ) :
    (deflectionBefore P a L EI).eval a = (deflectionAfter P a L EI).eval a := by
  simp [deflectionAfter]

/-- The two physical-slope branches agree at the action. -/
theorem point_slope_continuity (P a L EI : ℝ) :
    (slopeBefore P a L EI).eval a = (slopeAfter P a L EI).eval a := by
  simp [slopeAfter]

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

end RealBeamFields
