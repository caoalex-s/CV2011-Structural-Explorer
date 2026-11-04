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
  all_goals simp

/-- After the point force, the elastic-curve derivative is physical slope. -/
theorem point_after_derivative (P a L EI : ℝ) :
    (deflectionAfter P a L EI).derivative = slopeAfter P a L EI := by
  simp [deflectionAfter, slopeAfter, point_before_derivative, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
  simp only [show C (3 : ℝ) = (3 : Field) from map_natCast (Polynomial.C : ℝ →+* Field) 3]
  ring
  all_goals simp

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

/-- Select the left or right polynomial at an action coordinate. -/
def splice (left right : Field) (a x : ℝ) : ℝ :=
  if x < a then left.eval x else right.eval x

theorem splice_derivative_before (left right : Field) (a x : ℝ) (hx : x < a) :
    HasDerivAt (splice left right a) (left.derivative.eval x) x := by
  apply (left.hasDerivAt x).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hx] with t ht
  simp [splice, ht]

theorem splice_derivative_after (left right : Field) (a x : ℝ) (hx : a < x) :
    HasDerivAt (splice left right a) (right.derivative.eval x) x := by
  apply (right.hasDerivAt x).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with t ht
  simp [splice, not_lt.mpr ht.le]

/-- Matching values and slopes give an actual derivative at the join. -/
theorem splice_derivative_at (left right : Field) (a : ℝ)
    (hvalue : left.eval a = right.eval a)
    (hslope : left.derivative.eval a = right.derivative.eval a) :
    HasDerivAt (splice left right a) (right.derivative.eval a) a := by
  have hleft : HasDerivWithinAt (splice left right a) (right.derivative.eval a) (Set.Iio a) a := by
    apply ((left.hasDerivAt a).congr_deriv hslope).hasDerivWithinAt.congr
    · intro t ht
      change t < a at ht
      simp [splice, ht]
    · simp [splice, ← hvalue]
  have hright : HasDerivWithinAt (splice left right a) (right.derivative.eval a) (Set.Ici a) a := by
    apply (right.hasDerivAt a).hasDerivWithinAt.congr
    · intro t ht
      change a ≤ t at ht
      simp [splice, not_lt.mpr ht]
    · simp [splice]
  have h := hleft.union hright
  have hunion : Set.Iio a ∪ Set.Ici a = Set.univ := Set.Iio_union_Ici
  rw [hunion, hasDerivWithinAt_univ] at h
  exact h

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


/-- The selected displacement satisfies endpoint support values when the
load coordinate lies on the span. Endpoint loads use the joined value. -/
theorem point_selected_supports (P a L EI : ℝ) (hL : 0 < L) (hEI : 0 < EI)
    (ha₀ : 0 ≤ a) (haL : a ≤ L) :
    pointDisplacement P a L EI 0 = 0 ∧ pointDisplacement P a L EI L = 0 := by
  constructor
  · by_cases ha : 0 < a
    · simpa [pointDisplacement, ha] using point_left_support P a L EI
    · have haeq : a = 0 := le_antisymm (le_of_not_gt ha) ha₀
      subst a
      simpa [pointDisplacement, ← point_displacement_continuity] using point_left_support P 0 L EI
  · simpa [pointDisplacement, not_lt.mpr haL] using
      point_right_support P a L EI (ne_of_gt hL) (ne_of_gt hEI)

/-- For a fixed moment field, the two integration constants in each
interval are unique if their difference is affine, displacement and slope are
continuous at the load, and both endpoint displacements are prescribed. -/
theorem affine_boundary_uniqueness (L a c₀ c₁ d₀ d₁ : ℝ) (hL : L ≠ 0)
    (hleft : c₀ = 0) (hright : d₀ + d₁*L = 0)
    (hdisplacement : c₀ + c₁*a = d₀ + d₁*a) (hslope : c₁ = d₁) :
    c₀ = 0 ∧ c₁ = 0 ∧ d₀ = 0 ∧ d₁ = 0 := by
  subst c₁
  have hd₀ : d₀ = 0 := by linarith
  have hproduct : d₁*L = 0 := by linarith
  have hd₁ : d₁ = 0 := (mul_eq_zero.mp hproduct).resolve_right hL
  exact ⟨hleft, hd₁, hd₀, hd₁⟩

/-- A real polynomial with zero second derivative is affine. This supplies,
rather than assumes, the integration-constant form used in uniqueness. -/
theorem affine_of_second_derivative_zero (p : Field) (h : p.derivative.derivative = 0) :
    ∃ c₀ c₁ : ℝ, p = C c₀ + C c₁ * X := by
  let c₁ : ℝ := p.derivative.coeff 0
  have hslope : p.derivative = C c₁ := Polynomial.eq_C_of_derivative_eq_zero h
  let remainder : Field := p - C c₁ * X
  have hzero : remainder.derivative = 0 := by
    simp [remainder, Polynomial.derivative_mul, hslope]
  have hconstant : remainder = C (remainder.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hzero
  refine ⟨remainder.coeff 0, c₁, ?_⟩
  dsimp [remainder] at hconstant ⊢
  linear_combination hconstant

/-- Two polynomial elastic-curve branches with the same curvature, endpoint
values and compatible value/slope joins have the same displacement fields. -/
theorem piecewise_curvature_uniqueness (left right otherLeft otherRight : Field) (a L : ℝ)
    (hL : L ≠ 0)
    (hcurvatureLeft : left.derivative.derivative = otherLeft.derivative.derivative)
    (hcurvatureRight : right.derivative.derivative = otherRight.derivative.derivative)
    (hleft : left.eval 0 = otherLeft.eval 0) (hright : right.eval L = otherRight.eval L)
    (hjoin : left.eval a - otherLeft.eval a = right.eval a - otherRight.eval a)
    (hslope : left.derivative.eval a - otherLeft.derivative.eval a =
              right.derivative.eval a - otherRight.derivative.eval a) :
    left = otherLeft ∧ right = otherRight := by
  have hlzero : (left - otherLeft).derivative.derivative = 0 := by
    simp [Polynomial.derivative_sub, hcurvatureLeft]
  have hrzero : (right - otherRight).derivative.derivative = 0 := by
    simp [Polynomial.derivative_sub, hcurvatureRight]
  obtain ⟨c₀, c₁, hc⟩ := affine_of_second_derivative_zero _ hlzero
  obtain ⟨d₀, d₁, hd⟩ := affine_of_second_derivative_zero _ hrzero
  have h₀ : c₀ = 0 := by
    have h := congrArg (Polynomial.eval (0 : ℝ)) hc
    simpa [hleft] using h.symm
  have hLvalue : d₀ + d₁*L = 0 := by
    have h := congrArg (Polynomial.eval L) hd
    simpa [hright] using h.symm
  have hv : c₀ + c₁*a = d₀ + d₁*a := by
    have hleftEval := congrArg (Polynomial.eval a) hc
    have hrightEval := congrArg (Polynomial.eval a) hd
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] at hleftEval hrightEval
    linarith
  have ht : c₁ = d₁ := by
    have hleftDeriv := congrArg (fun p : Field => p.derivative.eval a) hc
    have hrightDeriv := congrArg (fun p : Field => p.derivative.eval a) hd
    simp [Polynomial.derivative_sub, Polynomial.derivative_mul] at hleftDeriv hrightDeriv
    linarith
  obtain ⟨hc₀, hc₁, hd₀, hd₁⟩ := affine_boundary_uniqueness L a c₀ c₁ d₀ d₁ hL h₀ hLvalue hv ht
  constructor
  · have : left - otherLeft = 0 := by simpa [hc₀, hc₁] using hc
    exact sub_eq_zero.mp this
  · have : right - otherRight = 0 := by simpa [hd₀, hd₁] using hd
    exact sub_eq_zero.mp this

/-- Equal curvature, value and slope at one end determine a polynomial. -/
theorem polynomial_curvature_end_unique (p q : Field) (x₀ : ℝ)
    (hcurvature : p.derivative.derivative = q.derivative.derivative)
    (hvalue : p.eval x₀ = q.eval x₀)
    (hslope : p.derivative.eval x₀ = q.derivative.eval x₀) : p = q := by
  have hzero : (p-q).derivative.derivative = 0 := by
    simp [Polynomial.derivative_sub, hcurvature]
  obtain ⟨c₀, c₁, hc⟩ := affine_of_second_derivative_zero _ hzero
  have hc₁ : c₁ = 0 := by
    have h := congrArg (fun field : Field => field.derivative.eval x₀) hc
    simp [Polynomial.derivative_sub, Polynomial.derivative_mul, hslope] at h
    exact h.symm
  have hc₀ : c₀ = 0 := by
    have h := congrArg (Polynomial.eval x₀) hc
    simp [hvalue, hc₁] at h
    exact h.symm
  have hdiff : p-q = 0 := by simpa [hc₀, hc₁] using hc
  exact sub_eq_zero.mp hdiff

/-- A loaded point-force beam solution records the actual polynomial fields
and their balance, elastic, boundary and jump obligations. The predicate is
not a certificate until a theorem constructs an inhabitant or an independent
checker proves these obligations for a specific model. -/
structure PointBeamSolution (P a L EI : ℝ) where
  vLeft : Field
  vRight : Field
  thetaLeft : Field
  thetaRight : Field
  momentLeft : Field
  momentRight : Field
  shearLeft : Field
  shearRight : Field
  spanPositive : 0 < L
  rigidityPositive : 0 < EI
  loadAfterLeft : 0 ≤ a
  loadBeforeRight : a ≤ L
  leftKinematics : vLeft.derivative = thetaLeft
  rightKinematics : vRight.derivative = thetaRight
  leftConstitutive : ∀ x, EI * thetaLeft.derivative.eval x = momentLeft.eval x
  rightConstitutive : ∀ x, EI * thetaRight.derivative.eval x = momentRight.eval x
  leftMomentBalance : momentLeft.derivative = shearLeft
  rightMomentBalance : momentRight.derivative = shearRight
  leftShearBalance : shearLeft.derivative = 0
  rightShearBalance : shearRight.derivative = 0
  forceJump : shearRight.eval a - shearLeft.eval a = -P
  momentJoin : momentRight.eval a = momentLeft.eval a
  leftMomentSupport : momentLeft.eval 0 = 0
  rightMomentSupport : momentRight.eval L = 0
  leftDisplacementSupport : vLeft.eval 0 = 0
  rightDisplacementSupport : vRight.eval L = 0
  displacementJoin : vRight.eval a = vLeft.eval a
  slopeJoin : thetaRight.eval a = thetaLeft.eval a

/-- The prescribed endpoint-supported point-force fields satisfy the complete
loaded-beam predicate under positive span and rigidity and an on-span load. -/
theorem point_solution_exists (P a L EI : ℝ) (hL : 0 < L) (hEI : 0 < EI)
    (ha₀ : 0 ≤ a) (haL : a ≤ L) : Nonempty (PointBeamSolution P a L EI) := by
  refine ⟨{
    vLeft := deflectionBefore P a L EI
    vRight := deflectionAfter P a L EI
    thetaLeft := slopeBefore P a L EI
    thetaRight := slopeAfter P a L EI
    momentLeft := pointMomentBefore P a L
    momentRight := pointMomentAfter P a L
    shearLeft := pointShearBefore P a L
    shearRight := pointShearAfter P a L
    spanPositive := hL
    rigidityPositive := hEI
    loadAfterLeft := ha₀
    loadBeforeRight := haL
    leftKinematics := point_before_derivative P a L EI
    rightKinematics := point_after_derivative P a L EI
    leftConstitutive := fun x => point_curvature_before P a L EI x (ne_of_gt hEI)
    rightConstitutive := fun x => point_curvature_after P a L EI x (ne_of_gt hEI)
    leftMomentBalance := point_moment_derivative_before P a L
    rightMomentBalance := point_moment_derivative_after P a L
    leftShearBalance := ?_
    rightShearBalance := ?_
    forceJump := point_shear_jump P a L
    momentJoin := point_moment_continuity P a L
    leftMomentSupport := ?_
    rightMomentSupport := ?_
    leftDisplacementSupport := point_left_support P a L EI
    rightDisplacementSupport := point_right_support P a L EI (ne_of_gt hL) (ne_of_gt hEI)
    displacementJoin := (point_displacement_continuity P a L EI).symm
    slopeJoin := (point_slope_continuity P a L EI).symm
  }⟩
  · simp [pointShearBefore]
  · simp [pointShearAfter, pointShearBefore, shearAfterForce]
  · simp [pointMomentBefore]
  · simp [pointMomentAfter, pointMomentBefore, momentAfterActions, leftReaction]
    field_simp <;> ring

/-- Two solutions of the loaded point-force predicate have the same fields.
The proof first fixes moment by equilibrium and jump conditions, then fixes
displacement by constitutive, support, and compatibility conditions. -/
theorem point_solution_unique (P a L EI : ℝ) (A B : PointBeamSolution P a L EI) :
    A.vLeft = B.vLeft ∧ A.vRight = B.vRight ∧
    A.thetaLeft = B.thetaLeft ∧ A.thetaRight = B.thetaRight ∧
    A.momentLeft = B.momentLeft ∧ A.momentRight = B.momentRight ∧
    A.shearLeft = B.shearLeft ∧ A.shearRight = B.shearRight := by
  have hML : A.momentLeft.derivative.derivative = B.momentLeft.derivative.derivative := by
    rw [A.leftMomentBalance, B.leftMomentBalance, A.leftShearBalance, B.leftShearBalance]
  have hMR : A.momentRight.derivative.derivative = B.momentRight.derivative.derivative := by
    rw [A.rightMomentBalance, B.rightMomentBalance, A.rightShearBalance, B.rightShearBalance]
  have hmJoin : A.momentLeft.eval a - B.momentLeft.eval a =
      A.momentRight.eval a - B.momentRight.eval a := by
    rw [A.momentJoin, B.momentJoin]
  have hmSlope : A.momentLeft.derivative.eval a - B.momentLeft.derivative.eval a =
      A.momentRight.derivative.eval a - B.momentRight.derivative.eval a := by
    rw [A.leftMomentBalance, B.leftMomentBalance, A.rightMomentBalance, B.rightMomentBalance]
    have hA := A.forceJump
    have hB := B.forceJump
    linarith
  obtain ⟨hmLeft, hmRight⟩ := piecewise_curvature_uniqueness
    A.momentLeft A.momentRight B.momentLeft B.momentRight a L (ne_of_gt A.spanPositive)
    hML hMR (by rw [A.leftMomentSupport, B.leftMomentSupport])
    (by rw [A.rightMomentSupport, B.rightMomentSupport]) hmJoin hmSlope
  have htLeft : A.thetaLeft.derivative = B.thetaLeft.derivative := by
    apply Polynomial.funext
    intro x
    apply mul_left_cancel₀ (ne_of_gt A.rigidityPositive)
    rw [A.leftConstitutive x, B.leftConstitutive x, hmLeft]
  have htRight : A.thetaRight.derivative = B.thetaRight.derivative := by
    apply Polynomial.funext
    intro x
    apply mul_left_cancel₀ (ne_of_gt A.rigidityPositive)
    rw [A.rightConstitutive x, B.rightConstitutive x, hmRight]
  have hvL : A.vLeft.derivative.derivative = B.vLeft.derivative.derivative := by
    rw [A.leftKinematics, B.leftKinematics, htLeft]
  have hvR : A.vRight.derivative.derivative = B.vRight.derivative.derivative := by
    rw [A.rightKinematics, B.rightKinematics, htRight]
  have hvJoin : A.vLeft.eval a - B.vLeft.eval a = A.vRight.eval a - B.vRight.eval a := by
    rw [A.displacementJoin, B.displacementJoin]
  have hvSlope : A.vLeft.derivative.eval a - B.vLeft.derivative.eval a =
      A.vRight.derivative.eval a - B.vRight.derivative.eval a := by
    rw [A.leftKinematics, B.leftKinematics, A.rightKinematics, B.rightKinematics,
      A.slopeJoin, B.slopeJoin]
  obtain ⟨hvLeft, hvRight⟩ := piecewise_curvature_uniqueness
    A.vLeft A.vRight B.vLeft B.vRight a L (ne_of_gt A.spanPositive)
    hvL hvR (by rw [A.leftDisplacementSupport, B.leftDisplacementSupport])
    (by rw [A.rightDisplacementSupport, B.rightDisplacementSupport]) hvJoin hvSlope
  have hsLeft : A.thetaLeft = B.thetaLeft := by
    rw [← A.leftKinematics, ← B.leftKinematics, hvLeft]
  have hsRight : A.thetaRight = B.thetaRight := by
    rw [← A.rightKinematics, ← B.rightKinematics, hvRight]
  have hfLeft : A.shearLeft = B.shearLeft := by
    rw [← A.leftMomentBalance, ← B.leftMomentBalance, hmLeft]
  have hfRight : A.shearRight = B.shearRight := by
    rw [← A.rightMomentBalance, ← B.rightMomentBalance, hmRight]
  exact ⟨hvLeft, hvRight, hsLeft, hsRight, hmLeft, hmRight, hfLeft, hfRight⟩

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



/-- The common cantilever load intensity is downward-positive. -/
def cantileverIntensity (w₀ w₁ : ℝ) : Field := C w₀ + C w₁ * X

def cantileverShear (P T w₀ w₁ L : ℝ) : Field :=
  (cantileverMoment P T w₀ w₁ L).derivative

/-- This predicate records a loaded cantilever bending solution. Axial response,
frame assembly and the numerical solver remain separate obligations. -/
structure CantileverSolution (P T w₀ w₁ L EI : ℝ) where
  v : Field
  theta : Field
  moment : Field
  shear : Field
  spanPositive : 0 < L
  rigidityPositive : 0 < EI
  kinematics : v.derivative = theta
  constitutive : ∀ x, EI * theta.derivative.eval x = moment.eval x
  momentBalance : moment.derivative = shear
  shearBalance : shear.derivative = -cantileverIntensity w₀ w₁
  endMoment : moment.eval L = T
  endShear : shear.eval L = P
  fixedSlope : theta.eval 0 = 0
  fixedDisplacement : v.eval 0 = 0

/-- The explicit mixed-load polynomial fields solve the cantilever predicate. -/
theorem cantilever_solution_exists (P T w₀ w₁ L EI : ℝ) (hL : 0 < L) (hEI : 0 < EI) :
    Nonempty (CantileverSolution P T w₀ w₁ L EI) := by
  refine ⟨{
    v := cantileverDisplacement P T w₀ w₁ L EI
    theta := cantileverSlope P T w₀ w₁ L EI
    moment := cantileverMoment P T w₀ w₁ L
    shear := cantileverShear P T w₀ w₁ L
    spanPositive := hL
    rigidityPositive := hEI
    kinematics := ?_
    constitutive := ?_
    momentBalance := rfl
    shearBalance := ?_
    endMoment := cantilever_end_moment P T w₀ w₁ L
    endShear := cantilever_end_shear P T w₀ w₁ L
    fixedSlope := (cantilever_fixed_end P T w₀ w₁ L EI).1
    fixedDisplacement := (cantilever_fixed_end P T w₀ w₁ L EI).2
  }⟩
  · exact cubic_displacement_derivative _ _ _ _ _
  · intro x
    exact cubic_constitutive _ _ _ _ _ x (ne_of_gt hEI)
  · apply Polynomial.funext
    intro x
    simpa [cantileverShear, cantileverIntensity] using cantilever_load_balance P T w₀ w₁ L x

/-- A polynomial cantilever solution is unique under the same applied loads. -/
theorem cantilever_solution_unique (P T w₀ w₁ L EI : ℝ)
    (A B : CantileverSolution P T w₀ w₁ L EI) :
    A.v = B.v ∧ A.theta = B.theta ∧ A.moment = B.moment ∧ A.shear = B.shear := by
  have hmomentCurvature : A.moment.derivative.derivative = B.moment.derivative.derivative := by
    rw [A.momentBalance, B.momentBalance, A.shearBalance, B.shearBalance]
  have hmoment : A.moment = B.moment := polynomial_curvature_end_unique A.moment B.moment L
    hmomentCurvature (by rw [A.endMoment, B.endMoment])
    (by rw [A.momentBalance, B.momentBalance, A.endShear, B.endShear])
  have hthetaCurvature : A.theta.derivative = B.theta.derivative := by
    apply Polynomial.funext
    intro x
    apply mul_left_cancel₀ (ne_of_gt A.rigidityPositive)
    rw [A.constitutive x, B.constitutive x, hmoment]
  have hvCurvature : A.v.derivative.derivative = B.v.derivative.derivative := by
    rw [A.kinematics, B.kinematics, hthetaCurvature]
  have hv : A.v = B.v := polynomial_curvature_end_unique A.v B.v 0 hvCurvature
    (by rw [A.fixedDisplacement, B.fixedDisplacement])
    (by rw [A.kinematics, B.kinematics, A.fixedSlope, B.fixedSlope])
  have htheta : A.theta = B.theta := by rw [← A.kinematics, ← B.kinematics, hv]
  have hshear : A.shear = B.shear := by rw [← A.momentBalance, ← B.momentBalance, hmoment]
  exact ⟨hv, htheta, hmoment, hshear⟩


end

end RealBeamFields
