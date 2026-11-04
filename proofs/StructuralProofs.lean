import Std.Tactic

/-!
# Exact two-support reaction identities

Coordinates, resultant load W, and resultant moment Q are represented as scaled
integers after clearing the decimal input denominators. For distinct supports
a < b, the reaction numerators are W*b-Q and Q-W*a, with common denominator b-a.
The theorems establish the two equilibrium identities before division.

The mechanical idealisation, translation of the drawing, positivity of span,
and rational conversion are separately checked by the application. These
theorems do not certify the frame solver or arbitrary solution steps.
-/
namespace StructuralProofs

def leftNumerator (W Q b : Int) : Int := W * b - Q
def rightNumerator (W Q a : Int) : Int := Q - W * a

theorem reaction_force_balance (W Q a b : Int) :
    leftNumerator W Q b + rightNumerator W Q a = W * (b - a) := by
  simp only [leftNumerator, rightNumerator, Int.mul_sub]
  omega

theorem reaction_moment_balance (W Q a b : Int) :
    a * leftNumerator W Q b + b * rightNumerator W Q a = Q * (b - a) := by
  simp only [leftNumerator, rightNumerator, Int.mul_sub, Int.sub_mul]
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- Reversing the plotting side preserves the represented moment value. -/
def plottedMoment (compressionSide : Bool) (moment : Int) : Int :=
  if compressionSide then moment else -moment

theorem plotting_sides_are_opposite (moment : Int) :
    plottedMoment true moment = -plottedMoment false moment := by
  simp [plottedMoment]

#print axioms reaction_force_balance
#print axioms reaction_moment_balance
#print axioms plotting_sides_are_opposite

end StructuralProofs

/-!
# Single point-force lesson

P, L, a, and x are integer representations after clearing decimal denominators.
The reaction, shear, and moment expressions below are numerators: division by
the positive span and restoration of the input scales are outside this file.
These parameterized statements establish algebra and ordering for every encoded
input, not just the published central-load example. Mechanical idealisation,
real calculus, drawing translation, and floating-point rendering are not proved.
-/
namespace LessonBeam

def reactionA (P L a : Int) : Int := P * (L - a)
def shearBefore (P L a : Int) : Int := reactionA P L a
def shearAfter (P L a : Int) : Int := reactionA P L a - P * L
def momentBefore (P L a x : Int) : Int := reactionA P L a * x
def momentAfter (P L a x : Int) : Int := reactionA P L a * x - P * L * (x - a)
def shear (P L a x : Int) : Int := if x < a then shearBefore P L a else shearAfter P L a
def moment (P L a x : Int) : Int := if x < a then momentBefore P L a x else momentAfter P L a x
def peak (P L a : Int) : Int := P * (L - a) * a

/-- With no horizontal external force, the retained segment has N = 0. -/
theorem normal_from_equilibrium (N : Int) (balance : 0 - N = 0) : N = 0 := by
  omega

/-- Balances on the retained left segment, using the right-hand value at a. -/
theorem section_equilibrium (P L a x : Int) :
    reactionA P L a - (if x < a then 0 else P * L) - shear P L a x = 0 ∧
    moment P L a x - reactionA P L a * x + (if x < a then 0 else P * L * (x - a)) = 0 := by
  by_cases h : x < a
  · simp only [shear, moment, if_pos h, shearBefore, momentBefore]
    omega
  · simp only [shear, moment, if_neg h, shearAfter, momentAfter]
    omega

theorem shear_jump (P L a : Int) :
    shearAfter P L a - shearBefore P L a = -(P * L) := by
  simp only [shearAfter, shearBefore]
  omega

/-- Agreement at the load: there is no moment jump without an applied couple. -/
theorem moment_at_load (P L a : Int) :
    momentBefore P L a a = momentAfter P L a a := by
  simp [momentBefore, momentAfter]

theorem moment_after_factored (P L a x : Int) :
    momentAfter P L a x = P * a * (L - x) := by
  simp only [momentAfter, reactionA, Int.mul_sub, Int.sub_mul]
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- Finite-increment identities are algebraic counterparts of the branch slopes.
They are not claims that Lean has formalized real differentiation. -/
theorem moment_increment_before (P L a x h : Int) :
    momentBefore P L a (x + h) - momentBefore P L a x = shearBefore P L a * h := by
  simp only [momentBefore, shearBefore, Int.mul_add]
  omega

theorem moment_increment_after (P L a x h : Int) :
    momentAfter P L a (x + h) - momentAfter P L a x = shearAfter P L a * h := by
  simp only [momentAfter, shearAfter, Int.mul_sub, Int.mul_add, Int.sub_mul]
  omega

/-- Nonnegative loading and 0 <= a <= L give a global upper bound for both
linear branches. In particular this covers every section 0 <= x <= L. -/
theorem moment_maximum (P L a x : Int) (hP : 0 ≤ P) (ha : 0 ≤ a) (haL : a ≤ L) :
    moment P L a x ≤ peak P L a := by
  by_cases h : x < a
  · simp only [moment, if_pos h, momentBefore, reactionA, peak]
    exact Int.mul_le_mul_of_nonneg_left (Int.le_of_lt h)
      (Int.mul_nonneg hP (Int.sub_nonneg_of_le haL))
  · simp only [moment, if_neg h, moment_after_factored]
    have distance : L - x ≤ L - a := by omega
    have bound := Int.mul_le_mul_of_nonneg_left distance (Int.mul_nonneg hP ha)
    simpa only [peak, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using bound

theorem moment_attains_maximum (P L a : Int) : moment P L a a = peak P L a := by
  simp [moment, momentAfter, reactionA, peak]

#print axioms section_equilibrium
#print axioms normal_from_equilibrium
#print axioms shear_jump
#print axioms moment_at_load
#print axioms moment_after_factored
#print axioms moment_increment_before
#print axioms moment_increment_after
#print axioms moment_maximum
#print axioms moment_attains_maximum

end LessonBeam
