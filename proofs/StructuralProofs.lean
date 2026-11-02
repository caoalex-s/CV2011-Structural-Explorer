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
