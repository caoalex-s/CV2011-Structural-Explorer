import SmokeChecker
import Mathlib

namespace WasmSmoke

/-- Acceptance implies the equation and its unique rational solution. -/
theorem accepts_sound (a x : Rat) (h : accepts a x = true) :
    2 * x = a ∧ x = a / 2 ∧ ∀ y : Rat, 2 * y = a → y = x := by
  have equation : 2 * x = a := of_decide_eq_true h
  refine ⟨equation, ?_, ?_⟩
  · linarith
  · intro y hy
    linarith

/-- Completeness for the same named computable predicate. -/
theorem accepts_complete (a x : Rat) (h : 2 * x = a) : accepts a x = true := by
  exact decide_eq_true h

-- The harness displays only acceptance status and exact rational strings.
-- It makes no claim about real-valued portal displacements or reactions.
#print axioms accepts_sound
#print axioms accepts_complete

end WasmSmoke
