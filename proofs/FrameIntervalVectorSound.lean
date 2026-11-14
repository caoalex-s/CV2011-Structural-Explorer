import FrameIntervalVector
import FrameEnclosure
import FrameMatrixResidual

/-! Entrywise enclosure arithmetic connects to finite sums and the infinity-norm
    hypotheses. No numerical matrix rank or stability decision is assumed. -/
namespace FrameIntervalVectorSound
open FrameIntervalOps FrameIntervalVector FrameEnclosure
noncomputable section

theorem dot_contains {bits n : Nat} {left right : Fin n → Bounds} {out : Bounds}
    {x y : Fin n → ℝ} (h : dot bits left right = some out)
    (hx : ∀ i, Contains (left i) (x i)) (hy : ∀ i, Contains (right i) (y i)) :
    Contains out (∑ i, x i * y i) := by
  induction n generalizing out with
  | zero =>
    have hp := executable_point_contains h
    simpa using hp
  | succ n ih =>
    obtain ⟨head, hhead, tail, htail, hadd⟩ := by
      simpa only [dot, Option.bind_eq_bind, Option.bind_eq_some] using h
    have hheadContains := executable_multiply_contains hhead (hx 0) (hy 0)
    have htailContains := ih htail (fun i => hx i.succ) (fun i => hy i.succ)
    have hsum := executable_add_contains hadd hheadContains htailContains
    simpa [Fin.sum_univ_succ] using hsum

theorem magnitude_bound {bounds : Bounds} {x : ℝ} (hx : Contains bounds x) :
    |x| ≤ (magnitude bounds : ℝ) := by
  apply abs_le.mpr
  have hl : -(bounds.lower : ℝ) ≤ (magnitude bounds : ℝ) := by
    simp only [magnitude, upperOf_eq_max]
    exact_mod_cast (le_max_left (-bounds.lower) bounds.upper)
  have hu : (bounds.upper : ℝ) ≤ (magnitude bounds : ℝ) := by
    simp only [magnitude, upperOf_eq_max]
    exact_mod_cast (le_max_right (-bounds.lower) bounds.upper)
  constructor <;> dsimp [Contains] at * <;> linarith

theorem magnitudeSum_bound {n : Nat} {bounds : Fin n → Bounds} {x : Fin n → ℝ}
    (hx : ∀ i, Contains (bounds i) (x i)) :
    (∑ i, |x i|) ≤ (magnitudeSum bounds : ℝ) := by
  induction n with
  | zero => simp [magnitudeSum]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have hhead := magnitude_bound (hx 0)
    have htail := ih (fun i => hx i.succ)
    simpa [magnitudeSum, Rat.cast_add] using add_le_add hhead htail

/-- Rational row checks are sufficient for the actual real defect matrix.
    The source bridge must establish containment of every defect entry. -/
theorem checked_defect_rows {n : Nat} {matrix inverse : Fin n → Fin n → ℝ}
    {bounds : Fin n → Fin n → Bounds} {q : Rat}
    (hcontains : ∀ i j, Contains (bounds i j) (FrameMatrixResidual.defect matrix inverse i j))
    (hcheck : ∀ i, magnitudeSum (bounds i) ≤ q) :
    ∀ i, (∑ j, |FrameMatrixResidual.defect matrix inverse i j|) ≤ (q : ℝ) := by
  intro i
  exact le_trans (magnitudeSum_bound (hcontains i)) (by exact_mod_cast hcheck i)

end
end FrameIntervalVectorSound
