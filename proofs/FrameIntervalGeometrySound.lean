import FrameIntervalGeometry
import FrameEnclosure

/-! Original-endpoint interpretation of the executable member enclosure.
    Source decoding and segment ownership remain separate checker obligations. -/
namespace FrameIntervalGeometrySound
open FrameIntervalOps FrameIntervalGeometry FrameEnclosure
noncomputable section

theorem member_contains {bits : Nat} {dx dy : Rat} {root : Bounds} {out : MemberBounds}
    (h : member bits dx dy root = some out) :
    Contains out.length (Real.sqrt ((dx : ℝ)^2 + (dy : ℝ)^2)) ∧
    Contains out.cosine ((dx : ℝ) / Real.sqrt ((dx : ℝ)^2 + (dy : ℝ)^2)) ∧
    Contains out.sine ((dy : ℝ) / Real.sqrt ((dx : ℝ)^2 + (dy : ℝ)^2)) := by
  unfold member at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨squaredBounds, hsquared, hremaining⟩ := Option.bind_eq_some.mp h
    obtain ⟨length, hroot, hpositive⟩ := Option.bind_eq_some.mp hremaining
    split at hpositive
    · simp at hpositive
    · simp only [bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at hpositive
      obtain ⟨horizontal, hx, vertical, hy, cosine, hc, sine, hs, hout⟩ := hpositive
      subst out
      have hsquaredContains : Contains squaredBounds ((dx : ℝ)^2 + (dy : ℝ)^2) := by
        have hp := executable_point_contains hsquared
        simpa [Rat.cast_add, Rat.cast_mul, pow_two] using hp
      have hl := executable_sqrt_contains hroot hsquaredContains
      exact ⟨hl, executable_divide_contains hc (executable_point_contains hx) hl,
        executable_divide_contains hs (executable_point_contains hy) hl⟩

/-- The enclosed quantities refer to the actual endpoints, including irrational
    lengths. No rounded orientation is substituted into ExactGeometry. -/
theorem original_endpoints {bits : Nat} {ax ay bx by : Rat} {root : Bounds} {out : MemberBounds}
    (h : member bits (bx-ax) (by-ay) root = some out) :
    Contains out.length (ExactGeometry.distance (ax, ay) (bx, by)) ∧
    Contains out.cosine (ExactGeometry.direction (ax, ay) (bx, by)).cosine ∧
    Contains out.sine (ExactGeometry.direction (ax, ay) (bx, by)).sine := by
  simpa [ExactGeometry.distance, ExactGeometry.direction, ExactGeometry.dx,
    ExactGeometry.dy, Rat.cast_sub] using member_contains h

end
end FrameIntervalGeometrySound
