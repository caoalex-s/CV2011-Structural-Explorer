import ExactGeometry

/-! Local algebra for the source-derived rigid-point admissible basis.
    Full source ownership and degree-class equivalence are separate obligations. -/
namespace FrameAdmissiblePoint
noncomputable section

def normalWork (c s x y : ℝ) : ℝ := c*x + s*y
def tangentCoordinate (c s x y : ℝ) : ℝ := -s*x + c*y

theorem tangent_admissible (c s alpha : ℝ) :
    normalWork c s (-s*alpha) (c*alpha) = 0 := by
  unfold normalWork
  ring

theorem tangent_independent {c s alpha : ℝ} (hn : c^2+s^2=1)
    (hx : -s*alpha=0) (hy : c*alpha=0) : alpha=0 := by
  nlinarith [congrArg (fun v => v*alpha) hn,
    congrArg (fun v => v*s) hx, congrArg (fun v => v*c) hy]

theorem single_normal_kernel {c s x y : ℝ} (hn : c^2+s^2=1)
    (h : normalWork c s x y = 0) :
    x = -s * tangentCoordinate c s x y ∧ y = c * tangentCoordinate c s x y := by
  dsimp [normalWork] at h
  dsimp [tangentCoordinate]
  constructor
  · nlinarith [congrArg (fun v => v*x) hn, congrArg (fun v => v*c) h]
  · nlinarith [congrArg (fun v => v*y) hn, congrArg (fun v => v*s) h]

theorem two_normals_kernel {c s d t x y : ℝ}
    (hfirst : normalWork c s x y = 0) (hsecond : normalWork d t x y = 0)
    (hdet : c*t-s*d ≠ 0) : x=0 ∧ y=0 := by
  dsimp [normalWork] at hfirst hsecond
  have hx : (c*t-s*d)*x=0 := by
    nlinarith [congrArg (fun v => v*t) hfirst, congrArg (fun v => v*s) hsecond]
  have hy : (c*t-s*d)*y=0 := by
    nlinarith [congrArg (fun v => v*d) hfirst, congrArg (fun v => v*c) hsecond]
  exact ⟨(mul_eq_zero.mp hx).resolve_left hdet, (mul_eq_zero.mp hy).resolve_left hdet⟩

end
end FrameAdmissiblePoint
