import Mathlib.Tactic

namespace Week04Sections

/-- Taking positive moments counterclockwise about an arbitrary centre (x,y).
    u is the component of the diagonal force along either positive axis on
    the left free body. BC and GF are positive in tension. -/
def left (p x y bc u gf : ℝ) : Prop :=
  bc+u+gf=0 ∧ u-p=0 ∧ x*p+y*bc+(4-x+y)*u+(2+y)*gf=0

def right (dx dy ex x y bc u gf : ℝ) : Prop :=
  dx+ex-bc-u-gf=0 ∧ dy-u=0 ∧
  y*dx+(6-x)*dy+(2+y)*ex-y*bc-(4-x+y)*u-(2+y)*gf=0

theorem reactions (p dx dy ex : ℝ) (hx : dx+ex=0) (hy : dy-p=0)
    (hD : 6*p+2*ex=0) : dx=3*p ∧ dy=p ∧ ex= -3*p :=
  ⟨by linarith, by linarith, by linarith⟩

theorem left_solution (p x y bc u gf : ℝ) :
    left p x y bc u gf ↔ bc=p ∧ u=p ∧ gf= -2*p := by
  constructor
  · rintro ⟨hx,hy,hm⟩
    have hbc : bc=p := by linear_combination ((2+y)*hx+(2-x)*hy-hm)/2
    exact ⟨hbc,by linarith,by linarith⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact ⟨by ring,by ring,by ring⟩

theorem opposite_body (p x y bc u gf : ℝ) :
    right (3*p) p (-3*p) x y bc u gf ↔ left p x y bc u gf := by
  unfold right left
  constructor <;> rintro ⟨hx,hy,hm⟩ <;> exact ⟨by linarith,by linarith,by linear_combination -hm⟩

theorem diagonal_force (p force : ℝ) (h : force / Real.sqrt 2=p) :
    force=p*Real.sqrt 2 := (div_eq_iff (by positivity)).mp h

end Week04Sections
