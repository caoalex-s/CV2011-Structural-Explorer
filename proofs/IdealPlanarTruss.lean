import Mathlib.Tactic

namespace IdealPlanarTruss

/-- All eight joint equilibrium equations, with each bar force positive in tension.
    The direction cosines of AC are (4/5, 3/5). -/
def balanced (P Ax Ay By AB BC CD DA AC : ℚ) : Prop :=
  Ax + AB + 4/5*AC = 0 ∧ Ay + DA + 3/5*AC = 0 ∧
  -AB = 0 ∧ By + BC = 0 ∧
  P - CD - 4/5*AC = 0 ∧ -BC - 3/5*AC = 0 ∧
  CD = 0 ∧ -DA = 0

theorem rectangle_equilibrium (P Ax Ay By AB BC CD DA AC : ℚ) :
    balanced P Ax Ay By AB BC CD DA AC ↔
    Ax = -P ∧ Ay = -3*P/4 ∧ By = 3*P/4 ∧ AB = 0 ∧ BC = -3*P/4 ∧
    CD = 0 ∧ DA = 0 ∧ AC = 5*P/4 := by
  unfold balanced
  constructor <;> rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ <;> repeat' constructor <;> linarith

/-- Horizontal joint velocities at the top of the unbraced rectangle are equal.
    Pin A and vertical restraint B have already eliminated three coordinates. -/
def perimeterMotion (Bx Cx Cy Dx Dy : ℚ) : Prop :=
  Bx = 0 ∧ Cy = 0 ∧ Cx = Dx ∧ Dy = 0

theorem unbraced_motion (Bx Cx Cy Dx Dy : ℚ) :
    perimeterMotion Bx Cx Cy Dx Dy ↔
    ∃ t : ℚ, Bx = 0 ∧ Cx = t ∧ Cy = 0 ∧ Dx = t ∧ Dy = 0 := by
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨Cx,h1,rfl,h2,h3.symm,h4⟩
  · rintro ⟨t,h1,h2,h3,h4,h5⟩
    exact ⟨h1,h3,h2.trans h4.symm,h5⟩

theorem braced_motion (Bx Cx Cy Dx Dy : ℚ) (h : perimeterMotion Bx Cx Cy Dx Dy)
    (diagonal : 4*Cx + 3*Cy = 0) :
    Bx = 0 ∧ Cx = 0 ∧ Cy = 0 ∧ Dx = 0 ∧ Dy = 0 := by
  obtain ⟨h1,h2,h3,h4⟩ := h
  repeat' constructor <;> linarith

theorem horizontal_roller_motion (By Cx Cy Dx Dy : ℚ) :
    (Cy = By ∧ Cx = Dx ∧ Dy = 0 ∧ 4*Cx + 3*Cy = 0) ↔
    ∃ θ : ℚ, By = 4*θ ∧ Cx = -3*θ ∧ Cy = 4*θ ∧ Dx = -3*θ ∧ Dy = 0 := by
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨By/4, by ring, by linarith, by linarith, by linarith, h3⟩
  · rintro ⟨θ,h1,h2,h3,h4,h5⟩
    repeat' constructor <;> linarith

theorem unbraced_incompatible (P Ax Ay By AB BC CD DA : ℚ)
    (h : balanced P Ax Ay By AB BC CD DA 0) : P = 0 := by
  have hh := (rectangle_equilibrium P Ax Ay By AB BC CD DA 0).mp h
  obtain ⟨_,_,_,_,_,_,_,h8⟩ := hh
  linarith

theorem horizontal_roller_incompatible (P Bx Ax Ay AB BC CD DA AC : ℚ)
    (hA : Ax + AB + 4/5*AC = 0) (hAy : Ay + DA + 3/5*AC = 0)
    (hB : Bx-AB = 0) (hBy : BC = 0)
    (hCx : P-CD-4/5*AC = 0) (hCy : -BC-3/5*AC = 0)
    (hDx : CD = 0) (hDy : DA = 0) : P = 0 := by
  linarith

end IdealPlanarTruss

