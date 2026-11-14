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

/-- Degree aliases change the normal's sign, never its constraint kernel. -/
theorem degree_alias_kernel (angle canonical x y : ℝ) (turns : ℤ)
    (halias : angle = canonical + 180 * turns) :
    normalWork (ExactGeometry.degreeCos angle) (ExactGeometry.degreeSin angle) x y = 0 ↔
    normalWork (ExactGeometry.degreeCos canonical) (ExactGeometry.degreeSin canonical) x y = 0 := by
  have hangle : angle * (Real.pi / 180) = canonical * (Real.pi / 180) + turns * Real.pi := by
    rw [halias]
    ring
  have hfactor : (-1 : ℝ)^turns ≠ 0 := zpow_ne_zero _ (by norm_num)
  unfold ExactGeometry.degreeCos ExactGeometry.degreeSin normalWork
  rw [hangle, Real.cos_add_int_mul_pi, Real.sin_add_int_mul_pi]
  rw [show (-1 : ℝ)^turns * Real.cos (canonical * (Real.pi/180)) * x +
      (-1 : ℝ)^turns * Real.sin (canonical * (Real.pi/180)) * y =
      (-1 : ℝ)^turns * (Real.cos (canonical * (Real.pi/180))*x +
      Real.sin (canonical * (Real.pi/180))*y) by ring]
  simp [hfactor]

/-- Distinct exact canonical angles constrain both translations, without a
    numerical near-parallel threshold. The resulting problem may still be ill-conditioned. -/
theorem canonical_normals_independent {a b : ℝ}
    (ha : 0 ≤ a ∧ a < 180) (hb : 0 ≤ b ∧ b < 180) (hne : a ≠ b) :
    ExactGeometry.degreeCos a * ExactGeometry.degreeSin b -
      ExactGeometry.degreeSin a * ExactGeometry.degreeCos b ≠ 0 := by
  have hp : 0 < Real.pi/180 := div_pos Real.pi_pos (by norm_num)
  have hscale : 180*(Real.pi/180) = Real.pi := by ring
  have hlo : -Real.pi < (b-a)*(Real.pi/180) := by
    have h := mul_lt_mul_of_pos_right (show (-180 : ℝ) < b-a by linarith [ha.2, hb.1]) hp
    nlinarith
  have hhi : (b-a)*(Real.pi/180) < Real.pi := by
    have h := mul_lt_mul_of_pos_right (show b-a < (180 : ℝ) by linarith [hb.2, ha.1]) hp
    nlinarith
  have harg : (b-a)*(Real.pi/180) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hne.symm) (ne_of_gt hp)
  have hsin : Real.sin ((b-a)*(Real.pi/180)) ≠ 0 := by
    intro hz
    exact harg ((Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp hz)
  have hdet : ExactGeometry.degreeCos a * ExactGeometry.degreeSin b -
      ExactGeometry.degreeSin a * ExactGeometry.degreeCos b = Real.sin ((b-a)*(Real.pi/180)) := by
    unfold ExactGeometry.degreeCos ExactGeometry.degreeSin
    rw [sub_mul, Real.sin_sub]
    ring
  rw [hdet]
  exact hsin

/-- Every source row remains quantified, including redundant support entries.
    Exact alias witnesses transfer their kernels to their canonical classes. -/
theorem all_alias_kernels {ι : Type*} (angles canonical : ι → ℝ) (turns : ι → ℤ)
    (halias : ∀ i, angles i = canonical i + 180 * turns i) (x y : ℝ) :
    (∀ i, normalWork (ExactGeometry.degreeCos (angles i))
      (ExactGeometry.degreeSin (angles i)) x y = 0) ↔
    (∀ i, normalWork (ExactGeometry.degreeCos (canonical i))
      (ExactGeometry.degreeSin (canonical i)) x y = 0) := by
  constructor
  · intro h i
    exact (degree_alias_kernel _ _ x y (turns i) (halias i)).mp (h i)
  · intro h i
    exact (degree_alias_kernel _ _ x y (turns i) (halias i)).mpr (h i)

/-- A nonempty family of aliased roller rows has precisely one free tangent
    coordinate. This statement retains all rows rather than selecting one and
    assuming the remainder are redundant. -/
theorem all_single_class_kernel {ι : Type*} [Nonempty ι]
    (angles : ι → ℝ) (canonical : ℝ) (turns : ι → ℤ)
    (halias : ∀ i, angles i = canonical + 180 * turns i) (x y : ℝ) :
    (∀ i, normalWork (ExactGeometry.degreeCos (angles i))
      (ExactGeometry.degreeSin (angles i)) x y = 0) ↔
    ∃ alpha, x = -ExactGeometry.degreeSin canonical * alpha ∧
      y = ExactGeometry.degreeCos canonical * alpha := by
  rw [all_alias_kernels angles (fun _ => canonical) turns halias]
  constructor
  · intro h
    let i : ι := Classical.choice inferInstance
    exact ⟨tangentCoordinate (ExactGeometry.degreeCos canonical)
      (ExactGeometry.degreeSin canonical) x y,
      single_normal_kernel (ExactGeometry.degree_axis_normalized canonical) (h i)⟩
  · rintro ⟨alpha, hx, hy⟩ i
    rw [hx, hy]
    exact tangent_admissible _ _ alpha

/-- If two retained source classes are distinct, the entire family's kernel
    is zero in translation. No numerical rank decision enters the argument. -/
theorem all_distinct_classes_kernel {ι : Type*}
    (angles canonical : ι → ℝ) (turns : ι → ℤ)
    (halias : ∀ i, angles i = canonical i + 180 * turns i)
    (first second : ι)
    (hfirst : 0 ≤ canonical first ∧ canonical first < 180)
    (hsecond : 0 ≤ canonical second ∧ canonical second < 180)
    (hdistinct : canonical first ≠ canonical second) (x y : ℝ) :
    (∀ i, normalWork (ExactGeometry.degreeCos (angles i))
      (ExactGeometry.degreeSin (angles i)) x y = 0) ↔ x = 0 ∧ y = 0 := by
  rw [all_alias_kernels angles canonical turns halias]
  constructor
  · intro h
    exact two_normals_kernel (h first) (h second)
      (canonical_normals_independent hfirst hsecond hdistinct)
  · rintro ⟨rfl, rfl⟩ i
    simp [normalWork]

end
end FrameAdmissiblePoint
