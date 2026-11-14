import ExactGeometry
import Mathlib.Data.Real.Pi.Bounds
import FrameIntervalOps

/-! Real containment obligations for rational interval certificates. Candidate
    arithmetic is untrusted. These lemmas do not yet certify a frame solution. -/
namespace FrameEnclosure
noncomputable section

abbrev Bounds := FrameIntervalOps.Bounds

theorem power_eq_pow (value : Rat) (exponent : Nat) : FrameIntervalOps.power value exponent = value^exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp [FrameIntervalOps.power, pow_succ, ih]

theorem lowerOf_eq_min (a b : Rat) : FrameIntervalOps.lowerOf a b = min a b := by
  by_cases h : a ≤ b
  · simp only [FrameIntervalOps.lowerOf, if_pos h, min_eq_left h]
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge h)
    simp only [FrameIntervalOps.lowerOf, if_neg h, min_eq_right hba]

theorem upperOf_eq_max (a b : Rat) : FrameIntervalOps.upperOf a b = max a b := by
  by_cases h : a ≤ b
  · simp only [FrameIntervalOps.upperOf, if_pos h, max_eq_right h]
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge h)
    simp only [FrameIntervalOps.upperOf, if_neg h, max_eq_left hba]

def Contains (bounds : Bounds) (value : ℝ) : Prop :=
  (bounds.lower : ℝ) ≤ value ∧ value ≤ (bounds.upper : ℝ)

theorem outward_post {bits : Nat} {lower upper : Rat} {out : Bounds}
    (h : FrameIntervalOps.outward bits lower upper = some out) :
    out.lower ≤ lower ∧ upper ≤ out.upper := by
  unfold FrameIntervalOps.outward at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    next checks =>
      -- Preserve the checked inequalities before identifying the returned bounds.
      have endpoints := checks
      simp only [Bool.and_eq_true, decide_eq_true_eq] at endpoints
      have outputEquality := Option.some.inj h
      subst out
      exact ⟨endpoints.1.2, endpoints.2⟩
    next rejected => simp only [Option.none_eq_some] at h

theorem widen {a b : Bounds} {x : ℝ} (hx : Contains a x)
    (hl : (b.lower : ℝ) ≤ a.lower) (hu : (a.upper : ℝ) ≤ b.upper) :
    Contains b x := ⟨le_trans hl hx.1, le_trans hx.2 hu⟩

theorem add_contains {a b out : Bounds} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y)
    (hl : (out.lower : ℝ) ≤ (a.lower : ℝ) + b.lower)
    (hu : (a.upper : ℝ) + b.upper ≤ (out.upper : ℝ)) : Contains out (x + y) := by
  constructor <;> dsimp [Contains] at * <;> linarith

theorem subtract_contains {a b out : Bounds} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y)
    (hl : (out.lower : ℝ) ≤ (a.lower : ℝ) - b.upper)
    (hu : (a.upper : ℝ) - b.lower ≤ (out.upper : ℝ)) : Contains out (x - y) := by
  constructor <;> dsimp [Contains] at * <;> linarith

theorem product_upper {al au bl bu x y upper : ℝ}
    (hx : al ≤ x ∧ x ≤ au) (hy : bl ≤ y ∧ y ≤ bu)
    (hll : al * bl ≤ upper) (hlu : al * bu ≤ upper)
    (hul : au * bl ≤ upper) (huu : au * bu ≤ upper) : x * y ≤ upper := by
  rcases le_total 0 y with hypos | hyneg
  · have hfirst := mul_le_mul_of_nonneg_right hx.2 hypos
    rcases le_total 0 au with hpos | hneg
    · exact le_trans hfirst (le_trans (mul_le_mul_of_nonneg_left hy.2 hpos) huu)
    · exact le_trans hfirst (le_trans (mul_le_mul_of_nonpos_left hy.1 hneg) hul)
  · have hfirst := mul_le_mul_of_nonpos_right hx.1 hyneg
    rcases le_total 0 al with hpos | hneg
    · exact le_trans hfirst (le_trans (mul_le_mul_of_nonneg_left hy.2 hpos) hlu)
    · exact le_trans hfirst (le_trans (mul_le_mul_of_nonpos_left hy.1 hneg) hll)

theorem product_lower {al au bl bu x y lower : ℝ}
    (hx : al ≤ x ∧ x ≤ au) (hy : bl ≤ y ∧ y ≤ bu)
    (hll : lower ≤ al * bl) (hlu : lower ≤ al * bu)
    (hul : lower ≤ au * bl) (huu : lower ≤ au * bu) : lower ≤ x * y := by
  have h := product_upper (x := -x) (y := y) (al := -au) (au := -al)
    (upper := -lower) (by constructor <;> linarith) hy
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  nlinarith

/-- Squared rational endpoint comparisons establish containment of the actual
    nonnegative real root, including an irrational member length. -/
theorem sqrt_contains {a out : Bounds} {x : ℝ}
    (hx : Contains a x) (ha : 0 ≤ (a.lower : ℝ))
    (hl : 0 ≤ (out.lower : ℝ)) (hu : 0 ≤ (out.upper : ℝ))
    (hlower : (out.lower : ℝ)^2 ≤ (a.lower : ℝ))
    (hupper : (a.upper : ℝ) ≤ (out.upper : ℝ)^2) :
    Contains out (Real.sqrt x) := by
  have hxnonneg : 0 ≤ x := le_trans ha hx.1
  have hroot := Real.sqrt_nonneg x
  have hsquare := Real.sq_sqrt hxnonneg
  constructor <;> dsimp [Contains] at * <;> nlinarith

/-- A candidate midpoint is an estimate; the interval establishes its error. -/
theorem midpoint_error {a : Bounds} {x : ℝ} (hx : Contains a x) :
    |x - ((a.lower : ℝ) + a.upper) / 2| ≤ ((a.upper : ℝ) - a.lower) / 2 := by
  apply abs_le.mpr
  constructor <;> dsimp [Contains] at * <;> linarith

theorem pi_contains : Contains
    ⟨314159265358979323846 / 100000000000000000000,
      314159265358979323847 / 100000000000000000000⟩ Real.pi := by
  constructor
  · convert (le_of_lt Real.pi_gt_d20) using 1 <;> norm_num
  · convert (le_of_lt Real.pi_lt_d20) using 1 <;> norm_num

/-- The same fourth-order remainder applies to both small-angle polynomials.
    Repeated exact double-angle identities then cover the reduced degree angle. -/
theorem small_angle_error {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x^3 / 6)| ≤ |x|^4 * (5 / 96) ∧
    |Real.cos x - (1 - x^2 / 2)| ≤ |x|^4 * (5 / 96) :=
  ⟨Real.sin_bound hx, Real.cos_bound hx⟩

/-- This gate bounds error relative to the unknown true value, including zero.
    Absolute tolerances and result units are supplied by the fixed protocol. -/
theorem accuracy_gate {mid radius absolute relative x : ℝ}
    (herror : |x - mid| ≤ radius) (hr : 0 ≤ relative)
    (hgate : radius ≤ absolute + relative * max 0 (|mid| - radius)) :
    |x - mid| ≤ absolute + relative * |x| := by
  have htriangle : |mid| ≤ |x| + |x - mid| := by
    have h := abs_add x (mid - x)
    rw [abs_sub_comm mid x] at h
    simpa using h
  have hlower : max 0 (|mid| - radius) ≤ |x| := by
    apply max_le (abs_nonneg x)
    linarith
  exact le_trans herror (le_trans hgate (add_le_add_left (mul_le_mul_of_nonneg_left hlower hr) absolute))

theorem executable_add_contains {bits : Nat} {a b out : Bounds} {x y : ℝ}
    (h : FrameIntervalOps.add bits a b = some out)
    (hx : Contains a x) (hy : Contains b y) : Contains out (x+y) := by
  unfold FrameIntervalOps.add at h
  split at h
  · have hp := outward_post h
    apply add_contains hx hy
    · exact_mod_cast hp.1
    · exact_mod_cast hp.2
  · simp at h

theorem executable_subtract_contains {bits : Nat} {a b out : Bounds} {x y : ℝ}
    (h : FrameIntervalOps.subtract bits a b = some out)
    (hx : Contains a x) (hy : Contains b y) : Contains out (x-y) := by
  unfold FrameIntervalOps.subtract at h
  split at h
  · have hp := outward_post h
    apply subtract_contains hx hy
    · exact_mod_cast hp.1
    · exact_mod_cast hp.2
  · simp at h

theorem executable_point_contains {bits : Nat} {value : Rat} {out : Bounds}
    (h : FrameIntervalOps.point bits value = some out) : Contains out (value : ℝ) := by
  have hp := outward_post h
  constructor
  · exact_mod_cast hp.1
  · exact_mod_cast hp.2

theorem executable_negate_contains {bits : Nat} {a out : Bounds} {x : ℝ}
    (h : FrameIntervalOps.negate bits a = some out)
    (hx : Contains a x) : Contains out (-x) := by
  unfold FrameIntervalOps.negate at h
  split at h
  · have hp := outward_post h
    have hl : (out.lower : ℝ) ≤ -(a.upper : ℝ) := by exact_mod_cast hp.1
    have hu : -(a.lower : ℝ) ≤ (out.upper : ℝ) := by exact_mod_cast hp.2
    constructor <;> dsimp [Contains] at * <;> linarith
  · simp at h

/-- Four corner products suffice even when either input crosses zero. -/
theorem executable_multiply_contains {bits : Nat} {a b out : Bounds} {x y : ℝ}
    (h : FrameIntervalOps.multiply bits a b = some out)
    (hx : Contains a x) (hy : Contains b y) : Contains out (x*y) := by
  unfold FrameIntervalOps.multiply at h
  split at h
  · have hp := outward_post h
    simp only [lowerOf_eq_min, upperOf_eq_max] at hp
    have hll := le_trans hp.1 (le_trans (min_le_left _ _) (min_le_left _ _))
    have hlu := le_trans hp.1 (le_trans (min_le_left _ _) (min_le_right _ _))
    have hul := le_trans hp.1 (le_trans (min_le_right _ _) (min_le_left _ _))
    have huu := le_trans hp.1 (le_trans (min_le_right _ _) (min_le_right _ _))
    have ull := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hp.2
    have ulu := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hp.2
    have uul := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hp.2
    have uuu := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hp.2
    constructor
    · apply product_lower hx hy
      · exact_mod_cast hll
      · exact_mod_cast hlu
      · exact_mod_cast hul
      · exact_mod_cast huu
    · apply product_upper hx hy
      · exact_mod_cast ull
      · exact_mod_cast ulu
      · exact_mod_cast uul
      · exact_mod_cast uuu
  · simp at h

theorem executable_sqrt_contains {a witness out : Bounds} {x : ℝ}
    (h : FrameIntervalOps.squareRoot a witness = some out)
    (hx : Contains a x) : Contains out (Real.sqrt x) := by
  unfold FrameIntervalOps.squareRoot at h
  split at h
  next checks =>
    have hc : FrameIntervalOps.valid a = true ∧ FrameIntervalOps.valid witness = true ∧
        0 ≤ a.lower ∧ 0 ≤ witness.lower ∧
        witness.lower*witness.lower ≤ a.lower ∧ a.upper ≤ witness.upper*witness.upper := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checks
    have heq : witness = out := Option.some.inj h
    subst out
    have hordered : witness.lower ≤ witness.upper := by
      have hv := hc.2.1
      simp only [FrameIntervalOps.valid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hv
      exact hv.1
    apply sqrt_contains hx
    · exact_mod_cast hc.2.2.1
    · exact_mod_cast hc.2.2.2.1
    · exact_mod_cast le_trans hc.2.2.2.1 hordered
    · have hl := hc.2.2.2.2.1
      exact_mod_cast (show witness.lower^2 ≤ a.lower by nlinarith [hl])
    · have hu := hc.2.2.2.2.2
      exact_mod_cast (show a.upper ≤ witness.upper^2 by nlinarith [hu])
  · simp at h

private theorem reciprocal_positive_order {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : 1/b ≤ 1/a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  apply (div_le_div_iff₀ hb ha).mpr
  simpa using hab

theorem reciprocal_contains {a out : Bounds} {x : ℝ}
    (hx : Contains a x) (hsign : 0 < (a.lower : ℝ) ∨ (a.upper : ℝ) < 0)
    (hl : (out.lower : ℝ) ≤ 1/(a.upper : ℝ))
    (hu : 1/(a.lower : ℝ) ≤ (out.upper : ℝ)) : Contains out (1/x) := by
  have hinner : 1/(a.upper : ℝ) ≤ 1/x ∧ 1/x ≤ 1/(a.lower : ℝ) := by
    rcases hsign with hpositive | hnegative
    · exact ⟨reciprocal_positive_order (lt_of_lt_of_le hpositive hx.1) hx.2,
        reciprocal_positive_order hpositive hx.1⟩
    · have hxnegative : x < 0 := lt_of_le_of_lt hx.2 hnegative
      have hfirst := reciprocal_positive_order (neg_pos.mpr hnegative) (neg_le_neg hx.2)
      have hsecond := reciprocal_positive_order (neg_pos.mpr hxnegative) (neg_le_neg hx.1)
      constructor
      · simpa only [div_neg, neg_le_neg_iff] using hfirst
      · simpa only [div_neg, neg_le_neg_iff] using hsecond
  exact ⟨le_trans hl hinner.1, le_trans hinner.2 hu⟩

theorem executable_reciprocal_contains {bits : Nat} {a out : Bounds} {x : ℝ}
    (h : FrameIntervalOps.reciprocal bits a = some out)
    (hx : Contains a x) : Contains out (1/x) := by
  unfold FrameIntervalOps.reciprocal at h
  split at h
  next checks =>
    have hc : FrameIntervalOps.valid a = true ∧ (0 < a.lower ∨ a.upper < 0) := by
      simpa only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] using checks
    have hp := outward_post h
    apply reciprocal_contains hx
    · exact_mod_cast hc.2
    · exact_mod_cast hp.1
    · exact_mod_cast hp.2
  · simp at h

theorem executable_divide_contains {bits : Nat} {a b out : Bounds} {x y : ℝ}
    (h : FrameIntervalOps.divide bits a b = some out)
    (hx : Contains a x) (hy : Contains b y) : Contains out (x/y) := by
  unfold FrameIntervalOps.divide at h
  cases hinverse : FrameIntervalOps.reciprocal bits b with
  | none => simp [hinverse] at h
  | some inverse =>
    have hmultiply : FrameIntervalOps.multiply bits a inverse = some out := by
      simpa [hinverse] using h
    have hbound := executable_multiply_contains hmultiply hx (executable_reciprocal_contains hinverse hy)
    simpa [div_eq_mul_inv] using hbound

end
end FrameEnclosure
