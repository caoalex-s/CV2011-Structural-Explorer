import FrameIntervalTrig
import FrameEnclosure

/-! Containment through the executable double-angle recurrence. Initial
    small-angle bounds and source degree reduction are separate obligations. -/
namespace FrameIntervalTrigSound
open FrameIntervalOps FrameIntervalTrig FrameEnclosure
noncomputable section

def ContainsAxes (axes : Axes) (angle : ℝ) : Prop :=
  Contains axes.sine (Real.sin angle) ∧ Contains axes.cosine (Real.cos angle)

private theorem fourth_power_bound {x magnitude : ℝ}
    (h : |x| ≤ magnitude) : |x|^4 ≤ magnitude^4 := by
  have hm : 0 ≤ magnitude := le_trans (abs_nonneg x) h
  have hsquare : |x|^2 ≤ magnitude^2 := by nlinarith [abs_nonneg x]
  have hproduct := mul_nonneg (sub_nonneg.mpr hsquare)
    (add_nonneg (sq_nonneg magnitude) (sq_nonneg |x|))
  nlinarith

private theorem remainder_contains {bits : Nat} {magnitude : Rat} {out : Bounds} {error : ℝ}
    (h : outward bits (-(5*magnitude^4/96)) (5*magnitude^4/96) = some out)
    (he : |error| ≤ 5*(magnitude : ℝ)^4/96) : Contains out error := by
  have hp := outward_post h
  have hl : (out.lower : ℝ) ≤ -(5*(magnitude : ℝ)^4/96) := by exact_mod_cast hp.1
  have hu : 5*(magnitude : ℝ)^4/96 ≤ (out.upper : ℝ) := by exact_mod_cast hp.2
  exact ⟨le_trans hl (abs_le.mp he).1, le_trans (abs_le.mp he).2 hu⟩

theorem smallAngle_contains {bits : Nat} {angle outSine outCosine : Bounds} {x : ℝ}
    (h : smallAngle bits angle = some ⟨outSine, outCosine⟩)
    (hx : Contains angle x) : ContainsAxes ⟨outSine, outCosine⟩ x := by
  unfold smallAngle at h
  split at h
  · simp at h
  next checks =>
    have hlimit : max (-angle.lower) angle.upper ≤ (1 : Rat) := by
      by_contra hn
      have hgt : max (-angle.lower) angle.upper > (1 : Rat) := lt_of_not_ge hn
      simp [hgt] at checks
    have hmag : |x| ≤ (max (-angle.lower) angle.upper : Rat) := by
      apply abs_le.mpr
      have hl : (-(angle.lower : ℝ)) ≤ (max (-angle.lower) angle.upper : Rat) := by
        exact_mod_cast (le_max_left (-angle.lower) angle.upper)
      have hu : (angle.upper : ℝ) ≤ (max (-angle.lower) angle.upper : Rat) := by
        exact_mod_cast (le_max_right (-angle.lower) angle.upper)
      constructor <;> dsimp [Contains] at * <;> linarith
    have hxsmall : |x| ≤ 1 := le_trans hmag (by exact_mod_cast hlimit)
    have hfourth := fourth_power_bound hmag
    have herrors := small_angle_error hxsmall
    simp only [bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
    obtain ⟨squared, hsquared, cubed, hcubed, six, hsix, two, htwo, one, hone,
      remainder, hremainder, cubicTerm, hcubicTerm, sinePolynomial, hsinePolynomial,
      sine, hsine, squareTerm, hsquareTerm, cosinePolynomial, hcosinePolynomial,
      cosine, hcosine, hout⟩ := h
    have hsquareContains := executable_multiply_contains hsquared hx hx
    have hcubeContains := executable_multiply_contains hcubed hsquareContains hx
    have hsixContains : Contains six (6 : ℝ) := by simpa using executable_point_contains hsix
    have htwoContains : Contains two (2 : ℝ) := by simpa using executable_point_contains htwo
    have honeContains : Contains one (1 : ℝ) := by simpa using executable_point_contains hone
    have hsinePoly := executable_subtract_contains hsinePolynomial hx
      (executable_divide_contains hcubicTerm hcubeContains hsixContains)
    have hcosinePoly := executable_subtract_contains hcosinePolynomial honeContains
      (executable_divide_contains hsquareTerm hsquareContains htwoContains)
    have hsineError := remainder_contains hremainder
      (show |Real.sin x - (x-x^3/6)| ≤ 5*((max (-angle.lower) angle.upper : Rat) : ℝ)^4/96 by
        nlinarith [herrors.1])
    have hcosineError := remainder_contains hremainder
      (show |Real.cos x - (1-x^2/2)| ≤ 5*((max (-angle.lower) angle.upper : Rat) : ℝ)^4/96 by
        nlinarith [herrors.2])
    have hsineBound := executable_add_contains hsine hsinePoly hsineError
    have hcosineBound := executable_add_contains hcosine hcosinePoly hcosineError
    have hsineIdentity : (x-x*x*x/6) + (Real.sin x-(x-x^3/6)) = Real.sin x := by ring
    have hcosineIdentity : (1-x*x/2) + (Real.cos x-(1-x^2/2)) = Real.cos x := by ring
    rw [hsineIdentity] at hsineBound
    rw [hcosineIdentity] at hcosineBound
    have hsineEq : sine = outSine := congrArg Axes.sine hout
    have hcosineEq : cosine = outCosine := congrArg Axes.cosine hout
    simpa [hsineEq, hcosineEq] using And.intro hsineBound hcosineBound

theorem doubleAngle_contains {bits : Nat} {axes out : Axes} {angle : ℝ}
    (h : doubleAngle bits axes = some out) (haxes : ContainsAxes axes angle) :
    ContainsAxes out (2*angle) := by
  simp only [doubleAngle, bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
  obtain ⟨two, htwo, product, hproduct, sine, hsine, cosineSquared, hcosineSquared,
    sineSquared, hsineSquared, cosine, hcosine, hout⟩ := h
  subst out
  have htwoContains : Contains two (2 : ℝ) := by
    simpa using executable_point_contains htwo
  have hproductContains := executable_multiply_contains hproduct haxes.1 haxes.2
  have hsineContains := executable_multiply_contains hsine htwoContains hproductContains
  have hcosineContains := executable_subtract_contains hcosine
    (executable_multiply_contains hcosineSquared haxes.2 haxes.2)
    (executable_multiply_contains hsineSquared haxes.1 haxes.1)
  constructor
  · simpa [Real.sin_two_mul, mul_assoc] using hsineContains
  · simpa only [two_mul, Real.cos_add] using hcosineContains

theorem doubleAngles_contains {bits count : Nat} {axes out : Axes} {angle : ℝ}
    (h : doubleAngles bits count axes = some out) (haxes : ContainsAxes axes angle) :
    ContainsAxes out ((2 : ℝ)^count * angle) := by
  induction count generalizing axes out angle with
  | zero =>
    have heq : axes = out := Option.some.inj h
    subst out
    simpa using haxes
  | succ count ih =>
    obtain ⟨doubled, hdoubled, hremaining⟩ := Option.bind_eq_some.mp h
    have hresult := ih hremaining (doubleAngle_contains hdoubled haxes)
    simpa [pow_succ, mul_assoc] using hresult

theorem degreeAxesGeneral_contains {bits : Nat} {source reduced : Rat} {turns : Int} {out : Axes}
    (h : degreeAxesGeneral bits source reduced turns = some out) :
    ContainsAxes out ((source : ℝ) * (Real.pi/180)) := by
  unfold degreeAxesGeneral at h
  split at h
  · simp at h
  next checks =>
    have halias : source = reduced + 360 * (turns : Rat) := by
      by_contra hn
      simp [hn] at checks
    simp only [bind_eq_bind, Option.bind_eq_some] at h
    obtain ⟨pi, hpi, degrees, hdegrees, radians, hradians, scale, hscale,
      small, hsmall, axes, haxes, hdouble⟩ := h
    have hpiContains : Contains pi Real.pi := by
      have hp := outward_post hpi
      apply widen pi_contains
      · exact_mod_cast hp.1
      · exact_mod_cast hp.2
    have hdegreesContains : Contains degrees ((reduced : ℝ)/180) := by
      simpa using executable_point_contains hdegrees
    have hradiansContains := executable_multiply_contains hradians hdegreesContains hpiContains
    have hscaleContains : Contains scale ((2 : ℝ)^(bits/4)) := by
      simpa using executable_point_contains hscale
    have hsmallContains := executable_divide_contains hsmall hradiansContains hscaleContains
    have haxesContains : ContainsAxes axes (((reduced : ℝ)/180*Real.pi)/(2 : ℝ)^(bits/4)) := by
      cases axes with
      | mk sine cosine => exact smallAngle_contains haxes hsmallContains
    have hresult := doubleAngles_contains hdouble haxesContains
    have hscaleNonzero : (2 : ℝ)^(bits/4) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hrestore : (2 : ℝ)^(bits/4) * (((reduced : ℝ)/180*Real.pi)/(2 : ℝ)^(bits/4)) =
        (reduced : ℝ)*(Real.pi/180) := by
      field_simp [hscaleNonzero]
      <;> ring
    rw [hrestore] at hresult
    have haliasReal : (source : ℝ) = (reduced : ℝ) + 360 * (turns : ℝ) := by
      exact_mod_cast halias
    have hangle : (source : ℝ)*(Real.pi/180) =
        (reduced : ℝ)*(Real.pi/180) + turns*(2*Real.pi) := by
      rw [haliasReal]
      ring
    rw [hangle]
    simpa [ContainsAxes] using hresult

end
end FrameIntervalTrigSound
