import FrameIntervalLoad
import FrameEnclosure

/-! The affine-load enclosure refers to the established real consistent load,
    including both endpoint moments for sign-changing intensities. -/
namespace FrameIntervalLoadSound
open FrameIntervalLoad FrameEnclosure
noncomputable section

theorem scaledPair_contains {bits : Nat} {scale left right out : FrameIntervalOps.Bounds}
    {a b denominator : Rat} {L x y : ℝ}
    (h : scaledPair bits scale left right a b denominator = some out)
    (hscale : Contains scale L) (hleft : Contains left x) (hright : Contains right y) :
    Contains out (L * ((a : ℝ)*x + (b : ℝ)*y) / (denominator : ℝ)) := by
  simp only [scaledPair, Option.bind_eq_bind, Option.bind_eq_some] at h
  obtain ⟨leftWeight, ha, rightWeight, hb, divisor, hd, weightedLeft, hwl,
    weightedRight, hwr, combined, hc, numerator, hn, hout⟩ := h
  exact executable_divide_contains hout
    (executable_multiply_contains hn hscale
      (executable_add_contains hc
        (executable_multiply_contains hwl (executable_point_contains ha) hleft)
        (executable_multiply_contains hwr (executable_point_contains hb) hright)))
    (executable_point_contains hd)

theorem consistentLoad_contains {bits : Nat}
    {length axialLeft axialRight transverseLeft transverseRight : FrameIntervalOps.Bounds}
    {out : Fin 6 → FrameIntervalOps.Bounds} {L p₀ p₁ q₀ q₁ : ℝ}
    (h : consistentLoad bits length axialLeft axialRight transverseLeft transverseRight = some out)
    (hL : Contains length L) (hp₀ : Contains axialLeft p₀) (hp₁ : Contains axialRight p₁)
    (hq₀ : Contains transverseLeft q₀) (hq₁ : Contains transverseRight q₁) :
    ∀ i, Contains (out i) (LocalFrameFields.consistentLoad L p₀ p₁ q₀ q₁ i) := by
  simp only [consistentLoad, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
  obtain ⟨squared, hsquared, axialStart, has, shearStart, hss, momentStart, hms,
    axialEnd, hae, shearEnd, hse, momentEnd, hme, hout⟩ := h
  subst out
  have hL2 : Contains squared (L^2) := by
    simpa only [pow_two] using executable_multiply_contains hsquared hL hL
  have ha := scaledPair_contains has hL hp₀ hp₁
  have hb := scaledPair_contains hss hL hq₀ hq₁
  have hc := scaledPair_contains hms hL2 hq₀ hq₁
  have hd := scaledPair_contains hae hL hp₀ hp₁
  have he := scaledPair_contains hse hL hq₀ hq₁
  have hf := scaledPair_contains hme hL2 hq₀ hq₁
  norm_num at ha hb hc hd he hf
  have hf' : Contains momentEnd (-L^2 * (2*q₀+3*q₁)/60) := by
    convert hf using 1 <;> ring
  intro i
  fin_cases i
  · simpa [LocalFrameFields.consistentLoad] using ha
  · simpa [LocalFrameFields.consistentLoad] using hb
  · simpa [LocalFrameFields.consistentLoad] using hc
  · simpa [LocalFrameFields.consistentLoad] using hd
  · simpa [LocalFrameFields.consistentLoad] using he
  · simpa [LocalFrameFields.consistentLoad] using hf'

end
end FrameIntervalLoadSound
