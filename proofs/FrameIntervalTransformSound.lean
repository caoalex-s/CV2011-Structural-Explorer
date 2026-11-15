import FrameIntervalTransform
import FrameEnclosure

/-! Local projection containment for the original member direction. Source
    point-basis correspondence must be established before using this lemma. -/
namespace FrameIntervalTransformSound
open FrameIntervalTransform FrameEnclosure
noncomputable section

theorem localPoint_contains {bits : Nat} {cosine sine : FrameIntervalOps.Bounds}
    {global out : Fin 3 → FrameIntervalOps.Bounds} {c s : ℝ} {actual : Fin 3 → ℝ}
    (h : localPoint bits cosine sine global = some out)
    (hc : Contains cosine c) (hs : Contains sine s)
    (hglobal : ∀ i, Contains (global i) (actual i)) :
    ∀ i, Contains (out i) (![c*actual 0+s*actual 1, -s*actual 0+c*actual 1, actual 2] i) := by
  simp only [localPoint, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
  obtain ⟨cx, hcx, sy, hsy, sx, hsx, cy, hcy, axial, haxial, transverse, htransverse, hout⟩ := h
  subst out
  have ha := executable_add_contains haxial
    (executable_multiply_contains hcx hc (hglobal 0))
    (executable_multiply_contains hsy hs (hglobal 1))
  have ht := executable_subtract_contains htransverse
    (executable_multiply_contains hcy hc (hglobal 1))
    (executable_multiply_contains hsx hs (hglobal 0))
  have transverseIdentity : c*actual 1-s*actual 0 = -s*actual 0+c*actual 1 := by ring
  rw [transverseIdentity] at ht
  intro i
  fin_cases i
  · simpa using ha
  · simpa using ht
  · simpa using hglobal 2

theorem localPiece_contains {bits : Nat} {cosine sine : FrameIntervalOps.Bounds}
    {start finish : Fin 3 → FrameIntervalOps.Bounds} {out : Fin 6 → FrameIntervalOps.Bounds}
    {c s : ℝ} {first second : Fin 3 → ℝ}
    (h : localPiece bits cosine sine start finish = some out)
    (hc : Contains cosine c) (hs : Contains sine s)
    (hfirst : ∀ i, Contains (start i) (first i))
    (hsecond : ∀ i, Contains (finish i) (second i)) :
    ∀ i, Contains (out i) (FrameTransform.toLocal6 c s
      ![first 0, first 1, first 2, second 0, second 1, second 2] i) := by
  simp only [localPiece, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
  obtain ⟨startLocal, hstart, endLocal, hend, hout⟩ := h
  subst out
  have ha := localPoint_contains hstart hc hs hfirst
  have hb := localPoint_contains hend hc hs hsecond
  intro i
  fin_cases i
  · simpa [FrameTransform.toLocal6] using ha 0
  · simpa [FrameTransform.toLocal6] using ha 1
  · simpa [FrameTransform.toLocal6] using ha 2
  · simpa [FrameTransform.toLocal6] using hb 0
  · simpa [FrameTransform.toLocal6] using hb 1
  · simpa [FrameTransform.toLocal6] using hb 2

end
end FrameIntervalTransformSound
