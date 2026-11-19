import MemberDiagram
import RationalFrameSoundness
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace MemberDiagram.Sound
open RationalFrame
noncomputable section

def val (r : Radical) : ℝ := r.a + r.b * Real.sqrt r.d
def contains (b : Box) (z : ℝ) := (b.lo : ℝ) ≤ z ∧ z ≤ b.hi
def field (f : Cubic) (x : ℝ) : ℝ := f.f0 + x*(f.f1 + x*(f.f2 + x*f.f3))

theorem sqrt_checked {d : Rat} {b : Box} (h : sqrtBox d = some b) :
    0 ≤ (d : ℝ) ∧ contains b (Real.sqrt d) := by
  simp only [sqrtBox] at h
  split at h
  next ok =>
    obtain ⟨hl, lower, hu, upper⟩ := ok
    cases h
    have hd : 0 ≤ d := le_trans (mul_self_nonneg _) lower
    refine ⟨by exact_mod_cast hd, ?_, ?_⟩
    · apply Real.le_sqrt_of_sq_le
      rw [pow_two]
      exact_mod_cast lower
    · apply (Real.sqrt_le_iff).2
      constructor
      · exact_mod_cast hu
      · rw [pow_two]
        exact_mod_cast upper
  next => cases h

theorem enclosure_checked {r : Radical} {b : Box} (h : enclosure r = some b) :
    0 ≤ (r.d : ℝ) ∧ contains b (val r) := by
  unfold enclosure at h
  obtain ⟨s, hs, rest⟩ := Option.bind_eq_some.mp h
  obtain ⟨hd, hl, hu⟩ := sqrt_checked hs
  change (if (scaledBox r s).hi - (scaledBox r s).lo ≤ _ then some (scaledBox r s) else none) = some b at rest
  split at rest
  next =>
    cases rest
    refine ⟨hd, ?_⟩
    by_cases sign : r.b < 0
    · have neg : (r.b : ℝ) ≤ 0 := by exact_mod_cast le_of_lt sign
      simpa [contains, val, scaledBox, sign] using
        And.intro (add_le_add_left (mul_le_mul_of_nonpos_left hu neg) (r.a : ℝ))
          (add_le_add_left (mul_le_mul_of_nonpos_left hl neg) (r.a : ℝ))
    · have pos : 0 ≤ (r.b : ℝ) := by exact_mod_cast le_of_not_gt sign
      simpa [contains, val, scaledBox, sign] using
        And.intro (add_le_add_left (mul_le_mul_of_nonneg_left hl pos) (r.a : ℝ))
          (add_le_add_left (mul_le_mul_of_nonneg_left hu pos) (r.a : ℝ))
  next => cases rest

theorem horner_checked (x y : Radical) (c : Rat) (hd : 0 ≤ (x.d : ℝ)) (same : y.d = x.d) :
    val (hornerStep x y c) = c + val x * val y := by
  simp [val, hornerStep, same]
  linear_combination - (x.b : ℝ) * (y.b : ℝ) * Real.sq_sqrt hd
  
theorem evaluation_checked (f : Cubic) (x : Radical) (hd : 0 ≤ (x.d : ℝ)) :
    val (evaluate f x) = field f (val x) := by
  unfold evaluate
  rw [horner_checked x (hornerStep x (hornerStep x ⟨f.f3, 0, x.d⟩ f.f2) f.f1) f.f0 hd rfl,
      horner_checked x (hornerStep x ⟨f.f3, 0, x.d⟩ f.f2) f.f1 hd rfl,
      horner_checked x ⟨f.f3, 0, x.d⟩ f.f2 hd rfl]
  simp [val, field]

theorem equality_checked {x y : Radical} (hx : 0 ≤ (x.d : ℝ)) (hy : 0 ≤ (y.d : ℝ))
    (h : sameValue x y = true) : val x = val y := by
  obtain ⟨ha, hs, sign⟩ := of_decide_eq_true h
  have squares : ((x.b : ℝ) * Real.sqrt x.d)^2 = ((y.b : ℝ) * Real.sqrt y.d)^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy, pow_two, pow_two]
    exact_mod_cast hs
  unfold val
  rw [ha]
  congr 1
  rcases sign with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hp' : 0 ≤ (x.b : ℝ) * Real.sqrt x.d := mul_nonneg (by exact_mod_cast hp) (Real.sqrt_nonneg _)
    have hq' : 0 ≤ (y.b : ℝ) * Real.sqrt y.d := mul_nonneg (by exact_mod_cast hq) (Real.sqrt_nonneg _)
    nlinarith
  · have hp' : (x.b : ℝ) * Real.sqrt x.d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hp) (Real.sqrt_nonneg _)
    have hq' : (y.b : ℝ) * Real.sqrt y.d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hq) (Real.sqrt_nonneg _)
    nlinarith

/-- These are the physical element fields for every real coordinate, including
irrational extrema. All coefficients come from the source-owned end actions. -/
theorem source_fields (s : Segment) (motion : Array Rat) (x : ℝ)
    (hL : (s.length : ℝ) ≠ 0) (hEA : (s.EA : ℝ) ≠ 0) (hEI : (s.EI : ℝ) ≠ 0) :
    let d := fun i => (localMotion s motion i : ℝ)
    let q := (s.cosine : ℝ) * s.vertical
    let qEnd := (s.cosine : ℝ) * s.verticalEnd
    field (polynomial s motion false) x = (LocalFrameFields.shear d s.length s.EI q qEnd).eval x ∧
    field (polynomial s motion true) x = (LocalFrameFields.moment d s.length s.EI q qEnd).eval x := by
  have fields := Fields.affine_recovery (fun i => (localMotion s motion i : ℝ)) s.length s.EA s.EI
    (s.sine*s.vertical : Rat) (s.sine*s.verticalEnd : Rat) (s.cosine*s.vertical : Rat) (s.cosine*s.verticalEnd : Rat) x hL hEA hEI
  have actions := Recovery.end_action_cast s motion hL hEA hEI
  push_cast at fields actions
  obtain ⟨_, shear, moment, _⟩ := fields
  dsimp only
  rw [shear, moment]
  simp only [← actions]
  simp [field, polynomial]
  constructor <;> ring

/-- Every nonconstant cubic has only the endpoints and the real roots of its
derivative to consider. The same assertion applies to minima and maxima. -/
theorem stationary_condition (f : Cubic) (x : ℝ)
    (extreme : IsLocalMax (field f) x ∨ IsLocalMin (field f) x) :
    (3*(f.f3 : ℝ))*x^2 + (2*(f.f2 : ℝ))*x + f.f1 = 0 := by
  have deriv : HasDerivAt (field f) ((3*(f.f3 : ℝ))*x^2 + (2*(f.f2 : ℝ))*x + f.f1) x := by
    unfold field
    have inner := (hasDerivAt_id x).mul_const (f.f3 : ℝ)
    have middle := (hasDerivAt_id x).mul (inner.const_add (f.f2 : ℝ))
    have outer := ((hasDerivAt_id x).mul (middle.const_add (f.f1 : ℝ))).const_add (f.f0 : ℝ)
    convert outer using 1 <;> simp [id] <;> ring
  rcases extreme with hm | hm
  · exact hm.hasDerivAt_eq_zero deriv
  · exact hm.hasDerivAt_eq_zero deriv

#print axioms source_fields
#print axioms evaluation_checked
#print axioms stationary_condition
end
end MemberDiagram.Sound
