import FrameReuse

/-!
Generic exact interval and affine-load facts for the member-cut adapter.
The partition retains original member ownership and is independent of the
floating engine's snapping. Polynomial work uses the same physical field on
every interval; it does not identify independent child endpoint movements.
-/
open Polynomial MeasureTheory intervalIntegral
open FrameInterfaces FrameTransform FrameAssemblyModel FrameVirtualWork

namespace MemberCutAdapter
noncomputable section

/-- Ordered, positive consecutive intervals on one original member. -/
inductive IntervalChain : ℝ → ℝ → List (ℝ × ℝ) → Prop where
  | single {a b} : a < b → IntervalChain a b [(a, b)]
  | step {a b c tail} : a < b → IntervalChain b c tail → IntervalChain a c ((a, b) :: tail)

theorem chain_endpoints_ordered {a b : ℝ} {pieces : List (ℝ × ℝ)}
    (h : IntervalChain a b pieces) : a < b := by
  induction h with
  | single hab => exact hab
  | step hab _ ih => exact lt_trans hab ih

theorem chain_interval_bounds {a b : ℝ} {pieces : List (ℝ × ℝ)}
    (h : IntervalChain a b pieces) (piece : ℝ × ℝ) (hp : piece ∈ pieces) :
    a ≤ piece.1 ∧ piece.1 < piece.2 ∧ piece.2 ≤ b := by
  induction h with
  | single hab =>
    simp only [List.mem_singleton] at hp
    subst piece
    exact ⟨le_rfl, hab, le_rfl⟩
  | @step a c b tail hac htail ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨le_rfl, hac, le_of_lt (chain_endpoints_ordered htail)⟩
    · obtain ⟨hcl, hlr, hrb⟩ := ih hp
      exact ⟨le_trans (le_of_lt hac) hcl, hlr, hrb⟩

/-- Every point of the span lies in one of the closed consecutive intervals. -/
theorem chain_coverage {a b : ℝ} {pieces : List (ℝ × ℝ)}
    (h : IntervalChain a b pieces) (x : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    ∃ piece ∈ pieces, piece.1 ≤ x ∧ x ≤ piece.2 := by
  induction h with
  | @single a b hab => exact ⟨(a, b), by simp, ha, hb⟩
  | @step a c b tail hac htail ih =>
    by_cases hx : x ≤ c
    · exact ⟨(a, c), by simp, ha, hx⟩
    · obtain ⟨piece, hp, hl, hr⟩ := ih (le_of_not_ge hx) hb
      exact ⟨piece, by simp [hp], hl, hr⟩

/-- Earlier intervals finish no later than any later interval begins. -/
theorem chain_disjoint_interiors {a b : ℝ} {pieces : List (ℝ × ℝ)}
    (h : IntervalChain a b pieces) : pieces.Pairwise (fun left right => left.2 ≤ right.1) := by
  induction h with
  | single hab => simp
  | @step a c b tail hac htail ih =>
    simp only [List.pairwise_cons]
    refine ⟨?_, ih⟩
    intro piece hp
    exact (chain_interval_bounds htail piece hp).1

/-- Endpoint interpolation in the original member parameter. -/
def affine (a b qa qb t : ℝ) : ℝ := qa + (qb - qa) * (t - a) / (b - a)

def pullback (u v z : ℝ) : ℝ := u + (v-u)*z

def intervalAffine (q₀ q₁ z : ℝ) : ℝ := q₀ + (q₁-q₀)*z

/-- The endpoints of a restricted affine load determine its value at every
point of the same pulled-back physical interval. -/
theorem affine_restriction (a b qa qb u v z : ℝ) (_hab : a ≠ b) :
    intervalAffine (affine a b qa qb u) (affine a b qa qb v) z =
      affine a b qa qb (pullback u v z) := by
  unfold intervalAffine affine pullback
  field_simp
  ring

/-- Restricting an already restricted affine load agrees with direct restriction. -/
theorem successive_restriction (a b qa qb u v r s z : ℝ) (hab : a ≠ b) (huv : u ≠ v) :
    intervalAffine (affine u v (affine a b qa qb u) (affine a b qa qb v) r)
      (affine u v (affine a b qa qb u) (affine a b qa qb v) s) z =
    affine a b qa qb (pullback r s z) := by
  unfold intervalAffine affine pullback
  field_simp [sub_ne_zero.mpr (Ne.symm hab), sub_ne_zero.mpr (Ne.symm huv)]
  ring

/-- Restriction commutes with summing affine source contributions. -/
theorem overlap_restriction (ι : Type) [Fintype ι] (a b qa qb : ι → ℝ)
    (u v z : ℝ) (h : ∀ i, a i ≠ b i) :
    (∑ i, intervalAffine (affine (a i) (b i) (qa i) (qb i) u)
      (affine (a i) (b i) (qa i) (qb i) v) z) =
    ∑ i, affine (a i) (b i) (qa i) (qb i) (pullback u v z) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact affine_restriction _ _ _ _ _ _ _ (h i)

/-- Global vertical resultant, using intensity per unit member length. -/
def resultant (L a b qa qb : ℝ) : ℝ := L * (b-a) * (qa+qb) / 2

/-- First moment about the original member start, with arc coordinate x=L*t. -/
def firstMoment (L a b qa qb : ℝ) : ℝ :=
  L^2 * (a*(b-a)*(qa+qb)/2 + (b-a)^2*(qa+2*qb)/6)

theorem resultant_split (L a b qa qb m : ℝ) (hab : a ≠ b) :
    resultant L a b qa qb = resultant L a m qa (affine a b qa qb m) +
      resultant L m b (affine a b qa qb m) qb := by
  unfold resultant affine
  field_simp [sub_ne_zero.mpr (Ne.symm hab)]
  ring

theorem first_moment_split (L a b qa qb m : ℝ) (hab : a ≠ b) :
    firstMoment L a b qa qb = firstMoment L a m qa (affine a b qa qb m) +
      firstMoment L m b (affine a b qa qb m) qb := by
  unfold firstMoment affine
  field_simp [sub_ne_zero.mpr (Ne.symm hab)]
  ring

/-- The exact Jacobian is L*(v-u), and the same polynomial physical field is
pulled back to each interval. This covers linear and cubic virtual fields. -/
theorem polynomial_work_restriction (p : Polynomial ℝ) (L u v : ℝ) :
    L * (∫ t in u..v, p.eval t) =
      L * (v-u) * (∫ z in (0:ℝ)..1, p.eval (pullback u v z)) := by
  have h := intervalIntegral.smul_integral_comp_add_mul (fun t : ℝ => p.eval t) (a := (0:ℝ)) (b := 1) (v-u) u
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one] at h
  have huv : u + (v-u) = v := by ring
  rw [huv] at h
  rw [← h]
  unfold pullback
  ring

/-- Work on an elementary interval from the sum of its active affine
sources. The endpoints are those emitted by restriction; the same original
polynomial virtual field is evaluated at the pulled-back coordinate. Source
containment is explicit, so this statement does not justify extrapolation. -/
theorem overlap_interval_work (ι : Type) [Fintype ι] (a b qa qb : ι → ℝ)
    (u v L : ℝ) (p virtualField : Polynomial ℝ)
    (_huv : u < v) (hsource : ∀ i, a i < b i)
    (_hcontained : ∀ i, a i ≤ u ∧ v ≤ b i)
    (hdensity : ∀ t, p.eval t = (∑ i, affine (a i) (b i) (qa i) (qb i) t) * virtualField.eval t) :
    L * (∫ t in u..v, p.eval t) =
      L * (v-u) * (∫ z in (0:ℝ)..1,
        intervalAffine (∑ i, affine (a i) (b i) (qa i) (qb i) u)
          (∑ i, affine (a i) (b i) (qa i) (qb i) v) z *
          virtualField.eval (pullback u v z)) := by
  rw [polynomial_work_restriction p L u v]
  congr 2
  funext z
  rw [hdensity]
  congr 1
  rw [← overlap_restriction ι a b qa qb u v z (fun i => ne_of_lt (hsource i))]
  simp [intervalAffine, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]

/-- The statement applies simultaneously to any finite family of elementary
intervals, with each interval carrying its own active source parameters. -/
theorem overlap_finite_interval_work (κ ι : Type) [Fintype κ] [Fintype ι]
    (a b qa qb : κ → ι → ℝ) (u v : κ → ℝ) (L : ℝ)
    (p : κ → Polynomial ℝ) (virtualField : Polynomial ℝ)
    (huv : ∀ k, u k < v k) (hsource : ∀ k i, a k i < b k i)
    (hcontained : ∀ k i, a k i ≤ u k ∧ v k ≤ b k i)
    (hdensity : ∀ k t, (p k).eval t =
      (∑ i, affine (a k i) (b k i) (qa k i) (qb k i) t) * virtualField.eval t) :
    (∑ k, L * (∫ t in u k..v k, (p k).eval t)) =
      ∑ k, L * (v k-u k) * (∫ z in (0:ℝ)..1,
        intervalAffine (∑ i, affine (a k i) (b k i) (qa k i) (qb k i) (u k))
          (∑ i, affine (a k i) (b k i) (qa k i) (qb k i) (v k)) z *
          virtualField.eval (pullback (u k) (v k) z)) := by
  apply Finset.sum_congr rfl
  intro k hk
  exact overlap_interval_work ι (a k) (b k) (qa k) (qb k) (u k) (v k) L
    (p k) virtualField (huv k) (hsource k) (hcontained k) (hdensity k)

/-- The existing exact consistent-load theorem applies to each local pair of
rotated vertical-load endpoints and retains the physical segment length. -/
theorem local_vertical_consistent_work (d : LocalDofs) (L c s q₀ q₁ : ℝ) :
    L * (∫ z in (0:ℝ)..1, (loadDensity d L (s*q₀) (s*q₁) (c*q₀) (c*q₁)).eval z) =
      ∑ i : Fin 6, LocalFrameFields.consistentLoad L (s*q₀) (s*q₁) (c*q₀) (c*q₁) i * d i := by
  exact consistent_load_virtual_work d L (s*q₀) (s*q₁) (c*q₀) (c*q₁)

/-- When the pulled-back source density is the actual rotated local load
density, its work is the existing consistent-load vector work. -/
theorem overlap_rotated_consistent_work (ι : Type) [Fintype ι] (a b qa qb : ι → ℝ)
    (d : LocalDofs) (L c s q₀ q₁ : ℝ) (virtualField : Polynomial ℝ)
    (hsource : ∀ i, a i < b i) (hcontained : ∀ i, a i ≤ 0 ∧ (1:ℝ) ≤ b i)
    (hdensity : ∀ t, (loadDensity d L (s*q₀) (s*q₁) (c*q₀) (c*q₁)).eval t =
      (∑ i, affine (a i) (b i) (qa i) (qb i) t) * virtualField.eval t) :
    (∑ i : Fin 6, LocalFrameFields.consistentLoad L (s*q₀) (s*q₁) (c*q₀) (c*q₁) i * d i) =
      L * (1-0) * (∫ z in (0:ℝ)..1,
        intervalAffine (∑ i, affine (a i) (b i) (qa i) (qb i) 0)
          (∑ i, affine (a i) (b i) (qa i) (qb i) 1) z * virtualField.eval (pullback 0 1 z)) := by
  rw [← local_vertical_consistent_work]
  exact overlap_interval_work ι a b qa qb 0 1 L _ virtualField (by norm_num) hsource hcontained hdensity

/-- A global vertical load uses the member-side axial and transverse signs. -/
theorem vertical_rotation (c s q : ℝ) :
    toLocal c s (![0, q, 0] : Triple) = ![s*q, c*q, 0] := by
  exact global_vertical_components c s q


/-- Restricting through an intermediate original-coordinate interval has the
same value at every original parameter. -/
theorem affine_restriction_in_original_coordinate (a b qa qb u v t : ℝ)
    (hab : a ≠ b) (huv : u ≠ v) :
    affine u v (affine a b qa qb u) (affine a b qa qb v) t = affine a b qa qb t := by
  unfold affine
  field_simp [sub_ne_zero.mpr (Ne.symm hab), sub_ne_zero.mpr (Ne.symm huv)]
  ring

theorem resultant_restricted_split (L a b qa qb u m v : ℝ) (hab : a ≠ b) (huv : u ≠ v) :
    resultant L u v (affine a b qa qb u) (affine a b qa qb v) =
      resultant L u m (affine a b qa qb u) (affine a b qa qb m) +
      resultant L m v (affine a b qa qb m) (affine a b qa qb v) := by
  have hm := affine_restriction_in_original_coordinate a b qa qb u v m hab huv
  rw [← hm]
  exact resultant_split L u v _ _ m huv

theorem first_moment_restricted_split (L a b qa qb u m v : ℝ) (hab : a ≠ b) (huv : u ≠ v) :
    firstMoment L u v (affine a b qa qb u) (affine a b qa qb v) =
      firstMoment L u m (affine a b qa qb u) (affine a b qa qb m) +
      firstMoment L m v (affine a b qa qb m) (affine a b qa qb v) := by
  have hm := affine_restriction_in_original_coordinate a b qa qb u v m hab huv
  rw [← hm]
  exact first_moment_split L u v _ _ m huv

/-- The same polynomial load-work density is integrated on each child span. -/
def chainWork (p : Polynomial ℝ) (L : ℝ) (pieces : List (ℝ × ℝ)) : ℝ :=
  (pieces.map fun piece => L * (∫ t in piece.1..piece.2, p.eval t)).sum

theorem chain_polynomial_work {a b : ℝ} {pieces : List (ℝ × ℝ)}
    (h : IntervalChain a b pieces) (p : Polynomial ℝ) (L : ℝ) :
    chainWork p L pieces = L * (∫ t in a..b, p.eval t) := by
  induction h with
  | single hab => simp [chainWork]
  | @step a c b tail hac htail ih =>
    simp only [chainWork, List.map_cons, List.sum_cons]
    change L * (∫ t in a..c, p.eval t) + chainWork p L tail = _
    rw [ih]
    have hjoin := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (p.continuous.intervalIntegrable a c) (p.continuous.intervalIntegrable c b)
    rw [← hjoin]
    ring

/-- Finite source contributions preserve their combined work on the same
physical field when each contribution is restricted to the chain. -/
theorem chain_polynomial_work_sum {a b : ℝ} {pieces : List (ℝ × ℝ)}
    (h : IntervalChain a b pieces) (ι : Type) [Fintype ι]
    (p : ι → Polynomial ℝ) (L : ℝ) :
    (∑ i, chainWork (p i) L pieces) = ∑ i, L * (∫ t in a..b, (p i).eval t) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact chain_polynomial_work h (p i) L

/-- The chain work for one physical field equals the actual local consistent
load work. This does not identify independent child endpoint DOFs. -/
theorem consistent_load_chain_work {pieces : List (ℝ × ℝ)} (h : IntervalChain 0 1 pieces)
    (d : LocalDofs) (L p₀ p₁ q₀ q₁ : ℝ) :
    chainWork (loadDensity d L p₀ p₁ q₀ q₁) L pieces =
      ∑ i : Fin 6, LocalFrameFields.consistentLoad L p₀ p₁ q₀ q₁ i * d i := by
  rw [chain_polynomial_work h]
  exact consistent_load_virtual_work d L p₀ p₁ q₀ q₁


/-- Sum exact source resultants over the ordered target intervals. -/
def chainResultant (L A B qa qb : ℝ) (pieces : List (ℝ × ℝ)) : ℝ :=
  (pieces.map fun piece => resultant L piece.1 piece.2 (affine A B qa qb piece.1) (affine A B qa qb piece.2)).sum

def chainFirstMoment (L A B qa qb : ℝ) (pieces : List (ℝ × ℝ)) : ℝ :=
  (pieces.map fun piece => firstMoment L piece.1 piece.2 (affine A B qa qb piece.1) (affine A B qa qb piece.2)).sum

theorem chain_resultant {a b : ℝ} {pieces : List (ℝ × ℝ)} (h : IntervalChain a b pieces)
    (L A B qa qb : ℝ) (hAB : A ≠ B) :
    chainResultant L A B qa qb pieces = resultant L a b (affine A B qa qb a) (affine A B qa qb b) := by
  induction h with
  | single hab => simp [chainResultant]
  | @step a c b tail hac htail ih =>
    simp only [chainResultant, List.map_cons, List.sum_cons]
    change resultant L a c (affine A B qa qb a) (affine A B qa qb c) + chainResultant L A B qa qb tail = _
    rw [ih]
    exact (resultant_restricted_split L A B qa qb a c b hAB (ne_of_lt (lt_trans hac (chain_endpoints_ordered htail)))).symm

theorem chain_first_moment {a b : ℝ} {pieces : List (ℝ × ℝ)} (h : IntervalChain a b pieces)
    (L A B qa qb : ℝ) (hAB : A ≠ B) :
    chainFirstMoment L A B qa qb pieces = firstMoment L a b (affine A B qa qb a) (affine A B qa qb b) := by
  induction h with
  | single hab => simp [chainFirstMoment]
  | @step a c b tail hac htail ih =>
    simp only [chainFirstMoment, List.map_cons, List.sum_cons]
    change firstMoment L a c (affine A B qa qb a) (affine A B qa qb c) + chainFirstMoment L A B qa qb tail = _
    rw [ih]
    exact (first_moment_restricted_split L A B qa qb a c b hAB (ne_of_lt (lt_trans hac (chain_endpoints_ordered htail)))).symm

end
end MemberCutAdapter
