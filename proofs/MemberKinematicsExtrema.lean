import MemberKinematicsSound

namespace MemberKinematics.Sound
open FrameEnclosure (Contains)
open FrameIntervalOps Set
noncomputable section

abbrev RealInputs := Fin 15 → ℝ

def functionAt (inputs : RealInputs) (length : ℝ) (expr : FrameIntervalExpression.Expression 15) (t : ℝ) :=
  FrameIntervalExpressionSound.evaluate (atStation inputs length t) expr

/-- A candidate need not enclose a stationary point. Its range must enclose
at least one physical value, which gives the inner bound on each extremum. -/
theorem stationary_witness {bits p f inputs length} (fits : Fits p inputs length)
    (fuel : Nat) {budget t result} (ordered : t.lower ≤ t.upper)
    (done : stationary bits p f t fuel budget = some result) {r} (member : r ∈ result.1) :
    ∃ x, Contains t x ∧ Contains r.value (functionAt inputs length (quantity f) x) := by
  induction fuel generalizing budget t result with
  | zero => cases done
  | succ n ih =>
    cases budget with
    | zero => cases done
    | succ b =>
      obtain ⟨cell,hc,rest⟩ := Option.bind_eq_some.mp done
      cases cell with
      | excluded => cases rest; simp at member
      | enclosing row =>
        cases rest
        simp only [List.mem_singleton] at member
        subst r
        have h := candidate_fits fits (classified_enclosure hc)
        have whereAt : Contains t (t.lower:ℝ) := ⟨le_rfl,by exact_mod_cast ordered⟩
        exact ⟨_,whereAt,h.2 _ (h.1 ▸ whereAt)⟩
      | subdivide =>
        obtain ⟨⟨left,remaining⟩,hl,rest⟩ := Option.bind_eq_some.mp rest
        obtain ⟨⟨right,_⟩,hr,rest⟩ := Option.bind_eq_some.mp rest
        cases rest
        let mid := (t.lower+t.upper)/2
        have first : t.lower ≤ mid := by dsimp [mid]; linarith
        have last : mid ≤ t.upper := by dsimp [mid]; linarith
        rcases List.mem_append.mp member with a | a
        · obtain ⟨x,hx,hv⟩ := ih first hl a
          exact ⟨x,⟨hx.1,hx.2.trans (by exact_mod_cast last)⟩,hv⟩
        · obtain ⟨x,hx,hv⟩ := ih last hr a
          exact ⟨x,⟨le_trans (by exact_mod_cast first) hx.1,hx.2⟩,hv⟩

theorem candidates_cover {bits p f inputs length rows} (fits : Fits p inputs length)
    (done : candidates bits p f = some rows) {t : ℝ} (domain : t ∈ Icc 0 1)
    (critical : t = 0 ∨ t = 1 ∨ functionAt inputs length (derivativeSign f) t = 0) :
    ∃ r ∈ rows, Contains r.t t ∧ Contains r.value (functionAt inputs length (quantity f) t) := by
  obtain ⟨a,ha,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨b,hb,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨⟨interior,_⟩,hi,rest⟩ := Option.bind_eq_some.mp rest
  cases rest
  rcases critical with rfl | rfl | zero
  · obtain ⟨eq,h⟩ := candidate_fits fits ha
    have loc : Contains a.t 0 := by rw [eq]; norm_num [Contains]
    exact ⟨a,by simp,loc,h _ loc⟩
  · obtain ⟨eq,h⟩ := candidate_fits fits hb
    have loc : Contains b.t 1 := by rw [eq]; norm_num [Contains]
    exact ⟨b,by simp,loc,h _ loc⟩
  · obtain ⟨r,mem,loc,val⟩ := stationary_covered fits _ (by simpa [Contains] using domain) zero hi
    exact ⟨r,by simp [mem],loc,val⟩

theorem candidates_witness {bits p f inputs length rows} (fits : Fits p inputs length)
    (done : candidates bits p f = some rows) {r} (member : r ∈ rows) :
    ∃ x ∈ Icc (0:ℝ) 1, Contains r.value (functionAt inputs length (quantity f) x) := by
  obtain ⟨a,ha,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨b,hb,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨⟨interior,_⟩,hi,rest⟩ := Option.bind_eq_some.mp rest
  cases rest
  rcases List.mem_cons.mp member with rfl | other
  · obtain ⟨eq,h⟩ := candidate_fits fits ha
    exact ⟨0,by simp,h _ (by rw [eq]; norm_num [Contains])⟩
  rcases List.mem_cons.mp other with rfl | inner
  · obtain ⟨eq,h⟩ := candidate_fits fits hb
    exact ⟨1,by simp,h _ (by rw [eq]; norm_num [Contains])⟩
  obtain ⟨x,domain,val⟩ := stationary_witness fits _ (by decide) hi inner
  exact ⟨x,by simpa [Contains] using domain,val⟩

theorem summary_checks {rows e} (made : summarize rows = some e) : soundLimits rows e := by
  cases rows with
  | nil => cases made
  | cons a tail =>
    unfold summarize at made
    dsimp only at made
    split at made
    next ok =>
      cases made
      simp only [Bool.and_eq_true,decide_eq_true_eq] at ok
      exact ok.1.1
    next => cases made

/-- The outer and inner candidate bounds apply to attained global extrema.
This argument also covers equal extrema on distinct pieces and flat fields. -/
theorem extrema_enclosed {rows e} (made : summarize rows = some e)
    {attained : ℝ → Prop} {minimum maximum : ℝ}
    (minLe : ∀ y, attained y → minimum ≤ y) (leMax : ∀ y, attained y → y ≤ maximum)
    (witness : ∀ r ∈ rows, ∃ y, attained y ∧ Contains r.value y)
    (minRow : ∃ r ∈ rows, Contains r.value minimum) (maxRow : ∃ r ∈ rows, Contains r.value maximum) :
    Contains e.minimum minimum ∧ Contains e.maximum maximum := by
  obtain ⟨outer,⟨lo,hlo,low⟩,⟨hi,hhi,high⟩⟩ := summary_checks made
  obtain ⟨a,ha,ca⟩ := minRow
  obtain ⟨b,hb,cb⟩ := maxRow
  obtain ⟨x,ax,cx⟩ := witness lo hlo
  obtain ⟨y,ay,cy⟩ := witness hi hhi
  refine ⟨⟨le_trans ?_ ca.1,(minLe x ax).trans (cx.2.trans ?_)⟩,
    ⟨le_trans ?_ (cy.1.trans (leMax y ay)),cb.2.trans ?_⟩⟩
  · exact_mod_cast (outer a ha).1
  · exact_mod_cast low
  · exact_mod_cast high
  · exact_mod_cast (outer b hb).2

#print axioms candidates_cover
#print axioms candidates_witness
#print axioms extrema_enclosed
end
end MemberKinematics.Sound
