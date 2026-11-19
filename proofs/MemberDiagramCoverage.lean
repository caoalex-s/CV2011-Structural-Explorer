import MemberDiagramExtrema

namespace MemberDiagram.Sound
open RationalFrame Set
noncomputable section

def represents (f : Cubic) (origin : Rat) (r : Candidate) (x : ℝ) :=
  contains r.x ((origin : ℝ) + x) ∧ val r.exactY = field f x

def rowValid (f : Cubic) (o len : Rat) (r : Candidate) :=
  0 ≤ (r.exactY.d : ℝ) ∧ contains r.y (val r.exactY) ∧
    ∃ x ∈ Icc (0:ℝ) len, represents f o r x

theorem candidate_valid {f p side o x row} {len : Rat} (h : candidate f p side o x = some row)
    (domain : val x ∈ Icc (0:ℝ) len) :
    rowValid f o len row ∧ represents f o row (val x) := by
  obtain ⟨loc, img, eq, hd⟩ := row_enclosed h
  exact ⟨⟨hd, eq.symm ▸ img, val x, domain, loc, eq⟩, loc, eq⟩

theorem interior_valid {f p o len r z} (done : rootCandidate f p o len r = some (some z)) :
    rowValid f o len z := by
  obtain ⟨box,hb,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨_, lo, hi⟩ := enclosure_checked hb
  split at rest
  next => cases rest
  next =>
    split at rest
    next domain =>
      obtain ⟨v,hv,eq⟩ := Option.bind_eq_some.mp rest
      cases eq
      have left : (0:ℝ) < box.lo := by exact_mod_cast domain.1
      have right : (box.hi : ℝ) < len := by exact_mod_cast domain.2
      exact (candidate_valid hv ⟨by linarith, by linarith⟩).1
    next => cases rest

theorem flat_field {f : Cubic} (h : flat f = true) (x : ℝ) : field f x = f.f0 := by
  simp only [flat, Bool.and_eq_true, beq_iff_eq] at h
  simp [field, h.1.1, h.1.2, h.2]

/-- Every listed value is attained. Conversely, every endpoint or stationary
point is represented at its actual position, including all points of a plateau. -/
theorem piece_complete {f p o len rows} (ok : candidates f p o len = some rows) :
    0 < len ∧ (∀ r ∈ rows, rowValid f o len r) ∧
    ∀ x ∈ Icc (0:ℝ) len, (x = 0 ∨ x = len ∨
      3*(f.f3 : ℝ)*x^2 + 2*(f.f2 : ℝ)*x + f.f1 = 0) →
      ∃ r ∈ rows, represents f o r x := by
  unfold candidates at ok
  by_cases lenPos : 0 < len
  · rw [if_pos lenPos] at ok
    obtain ⟨left,hl,rest⟩ := Option.bind_eq_some.mp ok
    obtain ⟨right,hr,ok⟩ := Option.bind_eq_some.mp rest
    have hL : (0:ℝ) < len := by exact_mod_cast lenPos
    have zero : val (rational 0) = 0 := by simp [val,rational]
    have length : val (rational len) = len := by simp [val,rational]
    obtain ⟨vl, rl⟩ := candidate_valid hl (len := len) (by rw [zero]; exact ⟨le_rfl,hL.le⟩)
    obtain ⟨vr, rr⟩ := candidate_valid hr (len := len) (by rw [length]; exact ⟨hL.le,le_rfl⟩)
    rw [zero] at rl
    rw [length] at rr
    by_cases hf : flat f = true
    · simp [hf] at ok
      subst rows
      let plateau : Candidate := {left with side := "flat", x := ⟨o,o+len⟩}
      have covers (x : ℝ) (hx : x ∈ Icc (0:ℝ) len) : represents f o plateau x := by
        refine ⟨⟨by dsimp [plateau]; linarith [hx.1], by dsimp [plateau]; push_cast; linarith [hx.2]⟩, ?_⟩
        exact rl.2.trans ((flat_field hf 0).trans (flat_field hf x).symm)
      have vp : rowValid f o len plateau := ⟨vl.1,vl.2.1,0,⟨le_rfl,hL.le⟩,covers 0 ⟨le_rfl,hL.le⟩⟩
      exact ⟨lenPos, by simpa [plateau] using And.intro vl (And.intro vp vr),
        fun x hx _ => ⟨plateau, by simp [plateau], covers x hx⟩⟩
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at ok
      obtain ⟨middle,hm,eq⟩ := Option.bind_eq_some.mp ok
      cases eq
      obtain ⟨all, only⟩ := collected hm
      refine ⟨lenPos, ?_, ?_⟩
      · intro r hr'
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hr'
        rcases hr' with rfl | h | rfl
        · exact vl
        · obtain ⟨root, _, hroot⟩ := only r h
          exact interior_valid hroot
        · exact vr
      · intro x hx hc
        by_cases hz : x = 0
        · exact ⟨left, by simp, hz ▸ rl⟩
        by_cases he : x = len
        · exact ⟨right, by simp, he ▸ rr⟩
        have deriv := (hc.resolve_left hz).resolve_left he
        obtain ⟨root,listed,hxroot⟩ := nonflat_root (Bool.eq_false_iff.mpr hf) deriv
        obtain ⟨out,ho,retained⟩ := all root listed
        have interior : 0 < val root ∧ val root < (len:ℝ) := by
          rw [hxroot]; exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hz),lt_of_le_of_ne hx.2 he⟩
        obtain ⟨r,rfl,hit⟩ := kept interior ho
        have mem := retained r (by simp)
        exact ⟨r,by simp [mem],hxroot ▸ (candidate_valid hit (len := len) (hxroot.symm ▸ hx)).2⟩
  · simp [lenPos] at ok

end
end MemberDiagram.Sound
