import MemberDiagramSound

namespace MemberDiagram.Sound
open RationalFrame
noncomputable section

/-- Completing the square lists all real roots, with a separate linear
case. Constant fields are treated as entire intervals by the caller. -/
theorem roots_complete (a b c : Rat) (x : ℝ)
    (nonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (zero : (a : ℝ)*x^2 + b*x + c = 0) :
    ∃ r ∈ roots a b c, val r = x := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp_all
    · refine ⟨rational (-c/b), by simp [roots,hb], ?_⟩
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      simp [val,rational]
      field_simp
      linarith
  · have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    let d := b*b-4*a*c
    have dcast : (d : ℝ) = (b : ℝ)*b-4*a*c := by simp [d]
    have sq : (2*(a:ℝ)*x+b)^2 = (d : ℝ) := by rw [dcast]; linear_combination 4*(a : ℝ)*zero
    have hd' : 0 ≤ (d : ℝ) := sq ▸ sq_nonneg _
    have hd : ¬ d < 0 := not_lt.mpr (by exact_mod_cast hd')
    by_cases hz : d = 0
    · refine ⟨rational (-b/(2*a)), by simpa [roots,ha, ← show d = b*b-4*a*c from rfl, hd,hz], ?_⟩
      have s0 : 2*(a:ℝ)*x+b = 0 := by rw [hz] at sq; norm_num at sq; exact sq
      simp [val, rational]
      field_simp
      linarith
    · have sr := Real.sq_sqrt hd'
      have factors : (2*(a:ℝ)*x+b-Real.sqrt d)*(2*(a:ℝ)*x+b+Real.sqrt d)=0 := by
        nlinarith only [sq, sr]
      have list : roots a b c = [⟨-b/(2*a), -1/(2*a), d⟩, ⟨-b/(2*a), 1/(2*a), d⟩] := by
        simp [roots,ha, ← show d = b*b-4*a*c from rfl, hd,hz]
      rcases mul_eq_zero.mp factors with pos | neg
      · refine ⟨⟨-b/(2*a), 1/(2*a), d⟩, by simp [list], ?_⟩
        simp [val]
        field_simp
        linarith
      · refine ⟨⟨-b/(2*a), -1/(2*a), d⟩, by simp [list], ?_⟩
        simp [val]
        field_simp
        linarith

theorem collected {entry : Radical → Option (Option Candidate)} {roots : List Radical} {rows : List Candidate}
    (computed : collectRoots entry roots = some rows) :
    (∀ r ∈ roots, ∃ out, entry r = some out ∧ ∀ z ∈ out.toList, z ∈ rows) ∧
    (∀ z ∈ rows, ∃ r ∈ roots, entry r = some (some z)) := by
  induction roots generalizing rows with
  | nil => simp [collectRoots] at computed; subst rows; simp
  | cons r tail ih =>
    obtain ⟨out, h, rest⟩ := Option.bind_eq_some.mp computed
    obtain ⟨others, ho, result⟩ := Option.bind_eq_some.mp rest
    cases result
    obtain ⟨all, only⟩ := ih ho
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨out,h,fun _ hz => List.mem_append_left _ hz⟩
      · obtain ⟨v, hv, inc⟩ := all x hx
        exact ⟨v,hv,fun z hz => List.mem_append_right _ (inc z hz)⟩
    · intro z hz
      rcases List.mem_append.mp hz with first | later
      · cases out with
        | none => simp at first
        | some w => simp at first; subst w; exact ⟨r, List.mem_cons_self, h⟩
      · obtain ⟨x,hx,hit⟩ := only z later
        exact ⟨x,List.mem_cons_of_mem _ hx,hit⟩

theorem row_enclosed {f p side o x row} (done : candidate f p side o x = some row) :
    contains row.x (o + val x) ∧ contains row.y (field f (val x)) ∧
    val row.exactY = field f (val x) ∧ 0 ≤ (row.exactY.d : ℝ) := by
  obtain ⟨pos, hp, rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨value, hv, eq⟩ := Option.bind_eq_some.mp rest
  cases eq
  obtain ⟨hd, loc⟩ := enclosure_checked hp
  obtain ⟨hdy, image⟩ := enclosure_checked hv
  have computed := evaluation_checked f x hd
  refine ⟨?_, computed ▸ image, computed, hdy⟩
  convert loc using 1 <;> simp [val] <;> ring

theorem nonflat_root {f : Cubic} (h : flat f = false) {x : ℝ}
    (crit : (3*(f.f3 : ℝ))*x^2 + (2*(f.f2 : ℝ))*x + f.f1 = 0) :
    ∃ r ∈ stationary f, val r = x := by
  apply roots_complete
  · by_contra! all
    simp_all [flat]
  · push_cast
    exact crit

/-- The checked choice for an interior critical point cannot discard it. -/
theorem kept {f p o len r out} (inside : 0 < val r ∧ val r < (len : ℝ))
    (done : rootCandidate f p o len r = some out) :
    ∃ z, out = some z ∧ candidate f p "interior" o r = some z := by
  obtain ⟨box,hb,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨_, lo, hi⟩ := enclosure_checked hb
  have h0 : ¬ box.hi ≤ 0 := by exact_mod_cast (show ¬ (box.hi : ℝ) ≤ 0 by linarith [inside.1])
  have hL : ¬ len ≤ box.lo := by exact_mod_cast (show ¬ (len : ℝ) ≤ box.lo by linarith [inside.2])
  simp [h0,hL] at rest
  split at rest
  next => obtain ⟨z,hz,eq⟩ := Option.bind_eq_some.mp rest; cases eq; exact ⟨z,rfl,hz⟩
  next => cases rest

#print axioms roots_complete
end
end MemberDiagram.Sound
