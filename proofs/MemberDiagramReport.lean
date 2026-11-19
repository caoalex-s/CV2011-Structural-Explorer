import MemberDiagramCoverage

namespace MemberDiagram.Sound
open RationalFrame Set
noncomputable section

/-- Each inequality used in the printed table has either separated rational
bounds or an equality witness shared by both comparison directions. -/
theorem comparison {r s : Candidate}
    (hr : contains r.y (val r.exactY)) (hs : contains s.y (val s.exactY))
    (dr : 0 ≤ (r.exactY.d : ℝ)) (ds : 0 ≤ (s.exactY.d : ℝ))
    (ordered : lessEqual r s = true) :
    val r.exactY < val s.exactY ∨ (val r.exactY = val s.exactY ∧ lessEqual s r = true) := by
  simp only [lessEqual, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ordered ⊢
  rcases ordered with ((gap | ⟨⟨a,b⟩,c⟩) | eq)
  · exact Or.inl (lt_of_le_of_lt hr.2 (lt_of_lt_of_le (by exact_mod_cast gap) hs.1))
  · right
    constructor
    · obtain ⟨rl,rh⟩ := hr
      obtain ⟨sl,sh⟩ := hs
      rw [← a] at rh
      rw [← b, ← c] at sh
      rw [← c] at sl
      linarith
    · exact Or.inl (Or.inr ⟨⟨b,a⟩,c.symm⟩)
  · right
    refine ⟨equality_checked dr ds eq, Or.inr ?_⟩
    obtain ⟨a,b,sign⟩ := of_decide_eq_true eq
    apply decide_eq_true
    exact ⟨a.symm,b.symm,sign.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩

theorem mem_allRows {data m motion moment row} {sheet : Sheet data m motion} :
    row ∈ allRows sheet moment ↔ ∃ i, row ∈ (sheet.rows moment i).value := by
  simp [allRows, List.mem_flatMap]

theorem sheet_bounds {data m motion moment row} {sheet : Sheet data m motion}
    (h : row ∈ allRows sheet moment) :
    contains row.y (val row.exactY) ∧ 0 ≤ (row.exactY.d : ℝ) := by
  obtain ⟨i,hi⟩ := mem_allRows.mp h
  have valid := (piece_complete (sheet.rows moment i).computed).2.1 row hi
  exact ⟨valid.2.1,valid.1⟩

theorem ranked_comparison {data m motion moment} {sheet : Sheet data m motion}
    (rank : ranked (allRows sheet moment) = true) {r s}
    (hr : r ∈ allRows sheet moment) (hs : s ∈ allRows sheet moment) :
    lessEqual r s = true ↔ val r.exactY ≤ val s.exactY := by
  obtain ⟨br,dr⟩ := sheet_bounds hr
  obtain ⟨bs,ds⟩ := sheet_bounds hs
  constructor
  · intro h
    exact (comparison br bs dr ds h).elim le_of_lt (fun h => h.1.le)
  · intro h
    simp only [ranked, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at rank
    rcases rank.2 r hr s hs with ordered | reverse
    · exact ordered
    · exact (comparison bs br ds dr reverse).elim (fun lt => (not_lt_of_ge h lt).elim) And.right

/-- Every section ordinate is bounded above and below by attained values
from this very piece. Use compactness on the closed one-sided interval. -/
theorem piece_bounds {f p o len rows} (ok : candidates f p o len = some rows)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) len) :
    (∃ r ∈ rows, field f x ≤ val r.exactY) ∧ (∃ r ∈ rows, val r.exactY ≤ field f x) := by
  obtain ⟨hlen,_,coverage⟩ := piece_complete ok
  have cont : Continuous (field f) := by unfold field; fun_prop
  have locate (z : ℝ) (hz : z ∈ Icc (0:ℝ) len)
      (ext : IsMaxOn (field f) (Icc 0 len) z ∨ IsMinOn (field f) (Icc 0 len) z) :
      ∃ r ∈ rows, represents f o r z := by
    apply coverage z hz
    by_cases h0 : z = 0
    · exact Or.inl h0
    by_cases he : z = len
    · exact Or.inr (Or.inl he)
    have n := Icc_mem_nhds (lt_of_le_of_ne hz.1 (Ne.symm h0)) (lt_of_le_of_ne hz.2 he)
    exact Or.inr (Or.inr (stationary_condition f z (ext.imp (fun h => h.isLocalMax n) (fun h => h.isLocalMin n))))
  obtain ⟨u,hu,upper⟩ := isCompact_Icc.exists_isMaxOn ⟨x,hx⟩ cont.continuousOn
  obtain ⟨v,hv,lower⟩ := isCompact_Icc.exists_isMinOn ⟨x,hx⟩ cont.continuousOn
  obtain ⟨r,hr,er⟩ := locate u hu (Or.inl upper)
  obtain ⟨s,hs,es⟩ := locate v hv (Or.inr lower)
  exact ⟨⟨r,hr,er.2.symm ▸ upper hx⟩,⟨s,hs,es.2.symm ▸ lower hx⟩⟩

end
end MemberDiagram.Sound
