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

theorem locate_extreme {f p o len rows} (ok : candidates f p o len = some rows) (z : ℝ) (hz : z ∈ Icc (0:ℝ) len)
      (ext : IsMaxOn (field f) (Icc 0 len) z ∨ IsMinOn (field f) (Icc 0 len) z) :
      ∃ r ∈ rows, represents f o r z := by
    apply (piece_complete ok).2.2 z hz
    by_cases h0 : z = 0
    · exact Or.inl h0
    by_cases he : z = len
    · exact Or.inr (Or.inl he)
    have n := Icc_mem_nhds (lt_of_le_of_ne hz.1 (Ne.symm h0)) (lt_of_le_of_ne hz.2 he)
    exact Or.inr (Or.inr (stationary_condition f z (ext.imp (fun h => h.isLocalMax n) (fun h => h.isLocalMin n))))

/-- Every section ordinate is bounded above and below by attained values
from this very piece. Use compactness on the closed one-sided interval. -/
theorem piece_bounds {f p o len rows} (ok : candidates f p o len = some rows)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) len) :
    (∃ r ∈ rows, field f x ≤ val r.exactY) ∧ (∃ r ∈ rows, val r.exactY ≤ field f x) := by
  have cont : Continuous (field f) := by unfold field; fun_prop
  obtain ⟨u,hu,upper⟩ := isCompact_Icc.exists_isMaxOn ⟨x,hx⟩ cont.continuousOn
  obtain ⟨v,hv,lower⟩ := isCompact_Icc.exists_isMinOn ⟨x,hx⟩ cont.continuousOn
  obtain ⟨r,hr,er⟩ := locate_extreme ok u hu (Or.inl upper)
  obtain ⟨s,hs,es⟩ := locate_extreme ok v hv (Or.inr lower)
  exact ⟨⟨r,hr,er.2.symm ▸ upper hx⟩,⟨s,hs,es.2.symm ▸ lower hx⟩⟩

/-- Include both limits at a load discontinuity by quantifying independently
over the closed domain of every selected source piece. -/
def attained {data m motion} (_sheet : Sheet data m motion) (moment : Bool) (y : ℝ) :=
  ∃ (i : Index data m) (x : ℝ), x ∈ Icc (0:ℝ) (segmentAt data m i).length ∧
    field (polynomial (segmentAt data m i) (motion (segmentAt data m i)) moment) x = y

theorem attained_row {data m motion moment row} {sheet : Sheet data m motion}
    (h : row ∈ allRows sheet moment) : attained sheet moment (val row.exactY) := by
  obtain ⟨i,hi⟩ := mem_allRows.mp h
  obtain ⟨_,_,x,hx,rep⟩ := (piece_complete (sheet.rows moment i).computed).2.1 row hi
  exact ⟨i,x,hx,rep.2.symm⟩

def correctFlags {data m motion} (sheet : Sheet data m motion) (moment : Bool) :=
  ∀ r ∈ allRows sheet moment,
    ((allRows sheet moment).all (lessEqual r) = true ↔
      ∀ y, attained sheet moment y → val r.exactY ≤ y) ∧
    ((allRows sheet moment).all (fun s => lessEqual s r) = true ↔
      ∀ y, attained sheet moment y → y ≤ val r.exactY)

theorem global_flags {data m motion moment} {sheet : Sheet data m motion}
    (rank : ranked (allRows sheet moment) = true) : correctFlags sheet moment := by
  intro r hr
  simp only [List.all_eq_true]
  constructor
  · constructor
    · intro flags y ⟨i,x,hx,eq⟩
      obtain ⟨s,hs,low⟩ := (piece_bounds (sheet.rows moment i).computed hx).2
      have mem := (mem_allRows (sheet := sheet) (moment := moment)).2 ⟨i,hs⟩
      exact eq ▸ (le_trans ((ranked_comparison rank hr mem).mp (flags s mem)) low)
    · intro bound s hs
      exact (ranked_comparison rank hr hs).mpr (bound _ (attained_row hs))
  · constructor
    · intro flags y ⟨i,x,hx,eq⟩
      obtain ⟨s,hs,high⟩ := (piece_bounds (sheet.rows moment i).computed hx).1
      have mem := (mem_allRows (sheet := sheet) (moment := moment)).2 ⟨i,hs⟩
      exact eq ▸ (le_trans high ((ranked_comparison rank mem hr).mp (flags s mem)))
    · intro bound s hs
      exact (ranked_comparison rank hs hr).mpr (bound _ (attained_row hs))

/-- Every tied location on every piece, including each point of a constant
interval, belongs to the location box of a flagged row on that piece. -/
theorem tied_max_location {data m motion flag} (sheet : Sheet data m motion)
    (flags : correctFlags sheet flag) (i : Index data m) (x : ℝ)
    (hx : x ∈ Icc (0:ℝ) (segmentAt data m i).length)
    (bound : ∀ y, attained sheet flag y → y ≤ field (polynomial (segmentAt data m i) (motion (segmentAt data m i)) flag) x) :
    ∃ r ∈ (sheet.rows flag i).value,
      represents (polynomial (segmentAt data m i) (motion (segmentAt data m i)) flag) (originAt data m i) r x ∧
      (allRows sheet flag).all (fun s => lessEqual s r) = true := by
  have hm : IsMaxOn (field (polynomial (segmentAt data m i) (motion (segmentAt data m i)) flag)) (Icc (0:ℝ) (segmentAt data m i).length) x := fun z hz => bound _ ⟨i,z,hz,rfl⟩
  obtain ⟨r,hr,rep⟩ := locate_extreme (sheet.rows flag i).computed x hx (Or.inl hm)
  refine ⟨r,hr,rep,(flags r (mem_allRows.mpr ⟨i,hr⟩)).2.mpr ?_⟩
  rw [rep.2]
  exact bound

theorem tied_min_location {data m motion flag} (sheet : Sheet data m motion)
    (flags : correctFlags sheet flag) (i : Index data m) (x : ℝ)
    (hx : x ∈ Icc (0:ℝ) (segmentAt data m i).length)
    (bound : ∀ y, attained sheet flag y → field (polynomial (segmentAt data m i) (motion (segmentAt data m i)) flag) x ≤ y) :
    ∃ r ∈ (sheet.rows flag i).value,
      represents (polynomial (segmentAt data m i) (motion (segmentAt data m i)) flag) (originAt data m i) r x ∧
      (allRows sheet flag).all (lessEqual r) = true := by
  have hm : IsMinOn (field (polynomial (segmentAt data m i) (motion (segmentAt data m i)) flag)) (Icc (0:ℝ) (segmentAt data m i).length) x := fun z hz => bound _ ⟨i,z,hz,rfl⟩
  obtain ⟨r,hr,rep⟩ := locate_extreme (sheet.rows flag i).computed x hx (Or.inr hm)
  refine ⟨r,hr,rep,(flags r (mem_allRows.mpr ⟨i,hr⟩)).1.mpr ?_⟩
  rw [rep.2]
  exact bound

theorem selected_iff {data : Compiled} {m} (i : Fin data.segments.size) :
    i ∈ selected data m ↔ data.segments[i.val]!.member = m := by simp [selected]

open RationalFrameSoundness RationalFrame.Interpretation FrameAssemblyModel

/-- Use the segment degrees of freedom from the unique equilibrium motion
of the original model when interpreting each polynomial at real distance x. -/
theorem physical_fields (data : Compiled) (valid : PartitionValid data) (m : Nat)
    (values : Array Rat) (i : Index data m) (x : ℝ) :
    let s := segmentAt data m i
    let d := segmentDofs (model data valid) (motion data valid (fun j => (values[j.val]! : ℝ)))
      ((selected data m).get i)
    let q := (s.cosine : ℝ) * s.vertical
    let qEnd := (s.cosine : ℝ) * s.verticalEnd
    field (polynomial s values false) x = (LocalFrameFields.shear d s.length s.EI q qEnd).eval x ∧
    field (polynomial s values true) x = (LocalFrameFields.moment d s.length s.EI q qEnd).eval x := by
  let j := (selected data m).get i
  rcases segments_valid data valid j with ⟨_,_,_,_,_,_,_,length,axial,bending,_⟩
  have fields := source_fields data.segments[j.val]! values x
    (by exact_mod_cast ne_of_gt length) (by exact_mod_cast ne_of_gt axial) (by exact_mod_cast ne_of_gt bending)
  rw [Recovery.actual_local_motion data valid j values] at fields
  exact fields

theorem accepted_report {input output : String} (h : checkReport input = some output) :
    ∃ (p : RationalFrame.Wire.Packet) (data : Compiled) (valid : PartitionValid data) (sheet : Sheet data p.query.member (fun _ => p.certificate.motion)),
      RationalFrame.Wire.decode input = some p ∧ compileModel p.source = some data ∧
      data.source = p.source ∧ ActualModel data valid ∧ StableResult data valid p.query p.certificate ∧
      output = encode sheet ∧ correctFlags sheet false ∧ correctFlags sheet true := by
  obtain ⟨p,decoded,rest⟩ := Option.bind_eq_some.mp h
  change (if !p.certificate.mechanism && accepts p.source p.query p.certificate then _ else none) = some output at rest
  split at rest
  next accepted =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at accepted
    obtain ⟨data,compiled,rest⟩ := Option.bind_eq_some.mp rest
    obtain ⟨sheet,built,result⟩ := Option.bind_eq_some.mp rest
    split at result
    next ranks =>
      cases result
      obtain ⟨_,other,valid,comp,src,_,_,actual,stable⟩ :=
        acceptance_actual_frame p.source p.query p.certificate accepted.2
      rw [compiled] at comp
      cases comp
      simp only [accepted.1, Bool.false_eq_true, if_false] at stable
      simp only [Bool.and_eq_true] at ranks
      exact ⟨p,data,valid,sheet,decoded,compiled,src,actual,stable,rfl,
        global_flags ranks.1.1,global_flags ranks.1.2⟩
    next => contradiction
  next => contradiction

#print axioms physical_fields
#print axioms tied_min_location
#print axioms tied_max_location
#print axioms accepted_report
end
end MemberDiagram.Sound
