import MemberKinematicsWire
import InclinedReleaseFields

namespace MemberKinematics.Sound
open FrameEnclosure (Contains executable_multiply_contains)
open FrameIntervalOps FrameIntervalExpression
noncomputable section

/-- Evaluate the same physical piece at any real fraction, using its original
checked coefficients and replacing only the longitudinal position. -/
def atStation (inputs : Fin 15 → ℝ) (length t : ℝ) (i : Fin 15) :=
  if i.val = 10 then length*t else inputs i

def Fits (p : Segment) (inputs : Fin 15 → ℝ) (length : ℝ) :=
  Contains p.length length ∧ ∀ i, Contains (p.inputs i) (inputs i)

theorem enclosure {bits p expr t box inputs length station}
    (fits : Fits p inputs length) (whereAt : Contains t station)
    (done : MemberKinematics.evaluate bits p expr t = some box) :
    Contains box (FrameIntervalExpressionSound.evaluate (atStation inputs length station) expr) := by
  obtain ⟨x,hx,rest⟩ := Option.bind_eq_some.mp done
  apply FrameIntervalExpressionSound.enclose_contains expr rest
  intro i
  by_cases pos : i.val = 10
  · simpa [atStation,pos] using executable_multiply_contains hx fits.1 whereAt
  · simpa [atStation,pos] using fits.2 i

theorem source_fits {data : InclinedFrameSource.Partition} {basis : InclinedFrameBasis.GlobalBasis}
    {bits} {cert : InclinedFrameIntervalAssembly.Certificate data basis}
    (partition : InclinedFrameSource.PartitionValid data) (motion : InclinedFrameReal.Motion data)
    (geo : InclinedFrameIntervalAssembly.GeometryChecks bits cert)
    (loads : InclinedFrameIntervalAssembly.LoadChecks bits cert)
    (nodes : InclinedRelease.Fields.NodeEnclosures bits cert motion)
    {i p} (checked : recover bits cert i = some p) :
    let seg := data.pieces[i.val]!
    Fits p (InclinedRelease.Fields.sourceInputs data motion i seg.left)
      (InclinedFrameReal.pieceLength data seg) := by
  obtain ⟨u,hu,rest⟩ := Option.bind_eq_some.mp checked
  cases rest
  exact ⟨(InclinedFrameIntervalGeometrySound.piece_contains (geo i)).1,
    InclinedRelease.Fields.fieldInputs_contains partition motion geo nodes loads hu⟩

theorem local_transverse (d : FrameInterfaces.LocalDofs) (L EA EI p pEnd q qEnd x c s : ℝ)
    (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0) :
    FrameIntervalExpressionSound.evaluate (FrameIntervalRecoverySound.inputs d L EA EI p pEnd q qEnd x c s)
      transverse = (LocalFrameFields.transverseDisplacement d L EI q qEnd).eval x := by
  rw [(RationalFrame.Fields.affine_recovery d L EA EI p pEnd q qEnd x hL hEA hEI).2.2.2.2.2]
  simp [transverse,FrameIntervalExpressionSound.evaluate,FrameIntervalRecoverySound.inputs]
  ring

/-- A candidate encloses the field throughout its entire station cell. -/
def RowFits (field : ℝ → ℝ) (r : Candidate) :=
  ∀ t, Contains r.t t → Contains r.value (field t)

theorem candidate_fits {bits p f t row inputs length}
    (fits : Fits p inputs length) (made : candidate bits p f t = some row) :
    row.t = t ∧ RowFits (fun s => FrameIntervalExpressionSound.evaluate
      (atStation inputs length s) (quantity f)) row := by
  obtain ⟨value,computed,rest⟩ := Option.bind_eq_some.mp made
  cases rest
  exact ⟨rfl, fun _ loc => enclosure fits loc computed⟩

@[local simp] theorem centeredInput1 (v : Fin 15 → ℝ) (m d : ℝ) : centeredInputs v m d 1 = v 1 := rfl
@[local simp] theorem stationInput1 (v : Fin 15 → ℝ) (L t : ℝ) : atStation v L t 1 = v 1 := rfl
@[local simp] theorem centeredInput2 (v : Fin 15 → ℝ) (m d : ℝ) : centeredInputs v m d 2 = v 2 := rfl
@[local simp] theorem stationInput2 (v : Fin 15 → ℝ) (L t : ℝ) : atStation v L t 2 = v 2 := rfl
@[local simp] theorem centeredInput5 (v : Fin 15 → ℝ) (m d : ℝ) : centeredInputs v m d 5 = v 5 := rfl
@[local simp] theorem stationInput5 (v : Fin 15 → ℝ) (L t : ℝ) : atStation v L t 5 = v 5 := rfl
@[local simp] theorem centeredInput8 (v : Fin 15 → ℝ) (m d : ℝ) : centeredInputs v m d 8 = v 8 := rfl
@[local simp] theorem stationInput8 (v : Fin 15 → ℝ) (L t : ℝ) : atStation v L t 8 = v 8 := rfl
@[local simp] theorem centeredInput9 (v : Fin 15 → ℝ) (m d : ℝ) : centeredInputs v m d 9 = v 9 := rfl
@[local simp] theorem stationInput9 (v : Fin 15 → ℝ) (L t : ℝ) : atStation v L t 9 = v 9 := rfl
@[local simp] theorem centeredInput10 (v : Fin 15 → ℝ) (m d : ℝ) : centeredInputs v m d 10 = m := rfl
@[local simp] theorem stationInput10 (v : Fin 15 → ℝ) (L t : ℝ) : atStation v L t 10 = L*t := rfl
@[local simp] theorem centeredInput12 (v : Fin 15 → ℝ) (m d : ℝ) : centeredInputs v m d 12 = v 12 := rfl
@[local simp] theorem stationInput12 (v : Fin 15 → ℝ) (L t : ℝ) : atStation v L t 12 = v 12 := rfl
@[local simp] theorem centeredInput15 (v : Fin 15 → ℝ) (m d : ℝ) : centeredInputs v m d 15 = d := rfl

set_option maxHeartbeats 2400000 in
theorem centered_identity (values : Fin 15 → ℝ) (length middle station : ℝ) (f : Field) :
    FrameIntervalExpressionSound.evaluate
      (centeredInputs values (length*middle) (length*(station-middle))) (centered f) =
    FrameIntervalExpressionSound.evaluate (atStation values length station) (derivativeSign f) := by
  cases f <;>
    simp [centered,derivativeSign,FrameIntervalRecovery.expressions,
      FrameIntervalExpressionSound.evaluate] <;> ring

theorem derivative_contains {bits p f t box inputs length station}
    (fits : Fits p inputs length) (whereAt : Contains t station)
    (done : derivativeBounds bits p f t = some box) :
    Contains box (FrameIntervalExpressionSound.evaluate (atStation inputs length station) (derivativeSign f)) := by
  let mid := (t.lower+t.upper)/2
  rw [← centered_identity inputs length (mid:ℝ) station f]
  obtain ⟨x,hx,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨dx,hd,rest⟩ := Option.bind_eq_some.mp rest
  apply FrameIntervalExpressionSound.enclose_contains _ rest
  have hm : Contains x (length*(mid:ℝ)) := executable_multiply_contains hx fits.1 ⟨le_rfl,le_rfl⟩
  have shift : Contains ⟨t.lower-mid,t.upper-mid⟩ (station-(mid:ℝ)) := by
    simpa only [Contains,Rat.cast_sub] using
      And.intro (sub_le_sub_right whereAt.1 (mid:ℝ)) (sub_le_sub_right whereAt.2 (mid:ℝ))
  have hoff := executable_multiply_contains hd fits.1 shift
  intro i
  by_cases middle : i.val = 10
  · simpa [centeredInputs,middle] using hm
  · by_cases original : i.val < 15
    · simpa [centeredInputs,middle,original] using fits.2 ⟨i.val,original⟩
    · simpa [centeredInputs,middle,original] using hoff

theorem classify_excluded {bits p f t inputs length} (fits : Fits p inputs length)
    (excluded : classify bits p f t = some .excluded) {s : ℝ} (inside : Contains t s) :
    FrameIntervalExpressionSound.evaluate (atStation inputs length s) (derivativeSign f) ≠ 0 := by
  obtain ⟨bound,computed,rest⟩ := Option.bind_eq_some.mp excluded
  have h := derivative_contains fits inside computed
  dsimp only at rest
  split at rest
  next sign =>
    simp only [Bool.or_eq_true,decide_eq_true_eq] at sign
    rcases sign with neg | pos
    · exact ne_of_lt (lt_of_le_of_lt h.2 (by exact_mod_cast neg))
    · exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast pos) h.1)
  next =>
    try dsimp only at rest
    split at rest
    next =>
      obtain ⟨row,_,rest⟩ := Option.bind_eq_some.mp rest
      split at rest <;> cases rest
    next => cases rest

theorem classified_enclosure {bits p f t row} (made : classify bits p f t = some (.enclosing row)) :
    candidate bits p f t = some row := by
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp made
  dsimp only at rest
  split at rest
  next => cases rest
  next =>
    try dsimp only at rest
    split at rest
    next =>
      obtain ⟨r,hr,rest⟩ := Option.bind_eq_some.mp rest
      split at rest
      next => cases rest; exact hr
      next => cases rest
    next => cases rest

/-- Every derivative zero is retained, even if the derivative touches zero
without changing sign or vanishes over an interval. -/
theorem stationary_covered {bits p f inputs length} (fits : Fits p inputs length)
    (fuel : Nat) {budget t result s} (inside : Contains t s)
    (zero : FrameIntervalExpressionSound.evaluate (atStation inputs length s) (derivativeSign f) = 0)
    (done : stationary bits p f t fuel budget = some result) :
    ∃ r ∈ result.1, Contains r.t s ∧ Contains r.value
      (FrameIntervalExpressionSound.evaluate (atStation inputs length s) (quantity f)) := by
  induction fuel generalizing budget t result with
  | zero => cases done
  | succ n ih =>
    cases budget with
    | zero => cases done
    | succ b =>
      obtain ⟨cell,classified,rest⟩ := Option.bind_eq_some.mp done
      cases cell with
      | excluded => exact (classify_excluded fits classified inside zero).elim
      | enclosing row =>
        cases rest
        have h := candidate_fits fits (classified_enclosure classified)
        have hr : Contains row.t s := h.1 ▸ inside
        exact ⟨row,by simp,hr,h.2 s hr⟩
      | subdivide =>
        obtain ⟨⟨left,remaining⟩,hl,rest⟩ := Option.bind_eq_some.mp rest
        obtain ⟨⟨right,_⟩,hr,rest⟩ := Option.bind_eq_some.mp rest
        cases rest
        let mid := (t.lower+t.upper)/2
        by_cases before : s ≤ (mid:ℝ)
        · obtain ⟨r,mem,loc,val⟩ := ih (t := ⟨t.lower,mid⟩) (inside := ⟨inside.1,before⟩) hl
          exact ⟨r,List.mem_append_left _ mem,loc,val⟩
        · obtain ⟨r,mem,loc,val⟩ := ih (t := ⟨mid,t.upper⟩) (inside := ⟨(le_of_not_ge before),inside.2⟩) hr
          exact ⟨r,List.mem_append_right _ mem,loc,val⟩

#print axioms local_transverse
#print axioms source_fits
#print axioms stationary_covered
end
end MemberKinematics.Sound
