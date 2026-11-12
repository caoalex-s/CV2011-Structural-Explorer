import RationalFrameAssembly

/-! Checked one-sided recovery retains the actual loaded polynomial fields,
    including their particular displacement and rotation terms. -/
namespace RationalFrame.Recovery
open FrameInterfaces FrameAssemblyModel Interpretation
noncomputable section

def fieldValues (d : LocalDofs) (L EA EI c s intensity x : ℝ) : Fin 6 → ℝ :=
  let p := s * intensity
  let q := c * intensity
  let axial := (LocalFrameFields.axialDisplacement d L EA p p).eval x
  let transverse := (LocalFrameFields.transverseDisplacement d L EI q q).eval x
  ![(LocalFrameFields.normal d L EA p p).eval x,
    (LocalFrameFields.shear d L EI q q).eval x,
    (LocalFrameFields.moment d L EI q q).eval x,
    (LocalFrameFields.rotation d L EI q q).eval x,
    c*axial - s*transverse, s*axial + c*transverse]

theorem end_action_cast (segment : Segment) (motion : Array Rat)
    (length : (segment.length : ℝ) ≠ 0) (axial : (segment.EA : ℝ) ≠ 0) (bending : (segment.EI : ℝ) ≠ 0)
    (i : Fin 6) :
    (endAction segment motion i : ℝ) = LocalFrameFields.endActions
      (fun j => (localMotion segment motion j : ℝ)) (segment.length : ℝ) (segment.EA : ℝ) (segment.EI : ℝ)
      ((segment.sine * segment.vertical : Rat) : ℝ) ((segment.sine * segment.vertical : Rat) : ℝ)
      ((segment.cosine * segment.vertical : Rat) : ℝ) ((segment.cosine * segment.vertical : Rat) : ℝ) i := by
  rw [LocalFrameFields.end_actions_from_fields _ _ _ _ _ _ _ _ length axial bending]
  simp only [endAction, Algebra.sumFin_eq_sum, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul,
    Fields.stiffness_cast, Fields.force_cast]

set_option maxHeartbeats 1000000 in
theorem recover_segment_cast (segment : Segment) (parameter : Rat) (motion : Array Rat)
    (length : (segment.length : ℝ) ≠ 0) (axial : (segment.EA : ℝ) ≠ 0) (bending : (segment.EI : ℝ) ≠ 0)
    (i : Fin 6) :
    ((recoverSegment segment parameter motion)[i.val]! : ℝ) =
      fieldValues (fun j => (localMotion segment motion j : ℝ))
        (segment.length : ℝ) (segment.EA : ℝ) (segment.EI : ℝ)
        (segment.cosine : ℝ) (segment.sine : ℝ) (segment.vertical : ℝ)
        ((segment.length * (parameter-segment.left) / (segment.right-segment.left) : Rat) : ℝ) i := by
  have formulas := Fields.uniform_recovery (fun j => (localMotion segment motion j : ℝ))
    (segment.length : ℝ) (segment.EA : ℝ) (segment.EI : ℝ)
    ((segment.sine * segment.vertical : Rat) : ℝ) ((segment.cosine * segment.vertical : Rat) : ℝ)
    ((segment.length * (parameter-segment.left) / (segment.right-segment.left) : Rat) : ℝ) length axial bending
  obtain ⟨normal, shear, moment, rotation, displacementX, displacementY⟩ := formulas
  have actions := end_action_cast segment motion length axial bending
  push_cast at normal shear moment rotation displacementX displacementY actions
  fin_cases i <;>
    simp [recoverSegment, fieldValues, normal, shear, moment, rotation,
      displacementX, displacementY, ← actions] <;> ring

theorem actual_local_motion (data : Compiled) (valid : PartitionValid data)
    (segment : Fin data.segments.size) (values : Array Rat) :
    (fun i => (localMotion data.segments[segment.val]! values i : ℝ)) =
      segmentDofs (model data valid) (motion data valid (fun i => (values[i.val]! : ℝ))) segment := by
  funext i
  simpa only [localMotion, Rat.cast_mul] using
    (Assembly.segment_dofs data valid (fun i => (values[i]! : ℝ)) segment i).symm

theorem checked_selection (data : Compiled) (query : Query) (checked : queryValid data query = true) :
    ∃ i : Fin data.segments.size, selectedIndex data query = some i ∧ SideContains data.segments[i.val]! query := by
  cases selected : selectedIndex data query with
  | none => simp [queryValid, selected] at checked
  | some i =>
    refine ⟨i, rfl, ?_⟩
    simp only [queryValid, selected, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.2

end
end RationalFrame.Recovery
