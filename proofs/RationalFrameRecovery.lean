import RationalFrameAssembly

/-! Checked one-sided recovery retains the actual loaded polynomial fields,
    including their particular displacement and rotation terms. -/
namespace RationalFrame.Recovery
open FrameInterfaces FrameAssemblyModel Interpretation
noncomputable section

def fieldValues (d : LocalDofs) (L EA EI c s intensity intensityEnd x : ℝ) : Fin 6 → ℝ :=
  let p := s * intensity
  let q := c * intensity
  let pEnd := s * intensityEnd
  let qEnd := c * intensityEnd
  let axial := (LocalFrameFields.axialDisplacement d L EA p pEnd).eval x
  let transverse := (LocalFrameFields.transverseDisplacement d L EI q qEnd).eval x
  ![(LocalFrameFields.normal d L EA p pEnd).eval x,
    (LocalFrameFields.shear d L EI q qEnd).eval x,
    (LocalFrameFields.moment d L EI q qEnd).eval x,
    (LocalFrameFields.rotation d L EI q qEnd).eval x,
    c*axial - s*transverse, s*axial + c*transverse]

theorem end_action_cast (segment : Segment) (motion : Array Rat)
    (length : (segment.length : ℝ) ≠ 0) (axial : (segment.EA : ℝ) ≠ 0) (bending : (segment.EI : ℝ) ≠ 0)
    (i : Fin 6) :
    (endAction segment motion i : ℝ) = LocalFrameFields.endActions
      (fun j => (localMotion segment motion j : ℝ)) (segment.length : ℝ) (segment.EA : ℝ) (segment.EI : ℝ)
      ((segment.sine * segment.vertical : Rat) : ℝ) ((segment.sine * segment.verticalEnd : Rat) : ℝ)
      ((segment.cosine * segment.vertical : Rat) : ℝ) ((segment.cosine * segment.verticalEnd : Rat) : ℝ) i := by
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
        (segment.verticalEnd : ℝ)
        ((segment.length * (parameter-segment.left) / (segment.right-segment.left) : Rat) : ℝ) i := by
  have formulas := Fields.affine_recovery (fun j => (localMotion segment motion j : ℝ))
    (segment.length : ℝ) (segment.EA : ℝ) (segment.EI : ℝ)
    ((segment.sine * segment.vertical : Rat) : ℝ) ((segment.sine * segment.verticalEnd : Rat) : ℝ)
    ((segment.cosine * segment.vertical : Rat) : ℝ) ((segment.cosine * segment.verticalEnd : Rat) : ℝ)
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

/-- Six quantities from the actual member-side motion and loaded fields.
    The coordinate x is measured from the selected segment's original-left
    boundary, in metres along the original member orientation. -/
def actualValues (data : Compiled) (valid : PartitionValid data)
    (values : Array Rat) (segment : Fin data.segments.size) (parameter : Rat) : Fin 6 → ℝ :=
  let frame := model data valid
  let orientation := (frame.member (frame.segmentMember segment)).orientation
  fieldValues (segmentDofs frame (motion data valid (fun i => (values[i.val]! : ℝ))) segment)
    (frame.segmentLength segment) (frame.segmentEA segment) (frame.segmentEI segment)
    orientation.cosine orientation.sine (frame.segmentVerticalStart segment) (frame.segmentVerticalEnd segment)
    (frame.segmentLength segment * ((parameter : ℝ) - (data.segments[segment.val]!.left : ℝ)) /
      ((data.segments[segment.val]!.right : ℝ) - (data.segments[segment.val]!.left : ℝ)))

theorem checked_readouts (data : Compiled) (valid : PartitionValid data)
    (query : Query) (certificate : Certificate)
    (queryChecked : queryValid data query = true) (solution : SolutionValid data query certificate) :
    ∃ segment : Fin data.segments.size,
      selectedIndex data query = some segment ∧ SideContains data.segments[segment.val]! query ∧
      ∀ i : Fin 6, (certificate.readouts[i.val]! : ℝ) =
        actualValues data valid certificate.motion segment query.t i := by
  obtain ⟨segment, selected, contains⟩ := checked_selection data query queryChecked
  refine ⟨segment, selected, contains, ?_⟩
  intro i
  rw [solution.2.2.1]
  simp only [recover, selectedSegment, selected, Option.map_some]
  change ((recoverSegment data.segments[segment.val]! query.t certificate.motion)[i.val]! : ℝ) = _
  rcases segments_valid data valid segment with
    ⟨_, _, _, _, _, _, _, length, axial, bending, _, _, cosine, sine, _⟩
  have lengthReal : (data.segments[segment.val]!.length : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt length
  have axialReal : (data.segments[segment.val]!.EA : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt axial
  have bendingReal : (data.segments[segment.val]!.EI : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt bending
  rw [recover_segment_cast _ _ _ lengthReal axialReal bendingReal, actual_local_motion]
  change fieldValues _ _ _ _ _ _ _ _ _ i = fieldValues _ _ _ _
    (memberCosine data.source data.segments[segment.val]!.member : ℝ)
    (memberSine data.source data.segments[segment.val]!.member : ℝ) _ _ _ i
  rw [← cosine, ← sine]
  push_cast
  rfl

end
end RationalFrame.Recovery
