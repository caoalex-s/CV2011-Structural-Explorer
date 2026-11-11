import RationalFrameInterpretation
import RationalFrameFields

/-! The signed coordinate permutation in the executable assembly is the
    actual rigid member-side map of the original frame interpretation. -/
namespace RationalFrame.Assembly
open FrameAssemblyModel FrameTransform Interpretation
noncomputable section

theorem segment_axes (data : Compiled) (valid : PartitionValid data) (i : Fin data.segments.size) :
    let segment := data.segments[i.val]!
    segment.cosine = memberCosine data.source segment.member ∧
    segment.sine = memberSine data.source segment.member ∧
    (segment.cosine = 0 ∨ segment.sine = 0) ∧ segment.a ≠ segment.b := by
  rcases segments_valid data valid i with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, hs, _, haxis, _, hends⟩
  exact ⟨hc, hs, haxis, hends⟩

/-- The six local degrees of freedom are not an independent supplied map:
    they are the actual end maps, rotated using the source member axes. -/
theorem segment_dofs (data : Compiled) (valid : PartitionValid data)
    (values : Nat → ℝ) (segment : Fin data.segments.size) (i : Fin 6) :
    segmentDofs (model data valid) (motion data valid (fun j => values j.val)) segment i =
      (coordinateSign data.segments[segment.val]! i : ℝ) *
        values (globalIndex data.segments[segment.val]! i) := by
  have leftMotion : sideMotion (model data valid) (motion data valid (fun j => values j.val))
      ((model data valid).segmentLeft segment) =
      fun direction => values (3 * data.segments[segment.val]!.a + direction.val) := by
    rw [side_reference]
    change referenceMotion (model data valid) (motion data valid (fun j => values j.val))
      (locationPoint (model data valid) (location data (segmentMember data valid segment)
        data.segments[segment.val]!.left (segmentStart data valid segment))) = _
    rw [location_point data valid _ _ _ (segments_valid data valid segment).2.1]
    funext direction
    exact reference_motion data valid values (segmentStart data valid segment) direction
  have rightMotion : sideMotion (model data valid) (motion data valid (fun j => values j.val))
      ((model data valid).segmentRight segment) =
      fun direction => values (3 * data.segments[segment.val]!.b + direction.val) := by
    rw [side_reference]
    change referenceMotion (model data valid) (motion data valid (fun j => values j.val))
      (locationPoint (model data valid) (location data (segmentMember data valid segment)
        data.segments[segment.val]!.right (segmentEnd data valid segment))) = _
    rw [location_point data valid _ _ _ (segments_valid data valid segment).2.2.1]
    funext direction
    exact reference_motion data valid values (segmentEnd data valid segment) direction
  obtain ⟨hc, hs, haxis, _⟩ := segment_axes data valid segment
  simp only [segmentDofs, segmentMotion, leftMotion, rightMotion]
  change toLocal6 (memberCosine data.source data.segments[segment.val]!.member : ℝ)
    (memberSine data.source data.segments[segment.val]!.member : ℝ) _ i = _
  rw [← hc, ← hs]
  by_cases horizontal : data.segments[segment.val]!.cosine = 0
  · fin_cases i <;> simp [toLocal6, coordinateSign, globalIndex, horizontal]
  · have vertical : data.segments[segment.val]!.sine = 0 := haxis.resolve_left horizontal
    fin_cases i <;> simp [toLocal6, coordinateSign, globalIndex, horizontal, vertical]

end
end RationalFrame.Assembly
