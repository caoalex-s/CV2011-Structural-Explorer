import RationalFrameInterpretation
import ExactGeometry

/-! Original endpoint geometry determines the interpreted member axes and
    segment lengths. The real model remains anchored to the exact parsed
    source coordinates, including reversed horizontal and vertical members. -/
namespace RationalFrame.Geometry
open FrameAssemblyModel Interpretation
noncomputable section

theorem member_segment (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size) :
    ∃ segment : Fin data.segments.size, segmentMember data valid segment = member := by
  obtain ⟨segment, represented, _, _⟩ := member_coverage data valid member 0 le_rfl (by norm_num)
  have filtered := List.mem_filter.mp represented
  have owner : segment.member = member.val := by simpa using filtered.2
  obtain ⟨index, bound, value⟩ := List.mem_iff_getElem.mp filtered.1
  have element : data.segments[index]! = segment := by simpa [getElem!_pos, bound] using value
  refine ⟨⟨index, by simpa using bound⟩, ?_⟩
  apply Fin.ext
  simpa [segmentMember, element] using owner

theorem member_properties (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size) :
    0 < data.source.members[member.val]!.EA ∧ 0 < data.source.members[member.val]!.EI ∧
    (memberCosine data.source member.val)^2 + (memberSine data.source member.val)^2 = 1 := by
  obtain ⟨segment, same⟩ := member_segment data valid member
  have owner : data.segments[segment.val]!.member = member.val := congrArg Fin.val same
  rcases segments_valid data valid segment with
    ⟨_, _, _, _, _, _, _, _, hEA, hEI, EA, EI, cosine, sine, normalized, _⟩
  rw [owner] at EA EI cosine sine
  rw [EA] at hEA
  rw [EI] at hEI
  refine ⟨hEA, hEI, ?_⟩
  rw [cosine, sine] at normalized
  simpa only [pow_two] using normalized

def nodePosition (data : Compiled) (node : Fin data.source.nodes.size) : ExactGeometry.Point :=
  ((data.source.nodes[node.val]!.x : ℝ), (data.source.nodes[node.val]!.y : ℝ))

def drawingStart (data : Compiled) (valid : PartitionValid data) (member : Fin data.source.members.size) :
    Fin data.source.nodes.size := ⟨data.source.members[member.val]!.a, (members_bounded data valid member).1⟩

def drawingEnd (data : Compiled) (valid : PartitionValid data) (member : Fin data.source.members.size) :
    Fin data.source.nodes.size := ⟨data.source.members[member.val]!.b, (members_bounded data valid member).2.1⟩

theorem member_distance (data : Compiled) (valid : PartitionValid data) (member : Fin data.source.members.size) :
    ExactGeometry.distance (nodePosition data (drawingStart data valid member))
      (nodePosition data (drawingEnd data valid member)) = (memberLength data.source member.val : ℝ) := by
  have positive := (members_bounded data valid member).2.2
  have normalized := (member_properties data valid member).2.2
  have nonzero : memberLength data.source member.val ≠ 0 := ne_of_gt positive
  have squared : (memberLength data.source member.val)^2 =
      (data.source.nodes[data.source.members[member.val]!.b]!.x -
        data.source.nodes[data.source.members[member.val]!.a]!.x)^2 +
      (data.source.nodes[data.source.members[member.val]!.b]!.y -
        data.source.nodes[data.source.members[member.val]!.a]!.y)^2 := by
    dsimp [memberCosine, memberSine] at normalized
    field_simp [nonzero] at normalized
    nlinarith
  have realSquared := congrArg (fun value : Rat => (value : ℝ)) squared
  push_cast at realSquared
  have realPositive : 0 < (memberLength data.source member.val : ℝ) := by exact_mod_cast positive
  simp only [ExactGeometry.distance, ExactGeometry.dx, ExactGeometry.dy,
    nodePosition, drawingStart, drawingEnd]
  rw [← realSquared, Real.sqrt_sq_eq_abs, abs_of_pos realPositive]

theorem member_direction (data : Compiled) (valid : PartitionValid data) (member : Fin data.source.members.size) :
    (model data valid).member member |>.orientation =
      ExactGeometry.direction (nodePosition data (drawingStart data valid member))
        (nodePosition data (drawingEnd data valid member)) := by
  unfold ExactGeometry.direction
  rw [member_distance]
  simp [model, memberCosine, memberSine, nodePosition, drawingStart, drawingEnd,
    ExactGeometry.dx, ExactGeometry.dy]

def segmentStartPosition (data : Compiled) (valid : PartitionValid data) (segment : Fin data.segments.size) :
    ExactGeometry.Point :=
  ExactGeometry.position (nodePosition data (drawingStart data valid (segmentMember data valid segment)))
    (nodePosition data (drawingEnd data valid (segmentMember data valid segment))) (data.segments[segment.val]!.left : ℝ)

def segmentEndPosition (data : Compiled) (valid : PartitionValid data) (segment : Fin data.segments.size) :
    ExactGeometry.Point :=
  ExactGeometry.position (nodePosition data (drawingStart data valid (segmentMember data valid segment)))
    (nodePosition data (drawingEnd data valid (segmentMember data valid segment))) (data.segments[segment.val]!.right : ℝ)

theorem correspondence (data : Compiled) (valid : PartitionValid data) :
    ExactGeometry.GeometryCorrespondence (model data valid) (nodePosition data)
      (drawingStart data valid) (drawingEnd data valid) (cutParameter data)
      (fun member => (data.source.members[member.val]!.EA : ℝ))
      (fun member => (data.source.members[member.val]!.EI : ℝ))
      (segmentStartPosition data valid) (segmentEndPosition data valid) := by
  refine ⟨?_, member_direction data valid, ?_, ?_, ?_, ?_⟩
  · intro member
    exact ⟨rfl, rfl⟩
  · intro segment
    change _ = ExactGeometry.position _ _ (locationParameter (cutParameter data)
      (location data _ _ _))
    rw [location_parameter data _ _ _ (segments_valid data valid segment).2.1]
    rfl
  · intro segment
    change _ = ExactGeometry.position _ _ (locationParameter (cutParameter data)
      (location data _ _ _))
    rw [location_parameter data _ _ _ (segments_valid data valid segment).2.2.1]
    rfl
  · intro segment
    rcases segments_valid data valid segment with ⟨_, _, _, _, ordered, _, length, _⟩
    unfold segmentStartPosition segmentEndPosition
    rw [ExactGeometry.segment_distance _ _ _ _ (by exact_mod_cast ordered), member_distance]
    change (data.segments[segment.val]!.length : ℝ) = _
    have castLength := congrArg (fun value : Rat => (value : ℝ)) length
    push_cast at castLength
    simpa [segmentMember, mul_comm] using castLength
  · intro segment
    rcases segments_valid data valid segment with ⟨_, _, _, _, _, _, _, _, _, _, EA, EI, _⟩
    constructor
    · exact_mod_cast EA
    · exact_mod_cast EI

end
end RationalFrame.Geometry
