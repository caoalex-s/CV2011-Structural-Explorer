import RationalFrameGeometry

/-! Exact ownership, coverage and represented boundary locations for the
    original-member frame. This contract is derived from checked finite
    subdivision postconditions rather than supplied as a proof assumption. -/
namespace RationalFrame.Contract
open FrameAssemblyModel Interpretation
noncomputable section

theorem left_parameter (data : Compiled) (valid : PartitionValid data) (segment : Fin data.segments.size) :
    locationParameter (cutParameter data) ((model data valid).segmentLeft segment) =
      (data.segments[segment.val]!.left : ℝ) :=
  location_parameter data _ _ _ (segments_valid data valid segment).2.1

theorem right_parameter (data : Compiled) (valid : PartitionValid data) (segment : Fin data.segments.size) :
    locationParameter (cutParameter data) ((model data valid).segmentRight segment) =
      (data.segments[segment.val]!.right : ℝ) :=
  location_parameter data _ _ _ (segments_valid data valid segment).2.2.1

theorem location_owner (data : Compiled) (member owner : Fin data.source.members.size)
    (t : Rat) (index : Fin data.points.size) :
    locationBelongs member (location data owner t index) ↔ owner = member := by
  unfold location
  split_ifs <;> rfl

theorem location_unique (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size) (t : Rat) (i j : Fin data.points.size)
    (left : LocationValid data member.val t i.val) (right : LocationValid data member.val t j.val) :
    location data member t i = location data member t j := by
  by_cases atStart : t = 0
  · simp [location, atStart]
  by_cases atEnd : t = 1
  · simp [location, atEnd]
  have li := left.2.2
  have rj := right.2.2
  simp only [atStart, atEnd, ↓reduceIte] at li rj
  have pi := points_valid data valid i
  have pj := points_valid data valid j
  simp only [PointValid, li.1] at pi
  simp only [PointValid, rj.1] at pj
  have same : i = j := by
    rcases valid with ⟨_, _, _, _, _, _, _, unique, _⟩
    apply unique i j
    · exact li.1.trans rj.1.symm
    · exact pi.2.2.1.trans pj.2.2.1.symm
    · exact li.2.trans rj.2.symm
  rw [same]

theorem represented_decomposition (data : Compiled) (valid : PartitionValid data)
    (selected : Location data.source.members.size data.points.size)
    (represented : representedLocation (model data valid) selected) :
    ∃ member t index, selected = location data member t index ∧
      LocationValid data member.val t index.val := by
  obtain ⟨segment, left | right⟩ := represented
  · exact ⟨segmentMember data valid segment, data.segments[segment.val]!.left,
      segmentStart data valid segment, left.symm, (segments_valid data valid segment).2.1⟩
  · exact ⟨segmentMember data valid segment, data.segments[segment.val]!.right,
      segmentEnd data valid segment, right.symm, (segments_valid data valid segment).2.2.1⟩

theorem canonical_locations (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size)
    (left right : Location data.source.members.size data.points.size)
    (leftOwner : locationBelongs member left) (rightOwner : locationBelongs member right)
    (leftRepresented : representedLocation (model data valid) left)
    (rightRepresented : representedLocation (model data valid) right)
    (sameParameter : locationParameter (cutParameter data) left = locationParameter (cutParameter data) right) :
    left = right := by
  obtain ⟨lm, lt, li, rfl, lh⟩ := represented_decomposition data valid left leftRepresented
  obtain ⟨rm, rt, ri, rfl, rh⟩ := represented_decomposition data valid right rightRepresented
  have leftMember := (location_owner data member lm lt li).mp leftOwner
  have rightMember := (location_owner data member rm rt ri).mp rightOwner
  subst lm
  subst rm
  rw [location_parameter data _ _ _ lh, location_parameter data _ _ _ rh] at sameParameter
  have same : lt = rt := by exact_mod_cast sameParameter
  subst rt
  exact location_unique data valid member lt li ri lh rh

theorem represented_of_check (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size) (t : Rat) (index : Fin data.points.size)
    (checked : locationRepresented data member.val t index.val = true) :
    representedLocation (model data valid) (location data member t index) := by
  simp only [locationRepresented, Array.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at checked
  obtain ⟨i, bound, owner, endpoint⟩ := checked
  let segment : Fin data.segments.size := ⟨i, bound⟩
  have owned : segmentMember data valid segment = member := by
    apply Fin.ext
    simpa [segmentMember, segment, getElem!_pos, bound] using owner
  rcases endpoint with left | right
  · have position : data.segments[segment.val]!.left = t := by
      simpa [segment, getElem!_pos, bound] using left.1
    have point : segmentStart data valid segment = index := by
      apply Fin.ext
      simpa [segmentStart, segment, getElem!_pos, bound] using left.2
    refine ⟨segment, Or.inl ?_⟩
    change location data (segmentMember data valid segment) _ (segmentStart data valid segment) = _
    rw [owned, position, point]
  · have position : data.segments[segment.val]!.right = t := by
      simpa [segment, getElem!_pos, bound] using right.1
    have point : segmentEnd data valid segment = index := by
      apply Fin.ext
      simpa [segmentEnd, segment, getElem!_pos, bound] using right.2
    refine ⟨segment, Or.inr ?_⟩
    change location data (segmentMember data valid segment) _ (segmentEnd data valid segment) = _
    rw [owned, position, point]

theorem coverage (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size) (t : ℝ) (nonnegative : 0 ≤ t) (bounded : t ≤ 1) :
    ∃ segment, (model data valid).segmentMember segment = member ∧
      locationParameter (cutParameter data) ((model data valid).segmentLeft segment) ≤ t ∧
      t ≤ locationParameter (cutParameter data) ((model data valid).segmentRight segment) := by
  obtain ⟨part, represented, left, right⟩ := member_coverage data valid member t nonnegative bounded
  have filtered := List.mem_filter.mp represented
  obtain ⟨i, bound, value⟩ := List.mem_iff_getElem.mp filtered.1
  have arrayBound : i < data.segments.size := by simpa using bound
  have element : data.segments[i]! = part := by simpa [getElem!_pos, arrayBound] using value
  refine ⟨⟨i, arrayBound⟩, ?_, ?_, ?_⟩
  · apply Fin.ext
    simpa [model, segmentMember, element] using filtered.2
  · rw [left_parameter]
    simpa [element] using left
  · rw [right_parameter]
    simpa [element] using right

end
end RationalFrame.Contract
