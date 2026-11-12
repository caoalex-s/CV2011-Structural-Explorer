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

theorem member_ends (data : Compiled) (valid : PartitionValid data) (member : Fin data.source.members.size) :
    representedLocation (model data valid) (.endSide (member, false)) ∧
      representedLocation (model data valid) (.endSide (member, true)) := by
  constructor
  · obtain ⟨segment, owner, left, _⟩ := coverage data valid member 0 le_rfl (by norm_num)
    rw [left_parameter] at left
    have nonnegative := (segments_valid data valid segment).2.2.2.1
    have leZero : data.segments[segment.val]!.left ≤ 0 := by exact_mod_cast left
    have endpoint := le_antisymm leZero nonnegative
    refine ⟨segment, Or.inl ?_⟩
    change location data (segmentMember data valid segment) _ _ = _
    change segmentMember data valid segment = member at owner
    simp [location, endpoint, owner]
  · obtain ⟨segment, owner, _, right⟩ := coverage data valid member 1 (by norm_num) le_rfl
    rw [right_parameter] at right
    have bounded := (segments_valid data valid segment).2.2.2.2.2.1
    have geOne : 1 ≤ data.segments[segment.val]!.right := by exact_mod_cast right
    have endpoint := le_antisymm bounded geOne
    refine ⟨segment, Or.inr ?_⟩
    change location data (segmentMember data valid segment) _ _ = _
    change segmentMember data valid segment = member at owner
    simp [location, endpoint, owner]

theorem interior_cut (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size) (cut : Fin data.points.size)
    (represented : representedLocation (model data valid) (.interior member cut)) :
    0 < cutParameter data member cut ∧ cutParameter data member cut < 1 := by
  obtain ⟨owner, t, index, same, locationValid⟩ := represented_decomposition data valid _ represented
  by_cases atStart : t = 0
  · simp [location, atStart] at same
  by_cases atEnd : t = 1
  · simp [location, atEnd] at same
  simp only [location, atStart, atEnd, ↓reduceIte] at same
  cases same
  have owned := locationValid.2.2
  simp only [atStart, atEnd, ↓reduceIte] at owned
  have hp := points_valid data valid cut
  simp only [PointValid, owned.1] at hp
  dsimp [cutParameter]
  exact_mod_cast And.intro hp.2.2.2.1 hp.2.2.2.2.1

theorem support_normalized (data : Compiled) (valid : PartitionValid data)
    (i : Fin data.source.supports.size)
    (inclined : (supports data valid i).kind = .roller ∨ (supports data valid i).kind = .guided) :
    (supports data valid i).cosine^2 + (supports data valid i).sine^2 = 1 := by
  have semantic := support_semantics data valid i
  have kind : data.source.supports[i.val]!.kind = 2 := by
    by_cases pin : data.source.supports[i.val]!.kind = 0
    · simp [supports, pin] at inclined
    by_cases fixed : data.source.supports[i.val]!.kind = 1
    · simp [supports, fixed] at inclined
    have := semantic.2.1
    omega
  rcases semantic.2.2 kind with angle | angle | angle | angle
  all_goals norm_num [supports, angle]

/-- The full existing presegmented-frame contract follows for the original
    source member interpretation, including exact boundary representation. -/
theorem exact_contract (data : Compiled) (valid : PartitionValid data) :
    ExactContract (model data valid) (actions data valid) (supports data valid) (cutParameter data)
      (fun member => (memberLength data.source member.val : ℝ))
      (fun member => (data.source.members[member.val]!.EA : ℝ))
      (fun member => (data.source.members[member.val]!.EI : ℝ)) := by
  refine {
    ownership := ownership data valid
    ordered := ?_
    coverage := coverage data valid
    disjointInteriors := ?_
    canonicalLocations := canonical_locations data valid
    memberEnds := member_ends data valid
    interiorCuts := interior_cut data valid
    actionLocations := ?_
    supportLocations := ?_
    orientationNormalized := ?_
    supportNormalized := support_normalized data valid
    positiveMember := ?_
    segmentLengthMatches := ?_
    segmentPropertiesMatch := (Geometry.correspondence data valid).properties
    positiveSpring := ?_ }
  · intro segment
    rw [left_parameter, right_parameter]
    rcases segments_valid data valid segment with ⟨_, _, _, lo, ordered, hi, _⟩
    exact_mod_cast And.intro lo (And.intro ordered hi)
  · intro a b different owner
    rw [left_parameter, right_parameter, left_parameter, right_parameter]
    have same : data.segments[a.val]!.member = data.segments[b.val]!.member := congrArg Fin.val owner
    exact_mod_cast (boundaries_valid data valid).1 a b different same
  · intro action
    exact represented_of_check data valid _ _ _ ((boundaries_valid data valid).2.2 action)
  · intro support
    exact represented_of_check data valid _ _ _ ((boundaries_valid data valid).2.1 support)
  · intro member
    change (memberCosine data.source member.val : ℝ)^2 + (memberSine data.source member.val : ℝ)^2 = 1
    exact_mod_cast (Geometry.member_properties data valid member).2.2
  · intro member
    have length := (members_bounded data valid member).2.2
    obtain ⟨EA, EI, _⟩ := Geometry.member_properties data valid member
    exact_mod_cast And.intro length (And.intro EA EI)
  · intro segment
    rw [left_parameter, right_parameter]
    have length := (segments_valid data valid segment).2.2.2.2.2.2.1
    dsimp only [model, segmentMember]
    exact_mod_cast length
  · intro side direction stiffness _ spring
    simp [rigid, directionLaw, rigidConnection] at spring

end
end RationalFrame.Contract
