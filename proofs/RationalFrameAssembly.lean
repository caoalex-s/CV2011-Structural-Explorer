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
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, hs, _, haxis, _, _, hends, _⟩
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

/-- Distinct endpoints make the axis permutation invertible on its six
    incident coordinates. Coordinates elsewhere have no local preimage. -/
theorem localAt_eq (segment : Segment) (different : segment.a ≠ segment.b)
    (row : Nat) (i : Fin 6) :
    localAt segment row = some i ↔ globalIndex segment i = row := by
  have directions : row % 3 = 0 ∨ row % 3 = 1 ∨ row % 3 = 2 := by omega
  rcases directions with direction | direction | direction
  all_goals
    fin_cases i <;> by_cases horizontal : segment.cosine = 0 <;>
      by_cases atStart : row / 3 = segment.a <;>
      by_cases atEnd : row / 3 = segment.b <;>
      norm_num [localAt, globalIndex, horizontal, direction, atStart, atEnd] <;>
      (try simp [different, Ne.symm different]) <;> omega

theorem mapping_at (segment : Segment) (different : segment.a ≠ segment.b)
    (row : Nat) (i : Fin 6) :
    mapping segment i row =
      if localAt segment row = some i then coordinateSign segment i else 0 := by
  simp only [mapping, localAt_eq segment different]

/-- A sparse assembled row is precisely the finite sum of the actual local
    coordinate projections, including the zero contribution off the member. -/
theorem projection_sum (segment : Segment) (different : segment.a ≠ segment.b)
    (row : Nat) (values : Fin 6 → ℝ) :
    (∑ i : Fin 6, (mapping segment i row : ℝ) * values i) =
      match localAt segment row with
      | none => 0
      | some i => (coordinateSign segment i : ℝ) * values i := by
  simp_rw [mapping_at segment different]
  cases found : localAt segment row with
  | none => simp
  | some selected => simp [apply_ite, eq_comm]

theorem segment_stiffness_sum (segment : Segment) (different : segment.a ≠ segment.b)
    (row column : Nat) :
    (segmentStiffnessEntry segment row column : ℝ) =
      ∑ i : Fin 6, (mapping segment i row : ℝ) *
        (∑ j : Fin 6, (localStiffness segment i j : ℝ) * (mapping segment j column : ℝ)) := by
  have columnSum (i : Fin 6) :
      (∑ j : Fin 6, (localStiffness segment i j : ℝ) * (mapping segment j column : ℝ)) =
      match localAt segment column with
      | none => 0
      | some j => (coordinateSign segment j : ℝ) * (localStiffness segment i j : ℝ) := by
    simpa only [mul_comm] using projection_sum segment different column
      (fun j => (localStiffness segment i j : ℝ))
  simp_rw [columnSum]
  rw [projection_sum segment different]
  cases hr : localAt segment row <;> cases hc : localAt segment column <;>
    simp [segmentStiffnessEntry, hr, hc] <;> ring

theorem segment_force_sum (segment : Segment) (different : segment.a ≠ segment.b) (row : Nat) :
    (segmentForceEntry segment row : ℝ) =
      ∑ i : Fin 6, (mapping segment i row : ℝ) * (localForce segment i : ℝ) := by
  rw [projection_sum segment different]
  cases found : localAt segment row <;> simp [segmentForceEntry, found]

theorem basis_motion (data : Compiled) (valid : PartitionValid data) (row : Fin data.dofs) :
    FrameAssembly.coordinateBasis (model data valid) (coordinateEquiv data valid row) =
      motion data valid (fun i => if i.val = row.val then 1 else 0) := by
  funext coordinate
  obtain ⟨i, rfl⟩ := (coordinateEquiv data valid).surjective coordinate
  rw [motion_coordinate]
  simp [FrameAssembly.coordinateBasis, Fin.ext_iff]

theorem segment_basis (data : Compiled) (valid : PartitionValid data)
    (segment : Fin data.segments.size) (row : Fin data.dofs) (i : Fin 6) :
    segmentDofs (model data valid)
      (FrameAssembly.coordinateBasis (model data valid) (coordinateEquiv data valid row)) segment i =
      (mapping data.segments[segment.val]! i row.val : ℝ) := by
  rw [basis_motion, segment_dofs data valid (fun j => if j = row.val then 1 else 0)]
  by_cases incident : globalIndex data.segments[segment.val]! i = row.val
  · simp [mapping, incident]
  · simp [mapping, incident]

theorem stiffness_coefficient (data : Compiled) (valid : PartitionValid data)
    (segment : Fin data.segments.size) (i j : Fin 6) :
    LocalFrameFields.stiffness ((model data valid).segmentLength segment)
      ((model data valid).segmentEA segment) ((model data valid).segmentEI segment) i j =
      (localStiffness data.segments[segment.val]! i j : ℝ) := by
  exact (Fields.stiffness_cast _ i j).symm

/-- Every computed matrix entry is the actual model's bilinear work on its
    coordinate bases. The source-derived original-member interpretation is
    fixed throughout; neither side accepts an independently supplied K. -/
theorem stiffness_entry (data : Compiled) (valid : PartitionValid data)
    (row column : Fin data.dofs) :
    (RationalFrame.stiffnessEntry data row.val column.val : ℝ) =
      FrameAssembly.stiffnessEntry (model data valid)
        (coordinateEquiv data valid row) (coordinateEquiv data valid column) := by
  unfold FrameAssembly.stiffnessEntry FrameAssembly.stiffnessWork FrameAssembly.internalVirtualWork
  simp only [segment_basis, stiffness_coefficient]
  have zeroSlip (q : Coordinate (model data valid) → ℝ)
      (side : MemberEnd data.source.members.size) (direction : Fin 3) :
      slipValue (model data valid) q side direction = 0 := by
    simp [slipValue, no_slip]
  simp only [zeroSlip, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [RationalFrame.stiffnessEntry, sumSegments, Algebra.sumFin_eq_sum, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro segment _
  exact segment_stiffness_sum _ (segment_axes data valid segment).2.2.2 row.val column.val

theorem load_coefficient (data : Compiled) (valid : PartitionValid data)
    (segment : Fin data.segments.size) (i : Fin 6) :
    segmentLoad (model data valid) segment i = (localForce data.segments[segment.val]! i : ℝ) := by
  obtain ⟨hc, hs, _, _⟩ := segment_axes data valid segment
  simp only [segmentLoad, model, segmentMember]
  rw [← hc, ← hs]
  simpa only [Rat.cast_mul] using (Fields.force_cast data.segments[segment.val]! i).symm

/-- Direct source actions act on the same owned point as the represented
    physical action. A distributed source has no additional point action. -/
theorem point_action_work (data : Compiled) (valid : PartitionValid data)
    (loadIndex : Fin data.source.loads.size) (values : Nat → ℝ) :
    let load := data.source.loads[loadIndex.val]!
    let point := locationIndex data load.member load.t
    pointActionWork (model data valid) (actions data valid loadIndex)
      (motion data valid (fun i => values i.val)) =
      if load.kind = 0 then (load.fx : ℝ) * values (3*point) + (load.fy : ℝ) * values (3*point+1)
      else if load.kind = 1 then (load.mz : ℝ) * values (3*point+2) else 0 := by
  dsimp only
  simp only [pointActionWork, actions, side_reference]
  rw [location_point data valid _ _ _ (loads_valid data valid loadIndex)]
  simp only [work, reference_motion]
  split_ifs <;> simp_all

theorem point_force_basis (data : Compiled) (load : Load) (row : Nat) :
    (pointForceEntry data load row : ℝ) =
      if load.kind = 0 then
        (load.fx : ℝ) * (if row = 3*locationIndex data load.member load.t then 1 else 0) +
        (load.fy : ℝ) * (if row = 3*locationIndex data load.member load.t+1 then 1 else 0)
      else if load.kind = 1 then
        (load.mz : ℝ) * (if row = 3*locationIndex data load.member load.t+2 then 1 else 0) else 0 := by
  have zeroDirection : row = 3*locationIndex data load.member load.t ↔
      row / 3 = locationIndex data load.member load.t ∧ row % 3 = 0 := by omega
  have oneDirection : row = 3*locationIndex data load.member load.t+1 ↔
      row / 3 = locationIndex data load.member load.t ∧ row % 3 = 1 := by omega
  have rotationDirection : row = 3*locationIndex data load.member load.t+2 ↔
      row / 3 = locationIndex data load.member load.t ∧ row % 3 = 2 := by omega
  simp only [zeroDirection, oneDirection, rotationDirection, pointForceEntry]
  split_ifs <;> simp_all

/-- Consistent distributed loads and all direct actions assemble to the
    actual external-work functional, retaining overlaps and ownership. -/
theorem force_entry (data : Compiled) (valid : PartitionValid data) (row : Fin data.dofs) :
    (RationalFrame.forceEntry data row.val : ℝ) =
      FrameAssembly.forceEntry (model data valid) (actions data valid) (coordinateEquiv data valid row) := by
  unfold FrameAssembly.forceEntry FrameAssembly.externalWork
  simp only [segment_basis, load_coefficient]
  simp only [RationalFrame.forceEntry, sumSegments, Algebra.sumFin_eq_sum, Rat.cast_add, Rat.cast_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro segment _
    simpa only [mul_comm] using segment_force_sum data.segments[segment.val]!
      (segment_axes data valid segment).2.2.2 row.val
  · apply Finset.sum_congr rfl
    intro loadIndex _
    rw [basis_motion, point_action_work data valid loadIndex (fun i => if i = row.val then 1 else 0)]
    simpa only [eq_comm] using point_force_basis data data.source.loads[loadIndex.val]! row.val

end
end RationalFrame.Assembly
