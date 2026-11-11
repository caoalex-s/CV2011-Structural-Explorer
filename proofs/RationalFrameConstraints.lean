import RationalFrameInterpretation

/-! Cardinal support rows constrain the actual member-side motions. Duplicate
    source restraints retain their rows while the coordinate mask takes their
    union; no independence of restraint multipliers is assumed. -/
namespace RationalFrame.Constraints
open FrameAssemblyModel FrameTransform Interpretation
noncomputable section

theorem support_motion (data : Compiled) (valid : PartitionValid data)
    (supportIndex : Fin data.source.supports.size) (values : Nat → ℝ) (direction : Fin 3) :
    let support := data.source.supports[supportIndex.val]!
    sideMotion (model data valid) (motion data valid (fun i => values i.val))
      (supports data valid supportIndex).location direction =
      values (3 * locationIndex data support.member support.t + direction.val) := by
  dsimp only
  rw [side_reference]
  simp only [supports]
  rw [location_point data valid _ _ _ (supports_valid data valid supportIndex)]
  exact reference_motion data valid values _ direction

theorem support_row (data : Compiled) (valid : PartitionValid data)
    (supportIndex : Fin data.source.supports.size) (values : Nat → ℝ) (direction : Triple) :
    let support := data.source.supports[supportIndex.val]!
    let point := locationIndex data support.member support.t
    supportRow (model data valid) (supports data valid supportIndex) direction
      (motion data valid (fun i => values i.val)) =
      direction 0 * values (3*point) + direction 1 * values (3*point+1) +
        direction 2 * values (3*point+2) := by
  simp [supportRow, work, support_motion]

theorem support_constraints (data : Compiled) (valid : PartitionValid data)
    (supportIndex : Fin data.source.supports.size) (values : Nat → ℝ) :
    let support := data.source.supports[supportIndex.val]!
    (∀ direction ∈ supportDirections (supports data valid supportIndex),
      supportRow (model data valid) (supports data valid supportIndex) direction
        (motion data valid (fun i => values i.val)) = 0) ↔
    ∀ direction : Fin 3, blocksDirection support direction.val = true →
      values (3*locationIndex data support.member support.t + direction.val) = 0 := by
  dsimp only
  simp only [support_row]
  have semantics := support_semantics data valid supportIndex
  have kinds : data.source.supports[supportIndex.val]!.kind = 0 ∨
      data.source.supports[supportIndex.val]!.kind = 1 ∨
      data.source.supports[supportIndex.val]!.kind = 2 := by
    have := semantics.2.1
    omega
  rcases kinds with pin | fixed | roller
  · simp [supportDirections, supports, pin, blocksDirection, Fin.forall_fin_succ]
  · simp [supportDirections, supports, fixed, blocksDirection, Fin.forall_fin_succ]
  · rcases semantics.2.2 roller with angle | angle | angle | angle
    all_goals simp [supportDirections, supports, roller, blocksDirection,
      angle, Fin.forall_fin_succ]

theorem blocked_exists (data : Compiled) (row : Nat) :
    blocked data row = true ↔ ∃ support : Fin data.source.supports.size,
      row / 3 = locationIndex data data.source.supports[support.val]!.member
        data.source.supports[support.val]!.t ∧
      blocksDirection data.source.supports[support.val]! (row % 3) = true := by
  simp only [blocked, Array.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨support, hmember, hpoint, hdirection⟩
    obtain ⟨index, hindex, heq⟩ := Array.mem_iff_getElem.mp hmember
    refine ⟨⟨index, hindex⟩, ?_, ?_⟩
    · simpa [getElem!_pos, heq] using hpoint
    · simpa [getElem!_pos, heq] using hdirection
  · rintro ⟨index, hpoint, hdirection⟩
    refine ⟨data.source.supports[index.val]!, ?_, hpoint, hdirection⟩
    simp [getElem!_pos]

/-- The mask covers exactly the actual constraint kernel, not merely a
    subset of sufficient fixed coordinates. This also handles repeated rows. -/
theorem admissible_iff_mask (data : Compiled) (valid : PartitionValid data) (values : Nat → ℝ) :
    FrameAssembly.admissible (model data valid) (supports data valid)
      (motion data valid (fun i => values i.val)) ↔
      ∀ i : Fin data.dofs, blocked data i.val = true → values i.val = 0 := by
  unfold FrameAssembly.admissible
  simp_rw [support_constraints]
  constructor
  · intro restraints i hi
    obtain ⟨support, hpoint, hdirection⟩ := (blocked_exists data i.val).mp hi
    have value := restraints support ⟨i.val % 3, by omega⟩ hdirection
    have reconstruct : 3 * locationIndex data data.source.supports[support.val]!.member
        data.source.supports[support.val]!.t + i.val % 3 = i.val := by omega
    simpa only [reconstruct] using value
  · intro mask support direction hdirection
    let point := locationIndex data data.source.supports[support.val]!.member
      data.source.supports[support.val]!.t
    have bound : point < data.points.size := (supports_valid data valid support).2.1
    have directionBound := direction.isLt
    let i : Fin data.dofs := ⟨3*point+direction.val, by dsimp [Compiled.dofs]; omega⟩
    apply mask i
    apply (blocked_exists data i.val).mpr
    refine ⟨support, ?_, ?_⟩
    · change (3*point+direction.val)/3 = point
      omega
    · have hmod : i.val % 3 = direction.val := by dsimp [i]; omega
      simpa only [hmod] using hdirection

end
end RationalFrame.Constraints
