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

end
end RationalFrame.Constraints
