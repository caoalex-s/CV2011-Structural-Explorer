import FrameAssemblyModel

/-!
Assembly from the exact presegmented input. The local terms use the previously
proved element energy, consistent loads and end actions. The definitions keep
all member-side slips, including free directions, in the displacement space.
-/
open FrameInterfaces FrameEnergy FrameVirtualWork FrameAssemblyModel

namespace FrameAssembly
noncomputable section

/-- The positive spring modulus is retained only for a spring connection. -/
def springStiffness (law : EndLaw) : ℝ :=
  match law with
  | .spring stiffness => stiffness
  | _ => 0

/-- Every nonrigid coordinate remains present even when its stiffness is zero. -/
def springEnergy (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) : ℝ :=
  ∑ member : Fin members, ∑ endSide : Bool, ∑ direction : Fin 3,
    let side := (member, endSide)
    let k := springStiffness (directionLaw (endConnection model side) direction)
    k * (slipValue model q side direction)^2 / 2

/-- Sum of homogeneous member strain energy and finite connection springs. -/
def totalEnergy (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) : ℝ :=
  (∑ segment : Fin segments,
    energy (segmentDofs model q segment) (model.segmentLength segment)
      (model.segmentEA segment) (model.segmentEI segment)) + springEnergy model q

/-- External virtual work includes distributed loads and point actions on their
selected member sides. Support reactions are handled separately as constraints. -/
def externalWork (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts) (q : Coordinate model → ℝ) : ℝ :=
  (∑ segment : Fin segments, ∑ i : Fin 6,
    segmentLoad model segment i * segmentDofs model q segment i) +
  ∑ action : Fin actionCount, pointActionWork model (actions action) q

/-- Global dead-load potential on the actual model coordinates. -/
def potential (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts) (q : Coordinate model → ℝ) : ℝ :=
  totalEnergy model q - externalWork model actions q

/-- The member contribution is the virtual work of exact field-derived end
actions; spring work acts on the same local relative movements as the engine. -/
def internalVirtualWork (model : Model nodes members cuts segments)
    (q variation : Coordinate model → ℝ) : ℝ :=
  (∑ segment : Fin segments, ∑ i : Fin 6,
    segmentDofs model variation segment i *
      (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model q segment j)) +
  ∑ member : Fin members, ∑ endSide : Bool, ∑ direction : Fin 3,
    let side := (member, endSide)
    let k := springStiffness (directionLaw (endConnection model side) direction)
    k * slipValue model q side direction * slipValue model variation side direction

/-- The global bilinear stiffness is assembled from Bᵀ K B and Sᵀ k S,
where B and S are derived from the model's end laws and segment locations. -/
def stiffnessWork (model : Model nodes members cuts segments)
    (q variation : Coordinate model → ℝ) : ℝ :=
  internalVirtualWork model q variation

/-- Residual virtual work combines the actual local Kd−f and side-owned actions. -/
def residualWork (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (q variation : Coordinate model → ℝ) : ℝ :=
  internalVirtualWork model q variation - externalWork model actions variation

/-- Each finite support contributes its actual selected blocked directions;
duplicate directions are retained, not assumed independent. -/
def admissible (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (q : Coordinate model → ℝ) : Prop :=
  ∀ support : Fin supportCount, ∀ direction ∈ supportDirections (supports support),
    supportRow model (supports support) direction q = 0

/-- Exact constrained stationarity is a virtual-work statement on all motions
satisfying the actual support rows. -/
def equilibrium (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (q : Coordinate model → ℝ) : Prop :=
  admissible model supports q ∧
    ∀ variation, admissible model supports variation → residualWork model actions q variation = 0


/-- The encoded segment properties satisfy the hypotheses of the local proof. -/
def positiveSegments (model : Model nodes members cuts segments) : Prop :=
  ∀ segment, 0 < model.segmentLength segment ∧
    0 < model.segmentEA segment ∧ 0 < model.segmentEI segment

/-- Free and rigid directions have zero spring modulus. A finite spring must
have nonnegative modulus here; physical spring inputs require strict positivity. -/
def nonnegativeSprings (model : Model nodes members cuts segments) : Prop :=
  ∀ member endSide direction,
    0 ≤ springStiffness (directionLaw (endConnection model (member, endSide)) direction)

theorem spring_energy_nonnegative (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (h : nonnegativeSprings model) :
    0 ≤ springEnergy model q := by
  unfold springEnergy
  apply Finset.sum_nonneg
  intro member _
  apply Finset.sum_nonneg
  intro endSide _
  apply Finset.sum_nonneg
  intro direction _
  exact div_nonneg (mul_nonneg (h member endSide direction) (sq_nonneg _)) (by norm_num)

/-- Positivity is for the actual member and spring energy, including free slips. -/
theorem total_energy_nonnegative (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (hsegments : positiveSegments model)
    (hsprings : nonnegativeSprings model) : 0 ≤ totalEnergy model q := by
  unfold totalEnergy
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro segment _
    obtain ⟨hL, hEA, hEI⟩ := hsegments segment
    exact energy_nonnegative (segmentDofs model q segment) _ _ _ hL hEA hEI
  · exact spring_energy_nonnegative model q hsprings

/-- Each recovered segment has the unique loaded local fields associated with
its assembled end movements and its exact vertical affine load. -/
theorem recovered_segment_exists (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (segment : Fin segments) (h : positiveSegments model) :
    Nonempty (LocalFrameFields.SegmentSolution (segmentDofs model q segment)
      (model.segmentLength segment) (model.segmentEA segment) (model.segmentEI segment)
      ((model.member (model.segmentMember segment)).orientation.sine * model.segmentVerticalStart segment)
      ((model.member (model.segmentMember segment)).orientation.sine * model.segmentVerticalEnd segment)
      ((model.member (model.segmentMember segment)).orientation.cosine * model.segmentVerticalStart segment)
      ((model.member (model.segmentMember segment)).orientation.cosine * model.segmentVerticalEnd segment)) := by
  obtain ⟨hL, hEA, hEI⟩ := h segment
  exact LocalFrameFields.segment_solution_exists _ _ _ _ _ _ _ _ hL hEA hEI

end
end FrameAssembly
