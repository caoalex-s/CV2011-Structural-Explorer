import FrameAssemblyModel
import Mathlib.LinearAlgebra.Dual.Lemmas

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

/-- Assemble stiffness by applying the physical bilinear work to coordinate
basis vectors. These coefficients are derived from the actual B and slip maps. -/
def coordinateBasis (model : Model nodes members cuts segments) (coordinate : Coordinate model) :
    Coordinate model → ℝ := by
  classical
  exact fun index => if index = coordinate then 1 else 0

def stiffnessEntry (model : Model nodes members cuts segments)
    (row column : Coordinate model) : ℝ :=
  stiffnessWork model (coordinateBasis model column) (coordinateBasis model row)

def forceEntry (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts) (row : Coordinate model) : ℝ :=
  externalWork model actions (coordinateBasis model row)

/-- The support admissibility predicate is precisely the kernel of the
model-derived constraint map, even when support rows are repeated. -/
theorem admissible_iff_constraint_kernel (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (q : Coordinate model → ℝ) :
    admissible model supports q ↔ q ∈ LinearMap.ker (constraintMap model supports) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    funext row
    exact h row.1 _ (List.get_mem _ _)
  · intro h support direction hdirection
    obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp hdirection
    have hv := congrFun h ⟨support, ⟨index, hindex⟩⟩
    simpa [constraintMap, supportRowLinear, heq] using hv

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

/-- End actions recovered from the loaded exact segment fields. -/
def recoveredEndActions (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (segment : Fin segments) : LocalActions :=
  let orientation := (model.member (model.segmentMember segment)).orientation
  let q₀ := model.segmentVerticalStart segment
  let q₁ := model.segmentVerticalEnd segment
  LocalFrameFields.endActions (segmentDofs model q segment)
    (model.segmentLength segment) (model.segmentEA segment) (model.segmentEI segment)
    (orientation.sine*q₀) (orientation.sine*q₁)
    (orientation.cosine*q₀) (orientation.cosine*q₁)

/-- Kd−f in residual work is exactly the end action from the loaded fields,
with separate spring work and directly applied member-side point actions. -/
theorem residual_work_from_end_actions (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (q variation : Coordinate model → ℝ) (hsegments : positiveSegments model) :
    residualWork model actions q variation =
      (∑ segment : Fin segments, ∑ i : Fin 6,
        segmentDofs model variation segment i * recoveredEndActions model q segment i) +
      (∑ member : Fin members, ∑ endSide : Bool, ∑ direction : Fin 3,
        let side := (member, endSide)
        let k := springStiffness (directionLaw (endConnection model side) direction)
        k * slipValue model q side direction * slipValue model variation side direction) -
      ∑ action : Fin actionCount, pointActionWork model (actions action) variation := by
  have hsegment (segment : Fin segments) (i : Fin 6) :
      recoveredEndActions model q segment i =
        (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
          (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model q segment j) -
        segmentLoad model segment i := by
    obtain ⟨hL, hEA, hEI⟩ := hsegments segment
    exact LocalFrameFields.end_actions_from_fields _ _ _ _ _ _ _ _
      (ne_of_gt hL) (ne_of_gt hEA) (ne_of_gt hEI) i
  simp_rw [hsegment]
  unfold residualWork internalVirtualWork externalWork
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hloads : (∑ segment : Fin segments, ∑ i : Fin 6,
      segmentDofs model variation segment i * segmentLoad model segment i) =
      (∑ segment : Fin segments, ∑ i : Fin 6,
      segmentLoad model segment i * segmentDofs model variation segment i) := by
    apply Finset.sum_congr rfl
    intro segment _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hloads]
  ring

/-- A selected segment movement component, built from B. -/
def segmentCoordinateLinear (model : Model nodes members cuts segments)
    (segment : Fin segments) (i : Fin 6) : (Coordinate model → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (segmentDofsLinear model segment)

/-- Point-action work as a linear functional on its actual member side. -/
def pointActionLinear (model : Model nodes members cuts segments)
    (action : PointAction members cuts) : (Coordinate model → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : Fin 3, action.globalAction i •
    ((LinearMap.proj i).comp (sideMotionLinear model action.location))

/-- The complete distributed and point-action work as a linear functional. -/
def externalFunctional (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts) :
    (Coordinate model → ℝ) →ₗ[ℝ] ℝ :=
  (∑ segment : Fin segments, ∑ i : Fin 6,
    segmentLoad model segment i • segmentCoordinateLinear model segment i) +
  ∑ action : Fin actionCount, pointActionLinear model (actions action)

theorem external_functional_apply (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts) (variation : Coordinate model → ℝ) :
    externalFunctional model actions variation = externalWork model actions variation := by
  simp [externalFunctional, externalWork, segmentCoordinateLinear, pointActionLinear,
    pointActionWork, segmentDofsLinear, sideMotionLinear, FrameTransform.work,
    Fin.sum_univ_succ, smul_eq_mul, add_assoc]

/-- Assemble the loaded field end actions, spring slips and point actions into
the same residual functional used by constrained virtual work. -/
def residualFunctional (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts) (q : Coordinate model → ℝ) :
    (Coordinate model → ℝ) →ₗ[ℝ] ℝ :=
  (∑ segment : Fin segments, ∑ i : Fin 6,
    recoveredEndActions model q segment i • segmentCoordinateLinear model segment i) +
  (∑ member : Fin members, ∑ endSide : Bool, ∑ direction : Fin 3,
    let side := (member, endSide)
    let k := springStiffness (directionLaw (endConnection model side) direction)
    (k * slipValue model q side direction) • slipLinear model side direction) -
  ∑ action : Fin actionCount, pointActionLinear model (actions action)

/-- Its value is the model-derived residual virtual work. -/
theorem residual_functional_apply (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (q variation : Coordinate model → ℝ) (hsegments : positiveSegments model) :
    residualFunctional model actions q variation = residualWork model actions q variation := by
  rw [residual_work_from_end_actions model actions q variation hsegments]
  simp [residualFunctional, segmentCoordinateLinear, pointActionLinear, pointActionWork,
    segmentDofsLinear, sideMotionLinear, slipLinear, FrameTransform.work, Fin.sum_univ_succ,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_assoc]

/-- A linear residual annihilates the admissible motions exactly when it is
the pullback of a support-row functional. This allows dependent support rows:
the row functional need not be unique. -/
theorem admissible_reaction_dual (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (residual : Module.Dual ℝ (Coordinate model → ℝ)) :
    (∀ variation, admissible model supports variation → residual variation = 0) ↔
    ∃ reaction : Module.Dual ℝ (ConstraintIndex supports → ℝ),
      ∀ variation, residual variation = reaction (constraintMap model supports variation) := by
  let C := constraintMap model supports
  have hann : (∀ variation, admissible model supports variation → residual variation = 0) ↔
      residual ∈ (LinearMap.ker C).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro h variation hv
      exact h variation ((admissible_iff_constraint_kernel model supports variation).mpr hv)
    · intro h variation hv
      exact h variation ((admissible_iff_constraint_kernel model supports variation).mp hv)
  rw [hann, ← LinearMap.range_dualMap_eq_dualAnnihilator_ker C, LinearMap.mem_range]
  constructor
  · rintro ⟨reaction, hreaction⟩
    refine ⟨reaction, ?_⟩
    intro variation
    have h := congrArg (fun f : Module.Dual ℝ (Coordinate model → ℝ) => f variation) hreaction
    simpa [LinearMap.dualMap_apply] using h.symm
  · rintro ⟨reaction, hreaction⟩
    refine ⟨reaction, ?_⟩
    ext variation
    simpa [LinearMap.dualMap_apply] using (hreaction variation).symm

/-- Constrained equilibrium is equivalent to an aggregate support reaction
functional, with no independence assumption on the support rows. -/
theorem equilibrium_iff_support_reaction (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (q : Coordinate model → ℝ) (hsegments : positiveSegments model) :
    equilibrium model actions supports q ↔
      admissible model supports q ∧
      ∃ reaction : Module.Dual ℝ (ConstraintIndex supports → ℝ),
        ∀ variation, residualFunctional model actions q variation =
          reaction (constraintMap model supports variation) := by
  unfold equilibrium
  constructor
  · rintro ⟨hadmissible, hstationary⟩
    refine ⟨hadmissible, (admissible_reaction_dual model supports _).mp ?_⟩
    intro variation hvariation
    rw [residual_functional_apply model actions q variation hsegments]
    exact hstationary variation hvariation
  · rintro ⟨hadmissible, reaction, hreaction⟩
    refine ⟨hadmissible, ?_⟩
    have hstationary := (admissible_reaction_dual model supports _).mpr ⟨reaction, hreaction⟩
    intro variation hvariation
    rw [← residual_functional_apply model actions q variation hsegments]
    exact hstationary variation hvariation

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

/-- The exact model contract supplies positive segment properties. -/
theorem contract_positive_segments (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter memberLength memberEA memberEI) :
    positiveSegments model := by
  intro segment
  obtain ⟨hLength, hEA, hEI⟩ := h.positiveMember (model.segmentMember segment)
  obtain ⟨_, hOrder, _⟩ := h.ordered segment
  obtain ⟨hSegEA, hSegEI⟩ := h.segmentPropertiesMatch segment
  refine ⟨?_, ?_, ?_⟩
  · rw [h.segmentLengthMatches segment]
    exact mul_pos hLength (sub_pos.mpr hOrder)
  · rw [hSegEA]; exact hEA
  · rw [hSegEI]; exact hEI

/-- Physical spring inputs are strictly positive; rigid and released directions
contribute zero spring modulus. -/
theorem contract_nonnegative_springs (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter memberLength memberEA memberEI) :
    nonnegativeSprings model := by
  intro member endSide direction
  have hactive : activeEnd model (member, endSide) := by
    cases endSide with
    | false => exact (h.memberEnds member).1
    | true => exact (h.memberEnds member).2
  cases hlaw : directionLaw (endConnection model (member, endSide)) direction with
  | rigid => simp [springStiffness]
  | released => simp [springStiffness]
  | spring stiffness =>
      simp only [springStiffness]
      exact (h.positiveSpring (member, endSide) direction stiffness hactive hlaw).le

/-- Actual assembled stiffness work is symmetric because each local element
stiffness is symmetric and each spring contribution is a scalar product. -/
theorem stiffness_work_symmetric (model : Model nodes members cuts segments)
    (q variation : Coordinate model → ℝ) :
    stiffnessWork model q variation = stiffnessWork model variation q := by
  have hsegment (segment : Fin segments) :
      (∑ i : Fin 6, segmentDofs model variation segment i *
        (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
          (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model q segment j)) =
      (∑ i : Fin 6, segmentDofs model q segment i *
        (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
          (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model variation segment j)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [LocalFrameFields.stiffness_symmetric _ _ _ j i]
    ring
  unfold stiffnessWork internalVirtualWork
  rw [show (∑ segment : Fin segments, ∑ i : Fin 6, segmentDofs model variation segment i *
      (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model q segment j)) =
      (∑ segment : Fin segments, ∑ i : Fin 6, segmentDofs model q segment i *
      (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model variation segment j)) by
    exact Finset.sum_congr rfl (fun segment _ => hsegment segment)]
  congr 1
  apply Finset.sum_congr rfl
  intro member _
  apply Finset.sum_congr rfl
  intro endSide _
  apply Finset.sum_congr rfl
  intro direction _
  dsimp
  ring

/-- The entries of the stiffness matrix built from the model are symmetric. -/
theorem stiffness_entry_symmetric (model : Model nodes members cuts segments)
    (row column : Coordinate model) :
    stiffnessEntry model row column = stiffnessEntry model column row := by
  exact stiffness_work_symmetric model (coordinateBasis model column) (coordinateBasis model row)

/-- The assembled quadratic stiffness work is twice the model's energy. -/
theorem stiffness_work_energy (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (hsegments : positiveSegments model) :
    stiffnessWork model q q = 2 * totalEnergy model q := by
  have hsegment (segment : Fin segments) :
      (∑ i : Fin 6, segmentDofs model q segment i *
        (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
          (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model q segment j)) =
      2 * energy (segmentDofs model q segment) (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment) := by
    rw [energy_stiffness_identity _ _ _ _ (ne_of_gt (hsegments segment).1)]
    simp [Fin.sum_univ_succ]
    ring
  unfold stiffnessWork internalVirtualWork totalEnergy springEnergy
  simp_rw [hsegment]
  rw [mul_add]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro member _
  apply Finset.sum_congr rfl
  intro endSide _
  apply Finset.sum_congr rfl
  intro direction _
  dsimp
  ring

/-- Positive member and spring data give positive semidefinite global stiffness. -/
theorem stiffness_work_nonnegative (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (hsegments : positiveSegments model)
    (hsprings : nonnegativeSprings model) : 0 ≤ stiffnessWork model q q := by
  rw [stiffness_work_energy model q hsegments]
  exact mul_nonneg (by norm_num) (total_energy_nonnegative model q hsegments hsprings)

/-- Physical exact-input stiffness is positive semidefinite under the full
presegmentation, orientation, support and positive-spring contract. -/
theorem contract_stiffness_nonnegative (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q : Coordinate model → ℝ) : 0 ≤ stiffnessWork model q q :=
  stiffness_work_nonnegative model q
    (contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI h)
    (contract_nonnegative_springs model actions supports cutParameter memberLength memberEA memberEI h)

/-- Two support multiplier functionals give the same aggregate reaction
exactly when their difference lies in the kernel of the constraint transpose. -/
theorem reaction_gauge (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (first second : Module.Dual ℝ (ConstraintIndex supports → ℝ)) :
    (constraintMap model supports).dualMap first = (constraintMap model supports).dualMap second ↔
      first - second ∈ LinearMap.ker (constraintMap model supports).dualMap := by
  simp [LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- On a finite row space, a reaction functional has one real coefficient for
each actual row. Repeated rows may admit more than one coefficient vector. -/
theorem finite_reaction_coefficients {ι : Type} [Fintype ι] [DecidableEq ι]
    (reaction : Module.Dual ℝ (ι → ℝ)) :
    ∃ coefficients : ι → ℝ, ∀ values : ι → ℝ,
      reaction values = ∑ i : ι, coefficients i * values i := by
  refine ⟨fun i => reaction (Pi.single i 1), ?_⟩
  intro values
  calc
    reaction values = reaction (∑ i : ι, Pi.single i (values i)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ i : ι, reaction (Pi.single i (values i)) := by rw [map_sum]
    _ = ∑ i : ι, reaction (Pi.single i 1) * values i := by
      apply Finset.sum_congr rfl
      intro i _
      have hsingle : Pi.single i (values i) = values i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
        funext j
        by_cases h : j = i <;> simp [Pi.single_apply, h]
      rw [hsingle, map_smul]
      simp [smul_eq_mul, mul_comm]

/-- Under the complete exact input contract, equilibrium has an aggregate
support reaction even when constraint rows are dependent. -/
theorem contract_equilibrium_reaction (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (h : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q : Coordinate model → ℝ) :
    equilibrium model actions supports q ↔
      admissible model supports q ∧
      ∃ reaction : Module.Dual ℝ (ConstraintIndex supports → ℝ),
        ∀ variation, residualFunctional model actions q variation =
          reaction (constraintMap model supports variation) :=
  equilibrium_iff_support_reaction model actions supports q
    (contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI h)

/-- Each recovered segment has loaded local fields associated with its
assembled end movements and its exact vertical affine load. -/
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
