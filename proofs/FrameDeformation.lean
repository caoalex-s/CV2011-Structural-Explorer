import FrameAssembly

/-!
Deformation coordinates for exact presegmented members. The three member
coordinates are axial extension and the two rotations relative to the chord.
Connection slips remain separate coordinates so a free pure-slip mechanism is
not silently discarded.
-/
open FrameInterfaces FrameEnergy FrameAssemblyModel FrameAssembly

namespace FrameDeformation
noncomputable section

/-- The homogeneous local member energy depends on these three quantities. -/
def memberDeformation (d : LocalDofs) (L : ℝ) : Fin 3 → ℝ :=
  ![d 3-d 0, relativeRotationLeft d L, relativeRotationRight d L]

/-- Linear map from local end movements to extension and chord rotations. -/
def memberDeformationLinear (L : ℝ) : LocalDofs →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := fun d => memberDeformation d L
  map_add' := by
    intro d e
    funext i
    fin_cases i <;> simp [memberDeformation, relativeRotationLeft, relativeRotationRight,
      Pi.add_apply] <;> ring
  map_smul' := by
    intro a d
    funext i
    fin_cases i <;> simp [memberDeformation, relativeRotationLeft, relativeRotationRight,
      Pi.smul_apply, smul_eq_mul] <;> ring

set_option maxHeartbeats 4000000 in
/-- First variation of one homogeneous member energy along prescribed local
end movements. The distributed load enters separately through its work. -/
theorem member_energy_directional_derivative (d e : LocalDofs) (L EA EI : ℝ)
    (hL : L ≠ 0) :
    HasDerivAt (fun t : ℝ => energy (fun i => d i + t*e i) L EA EI)
      (∑ i : Fin 6, e i * (∑ j : Fin 6, LocalFrameFields.stiffness L EA EI i j * d j)) 0 := by
  let slope := ∑ i : Fin 6, e i * (∑ j : Fin 6, LocalFrameFields.stiffness L EA EI i j * d j)
  have hpoly (t : ℝ) : energy (fun i => d i + t*e i) L EA EI =
      energy d L EA EI + t*slope + t^2*energy e L EA EI := by
    simp [energy, relativeRotationLeft, relativeRotationRight, slope,
      LocalFrameFields.stiffness, Fin.sum_univ_succ]
    field_simp
    ring
  have h := ((hasDerivAt_const (0 : ℝ) (energy d L EA EI)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const slope)).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (energy e L EA EI))
  convert h using 1
  · funext t
    exact hpoly t
  · simp [slope]

/-- A model-derived slip varies linearly along any coordinate direction. -/
theorem slip_directional_derivative (model : Model nodes members cuts segments)
    (q variation : Coordinate model → ℝ) (side : MemberEnd members) (direction : Fin 3) :
    HasDerivAt (fun t : ℝ => slipValue model (q + t • variation) side direction)
      (slipValue model variation side direction) 0 := by
  have h := (hasDerivAt_const (0 : ℝ) (slipValue model q side direction)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (slipValue model variation side direction))
  convert h using 1
  · funext t
    have heq := (slipLinear model side direction).map_add q (t • variation)
    have hscale := (slipLinear model side direction).map_smul t variation
    change slipValue model (q + t • variation) side direction =
      slipValue model q side direction + slipValue model (t • variation) side direction at heq
    change slipValue model (t • variation) side direction =
      t * slipValue model variation side direction at hscale
    rw [heq, hscale]
  · simp

/-- The selected segment movement component has the corresponding B-map
directional derivative. -/
theorem segment_directional_derivative (model : Model nodes members cuts segments)
    (q variation : Coordinate model → ℝ) (segment : Fin segments) (i : Fin 6) :
    HasDerivAt (fun t : ℝ => segmentDofs model (q + t • variation) segment i)
      (segmentDofs model variation segment i) 0 := by
  have h := (hasDerivAt_const (0 : ℝ) (segmentDofs model q segment i)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (segmentDofs model variation segment i))
  convert h using 1
  · funext t
    rw [segment_dofs_add, segment_dofs_smul]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp

/-- The three rigid motions produce no axial extension or chord-relative rotation. -/
theorem rigid_deformation_zero (A B omega L : ℝ) (hL : L ≠ 0) :
    memberDeformation (rigidMotion A B omega L) L = 0 := by
  funext i
  fin_cases i <;> simp [memberDeformation, rigidMotion, relativeRotationLeft, relativeRotationRight]
  all_goals field_simp

/-- Zero member strain energy is equivalent to zero member deformation. -/
theorem member_energy_zero_iff_deformation (d : LocalDofs) (L EA EI : ℝ)
    (hL : 0 < L) (hEA : 0 < EA) (hEI : 0 < EI) :
    energy d L EA EI = 0 ↔ memberDeformation d L = 0 := by
  constructor
  · intro h
    obtain ⟨A, B, omega, rfl⟩ := energy_zero_rigid d L EA EI hL hEA hEI h
    exact rigid_deformation_zero A B omega L (ne_of_gt hL)
  · intro h
    have haxial : d 3 - d 0 = 0 := by simpa [memberDeformation] using congrFun h 0
    have hleft : relativeRotationLeft d L = 0 := by simpa [memberDeformation] using congrFun h 1
    have hright : relativeRotationRight d L = 0 := by simpa [memberDeformation] using congrFun h 2
    simp [energy, haxial, hleft, hright]

/-- Segment deformation is formed from the actual model-derived B map. -/
def segmentDeformation (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (segment : Fin segments) : Fin 3 → ℝ :=
  memberDeformation (segmentDofs model q segment) (model.segmentLength segment)

/-- A spring direction is an actual represented member-side end with a finite
spring law. Its positivity is supplied by the exact physical input contract. -/
def SpringIndex (model : Model nodes members cuts segments) :=
  { pair : MemberEnd members × Fin 3 // activeEnd model pair.1 ∧
    ∃ stiffness, directionLaw (endConnection model pair.1) pair.2 = .spring stiffness }

/-- D contains every segment deformation and every finite spring slip; free
slips remain in q and may therefore appear in the kernel. -/
def deformationMap (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) : Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ
  | .inl (segment, component) => segmentDeformation model q segment component
  | .inr spring => slipValue model q spring.val.1 spring.val.2

/-- D is a linear map built from actual segment B maps and spring slip maps. -/
def deformationLinear (model : Model nodes members cuts segments) :
    (Coordinate model → ℝ) →ₗ[ℝ] (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ) where
  toFun := deformationMap model
  map_add' := by
    intro q r
    funext index
    cases index with
    | inl memberIndex =>
        rcases memberIndex with ⟨segment, component⟩
        have h := (memberDeformationLinear (model.segmentLength segment)).map_add
          (segmentDofs model q segment) (segmentDofs model r segment)
        have hp := congrFun h component
        simpa [deformationMap, segmentDeformation, memberDeformationLinear,
          segment_dofs_add, Pi.add_apply] using hp
    | inr spring =>
        simpa [deformationMap, slipLinear, Pi.add_apply] using
          (slipLinear model spring.val.1 spring.val.2).map_add q r
  map_smul' := by
    intro a q
    funext index
    cases index with
    | inl memberIndex =>
        rcases memberIndex with ⟨segment, component⟩
        have h := (memberDeformationLinear (model.segmentLength segment)).map_smul a
          (segmentDofs model q segment)
        have hp := congrFun h component
        change memberDeformation (a • segmentDofs model q segment) (model.segmentLength segment) component =
          a * memberDeformation (segmentDofs model q segment) (model.segmentLength segment) component at hp
        change memberDeformation (segmentDofs model (a • q) segment) (model.segmentLength segment) component =
          a * memberDeformation (segmentDofs model q segment) (model.segmentLength segment) component
        rw [segment_dofs_smul]
        exact hp
    | inr spring =>
        have h := (slipLinear model spring.val.1 spring.val.2).map_smul a q
        change slipValue model (a • q) spring.val.1 spring.val.2 =
          a * slipValue model q spring.val.1 spring.val.2 at h
        exact h

/-- If all segment and spring deformations vanish, the assembled energy
vanishes. Free slips contribute no spring energy and remain part of the model. -/
theorem deformation_zero_implies_energy_zero (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q : Coordinate model → ℝ) (hzero : deformationMap model q = 0) :
    totalEnergy model q = 0 := by
  have hsegments := contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI hcontract
  have hmember (segment : Fin segments) :
      energy (segmentDofs model q segment) (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment) = 0 := by
    obtain ⟨hL, hEA, hEI⟩ := hsegments segment
    apply (member_energy_zero_iff_deformation _ _ _ _ hL hEA hEI).mpr
    funext component
    have h := congrFun hzero (.inl (segment, component))
    simpa [deformationMap, segmentDeformation] using h
  have hspring (member : Fin members) (ending : Bool) (direction : Fin 3) :
      springStiffness (directionLaw (endConnection model (member, ending)) direction) *
        (slipValue model q (member, ending) direction)^2 / 2 = 0 := by
    classical
    by_cases hactive : activeEnd model (member, ending)
    · cases hlaw : directionLaw (endConnection model (member, ending)) direction with
      | rigid => simp [springStiffness]
      | released => simp [springStiffness]
      | spring k =>
          have hv := congrFun hzero (.inr ⟨((member, ending), direction), hactive, k, hlaw⟩)
          have hslip : slipValue model q (member, ending) direction = 0 := by
            simpa [deformationMap] using hv
          simp [springStiffness, hslip]
    · have hslip : slipValue model q (member, ending) direction = 0 := by
        simp [slipValue, hasSlip, hactive]
      simp [hslip]
  unfold totalEnergy springEnergy
  simp [hmember, hspring]

/-- Under the exact positive-spring contract, zero energy forces all member
and spring deformations to vanish. This does not suppress free-slip motions. -/
theorem energy_zero_implies_deformation_zero (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q : Coordinate model → ℝ) (hzero : totalEnergy model q = 0) :
    deformationMap model q = 0 := by
  classical
  have hsegments := contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI hcontract
  have hsprings := contract_nonnegative_springs model actions supports cutParameter memberLength memberEA memberEI hcontract
  have hmemberNonnegative (segment : Fin segments) :
      0 ≤ energy (segmentDofs model q segment) (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment) := by
    obtain ⟨hL, hEA, hEI⟩ := hsegments segment
    exact energy_nonnegative _ _ _ _ hL hEA hEI
  have hmemberSumNonnegative : 0 ≤ ∑ segment : Fin segments,
      energy (segmentDofs model q segment) (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment) :=
    Finset.sum_nonneg (fun segment _ => hmemberNonnegative segment)
  have hspringNonnegative := spring_energy_nonnegative model q hsprings
  have hmemberSum : (∑ segment : Fin segments,
      energy (segmentDofs model q segment) (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment)) = 0 := by
    unfold totalEnergy at hzero
    linarith
  have hspringSum : springEnergy model q = 0 := by
    unfold totalEnergy at hzero
    linarith
  have hspringTerm (member : Fin members) (ending : Bool) (direction : Fin 3) :
      springStiffness (directionLaw (endConnection model (member, ending)) direction) *
        (slipValue model q (member, ending) direction)^2 / 2 = 0 := by
    let term := fun (m : Fin members) (e : Bool) (i : Fin 3) =>
      springStiffness (directionLaw (endConnection model (m, e)) i) *
        (slipValue model q (m, e) i)^2 / 2
    have htermNonnegative (m : Fin members) (e : Bool) (i : Fin 3) : 0 ≤ term m e i := by
      exact div_nonneg (mul_nonneg (hsprings m e i) (sq_nonneg _)) (by norm_num)
    have houter : (∑ m : Fin members, ∑ e : Bool, ∑ i : Fin 3, term m e i) = 0 := by
      simpa [springEnergy, term] using hspringSum
    have hmid : (∑ e : Bool, ∑ i : Fin 3, term member e i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => Finset.sum_nonneg
        (fun e _ => Finset.sum_nonneg (fun i _ => htermNonnegative m e i)))).mp houter
        member (Finset.mem_univ member)
    have hinner : (∑ i : Fin 3, term member ending i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => Finset.sum_nonneg
        (fun i _ => htermNonnegative member e i))).mp hmid ending (Finset.mem_univ ending)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => htermNonnegative member ending i)).mp
      hinner direction (Finset.mem_univ direction)
  funext index
  cases index with
  | inl memberIndex =>
      rcases memberIndex with ⟨segment, component⟩
      have hlocal := (Finset.sum_eq_zero_iff_of_nonneg
        (fun segment _ => hmemberNonnegative segment)).mp hmemberSum segment (Finset.mem_univ segment)
      obtain ⟨hL, hEA, hEI⟩ := hsegments segment
      have hdeformation := (member_energy_zero_iff_deformation _ _ _ _ hL hEA hEI).mp hlocal
      simpa [deformationMap, segmentDeformation] using congrFun hdeformation component
  | inr spring =>
      obtain ⟨k, hlaw⟩ := spring.property.2
      have hk := hcontract.positiveSpring spring.val.1 spring.val.2 k spring.property.1 hlaw
      have hterm := hspringTerm spring.val.1.1 spring.val.1.2 spring.val.2
      rw [hlaw] at hterm
      have hslip : slipValue model q spring.val.1 spring.val.2 = 0 := by
        apply (FrameTransform.spring_energy_zero_iff k _ hk).mp
        simpa [springStiffness] using hterm
      simpa [deformationMap] using hslip

/-- The actual encoded deformation map has exactly the zero-energy motions. -/
theorem energy_zero_iff_deformation_zero (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q : Coordinate model → ℝ) : totalEnergy model q = 0 ↔ deformationMap model q = 0 :=
  ⟨energy_zero_implies_deformation_zero model actions supports cutParameter memberLength memberEA memberEI hcontract q,
   deformation_zero_implies_energy_zero model actions supports cutParameter memberLength memberEA memberEI hcontract q⟩

/-- The kernel of the actual assembled stiffness work, expressed without
choosing or inverting a coordinate matrix. -/
def stiffnessNull (model : Model nodes members cuts segments) (q : Coordinate model → ℝ) : Prop :=
  ∀ variation, stiffnessWork model q variation = 0

/-- The assembled stiffness kernel is exactly the kernel of the actual member
and spring deformation map, under the complete exact input contract. -/
theorem stiffness_null_iff_deformation_zero (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q : Coordinate model → ℝ) : stiffnessNull model q ↔ deformationMap model q = 0 := by
  have hsegments := contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI hcontract
  constructor
  · intro hnull
    have hwork := hnull q
    rw [stiffness_work_energy model q hsegments] at hwork
    have henergy : totalEnergy model q = 0 := by linarith
    exact energy_zero_implies_deformation_zero model actions supports cutParameter memberLength memberEA memberEI hcontract q henergy
  · intro hzero variation
    have hrow (segment : Fin segments) (i : Fin 6) :
        (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
          (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model q segment j) = 0 := by
      obtain ⟨hL, hEA, hEI⟩ := hsegments segment
      have hdeformation : memberDeformation (segmentDofs model q segment) (model.segmentLength segment) = 0 := by
        funext component
        simpa [deformationMap, segmentDeformation] using congrFun hzero (.inl (segment, component))
      have henergy := (member_energy_zero_iff_deformation _ _ _ _ hL hEA hEI).mpr hdeformation
      obtain ⟨A, B, omega, hrigid⟩ := energy_zero_rigid _ _ _ _ hL hEA hEI henergy
      rw [hrigid]
      exact rigid_stiffness_zero A B omega _ _ _ (ne_of_gt hL) i
    have hspring (member : Fin members) (ending : Bool) (direction : Fin 3) :
        springStiffness (directionLaw (endConnection model (member, ending)) direction) *
          slipValue model q (member, ending) direction * slipValue model variation (member, ending) direction = 0 := by
      classical
      by_cases hactive : activeEnd model (member, ending)
      · cases hlaw : directionLaw (endConnection model (member, ending)) direction with
        | rigid => simp [springStiffness]
        | released => simp [springStiffness]
        | spring k =>
            have hv := congrFun hzero (.inr ⟨((member, ending), direction), hactive, k, hlaw⟩)
            have hslip : slipValue model q (member, ending) direction = 0 := by
              simpa [deformationMap] using hv
            simp [springStiffness, hslip]
      · have hslip : slipValue model q (member, ending) direction = 0 := by
          simp [slipValue, hasSlip, hactive]
        simp [hslip]
    unfold stiffnessWork internalVirtualWork
    simp [hrow, hspring]

/-- First variation of the actual assembled potential, including all finite
springs and point actions on their selected sides. -/
theorem potential_directional_derivative (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (q variation : Coordinate model → ℝ) (hsegments : positiveSegments model) :
    HasDerivAt (fun t : ℝ => potential model actions (q + t • variation))
      (residualWork model actions q variation) 0 := by
  have hmembers : HasDerivAt (fun t : ℝ => ∑ segment : Fin segments,
      energy (segmentDofs model (q + t • variation) segment) (model.segmentLength segment)
        (model.segmentEA segment) (model.segmentEI segment))
      (∑ segment : Fin segments, ∑ i : Fin 6, segmentDofs model variation segment i *
        (∑ j : Fin 6, LocalFrameFields.stiffness (model.segmentLength segment)
          (model.segmentEA segment) (model.segmentEI segment) i j * segmentDofs model q segment j)) 0 := by
    apply HasDerivAt.sum
    intro segment _
    have h := member_energy_directional_derivative (segmentDofs model q segment)
      (segmentDofs model variation segment) (model.segmentLength segment)
      (model.segmentEA segment) (model.segmentEI segment) (ne_of_gt (hsegments segment).1)
    convert h using 1
    funext t
    congr 1
    funext i
    rw [segment_dofs_add, segment_dofs_smul]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsprings : HasDerivAt (fun t : ℝ => springEnergy model (q + t • variation))
      (∑ member : Fin members, ∑ ending : Bool, ∑ direction : Fin 3,
        let side := (member, ending)
        let k := springStiffness (directionLaw (endConnection model side) direction)
        k * slipValue model q side direction * slipValue model variation side direction) 0 := by
    unfold springEnergy
    apply HasDerivAt.sum
    intro member _
    apply HasDerivAt.sum
    intro ending _
    apply HasDerivAt.sum
    intro direction _
    let side := (member, ending)
    let k := springStiffness (directionLaw (endConnection model side) direction)
    have h := ((slip_directional_derivative model q variation side direction).pow 2).const_mul (k/2)
    convert h using 1
    · funext t
      dsimp [side, k]
      ring
    · simp [side, k]
      ring
  have hexternal : HasDerivAt (fun t : ℝ => externalWork model actions (q + t • variation))
      (externalWork model actions variation) 0 := by
    let F := externalFunctional model actions
    have h := (hasDerivAt_const (0 : ℝ) (F q)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (F variation))
    convert h using 1
    · funext t
      rw [← external_functional_apply model actions]
      change F (q + t • variation) = F q + t * F variation
      rw [map_add, map_smul]
      rfl
    · simp [F, external_functional_apply]
  have h := (hmembers.add hsprings).sub hexternal
  simpa [potential, totalEnergy, residualWork, internalVirtualWork] using h

/-- A deformation-free admissible motion is a mechanism exactly when nonzero. -/
def mechanism (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) (q : Coordinate model → ℝ) : Prop :=
  q ≠ 0 ∧ admissible model supports q ∧ deformationMap model q = 0

end
end FrameDeformation
