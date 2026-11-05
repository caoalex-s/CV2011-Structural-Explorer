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
    rfl
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

/-- Axial force and the two end-rotation generalized stresses conjugate to
the extension and chord-relative rotations. -/
def memberBasicStress (d : LocalDofs) (L EA EI : ℝ) : Fin 3 → ℝ :=
  ![EA/L*(d 3-d 0),
    4*EI/L*(relativeRotationLeft d L + relativeRotationRight d L/2),
    4*EI/L*(relativeRotationRight d L + relativeRotationLeft d L/2)]

/-- The positive local elastic weighting maps deformations to the actual
stiffness virtual work, including the coupling of the two end rotations. -/
theorem member_basic_stress_work (d variation : LocalDofs) (L EA EI : ℝ) (hL : L ≠ 0) :
    (∑ i : Fin 3, memberBasicStress d L EA EI i * memberDeformation variation L i) =
      ∑ i : Fin 6, variation i *
        (∑ j : Fin 6, LocalFrameFields.stiffness L EA EI i j * d j) := by
  simp [memberBasicStress, memberDeformation, relativeRotationLeft, relativeRotationRight,
    LocalFrameFields.stiffness, Fin.sum_univ_succ]
  field_simp
  ring

/-- Half the generalized stress-deformation work is the local strain energy. -/
theorem member_basic_stress_energy (d : LocalDofs) (L EA EI : ℝ) (hL : L ≠ 0) :
    (∑ i : Fin 3, memberBasicStress d L EA EI i * memberDeformation d L i) =
      2 * energy d L EA EI := by
  rw [member_basic_stress_work d d L EA EI hL, energy_stiffness_identity d L EA EI hL]
  simp [Fin.sum_univ_succ]
  ring

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

/-- Actual member basic stresses and spring forces tested against an encoded
movement. Free and rigid directions have zero spring modulus. -/
def basicStressWork (model : Model nodes members cuts segments)
    (q variation : Coordinate model → ℝ) : ℝ :=
  (∑ segment : Fin segments, ∑ i : Fin 3,
    memberBasicStress (segmentDofs model q segment) (model.segmentLength segment)
      (model.segmentEA segment) (model.segmentEI segment) i * segmentDeformation model variation segment i) +
  ∑ member : Fin members, ∑ ending : Bool, ∑ direction : Fin 3,
    let side := (member, ending)
    springStiffness (directionLaw (endConnection model side) direction) *
      slipValue model q side direction * slipValue model variation side direction

/-- Assembled stiffness work is the work of physical basic stresses and
spring forces against the actual member and connection deformations. -/
theorem basic_stress_work_eq_stiffness (model : Model nodes members cuts segments)
    (q variation : Coordinate model → ℝ) (hsegments : positiveSegments model) :
    basicStressWork model q variation = stiffnessWork model q variation := by
  unfold basicStressWork stiffnessWork internalVirtualWork
  congr 1
  apply Finset.sum_congr rfl
  intro segment _
  exact member_basic_stress_work (segmentDofs model q segment) (segmentDofs model variation segment)
    (model.segmentLength segment) (model.segmentEA segment) (model.segmentEI segment)
    (ne_of_gt (hsegments segment).1)

/-- The exact equilibrium equations are the balance of assembled member basic
stresses and spring forces against the encoded external virtual work. -/
theorem equilibrium_iff_basic_stress_balance (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (q : Coordinate model → ℝ) (hsegments : positiveSegments model) :
    equilibrium model actions supports q ↔ admissible model supports q ∧
      ∀ variation, admissible model supports variation →
        basicStressWork model q variation = externalWork model actions variation := by
  unfold equilibrium
  constructor
  · rintro ⟨hadmissible, hbalance⟩
    refine ⟨hadmissible, ?_⟩
    intro variation hvariation
    have h := hbalance variation hvariation
    change stiffnessWork model q variation - externalWork model actions variation = 0 at h
    rw [← basic_stress_work_eq_stiffness model q variation hsegments] at h
    exact sub_eq_zero.mp h
  · rintro ⟨hadmissible, hbalance⟩
    refine ⟨hadmissible, ?_⟩
    intro variation hvariation
    change stiffnessWork model q variation - externalWork model actions variation = 0
    rw [← basic_stress_work_eq_stiffness model q variation hsegments]
    exact sub_eq_zero.mpr (hbalance variation hvariation)

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

/-- The actual assembled stiffness as a linear map into generalized-force
functionals, constructed from segment B and spring S coordinate maps. -/
def stiffnessOperator (model : Model nodes members cuts segments) :
    (Coordinate model → ℝ) →ₗ[ℝ] Module.Dual ℝ (Coordinate model → ℝ) :=
  (∑ segment : Fin segments, ∑ i : Fin 6, ∑ j : Fin 6,
    LocalFrameFields.stiffness (model.segmentLength segment) (model.segmentEA segment)
      (model.segmentEI segment) i j •
      (segmentCoordinateLinear model segment j).smulRight (segmentCoordinateLinear model segment i)) +
  ∑ member : Fin members, ∑ ending : Bool, ∑ direction : Fin 3,
    let side := (member, ending)
    let slip := slipLinear model side direction
    springStiffness (directionLaw (endConnection model side) direction) • slip.smulRight slip

/-- Applying K to a movement and testing against a variation gives the
previously established assembled stiffness work. -/
theorem stiffness_operator_apply (model : Model nodes members cuts segments)
    (q variation : Coordinate model → ℝ) :
    stiffnessOperator model q variation = stiffnessWork model q variation := by
  simp [stiffnessOperator, stiffnessWork, internalVirtualWork, segmentCoordinateLinear,
    segmentDofsLinear, slipLinear, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Restrict K to the actual support-admissible coordinate subspace. -/
def admissibleSpace (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) :=
  LinearMap.ker (constraintMap model supports)

def restrictedStiffness (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) :
    admissibleSpace model supports →ₗ[ℝ] Module.Dual ℝ (admissibleSpace model supports) :=
  (admissibleSpace model supports).subtype.dualMap.comp
    ((stiffnessOperator model).comp (admissibleSpace model supports).subtype)

/-- Restricted stiffness work uses the same physical model and support rows. -/
theorem restricted_stiffness_apply (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (q variation : admissibleSpace model supports) :
    restrictedStiffness model supports q variation = stiffnessWork model q.val variation.val := by
  exact stiffness_operator_apply model q.val variation.val

/-- A symmetric finite-dimensional operator into the dual has range equal
to the annihilator of its kernel. This is the exact load-compatibility result. -/
theorem symmetric_range_eq_kernel_annihilator {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (K : V →ₗ[ℝ] Module.Dual ℝ V)
    (hsymmetric : ∀ x y, K x y = K y x) :
    LinearMap.range K = (LinearMap.ker K).dualAnnihilator := by
  have hle : LinearMap.range K ≤ (LinearMap.ker K).dualAnnihilator := by
    intro functional hfunctional
    obtain ⟨x, rfl⟩ := hfunctional
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    rw [hsymmetric]
    have hyzero : K y = 0 := LinearMap.mem_ker.mp hy
    rw [hyzero]
    rfl
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hrank := LinearMap.finrank_range_add_finrank_ker K
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.ker K)
  omega

/-- The restricted stiffness operator is symmetric on admissible motions. -/
theorem restricted_stiffness_symmetric (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (q variation : admissibleSpace model supports) :
    restrictedStiffness model supports q variation = restrictedStiffness model supports variation q := by
  rw [restricted_stiffness_apply, restricted_stiffness_apply]
  exact stiffness_work_symmetric model q.val variation.val

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

/-- Subtracting two residuals removes the same dead loads and leaves the
stiffness work of the difference. -/
theorem residual_difference (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (q r variation : Coordinate model → ℝ) :
    residualWork model actions q variation - residualWork model actions r variation =
      stiffnessWork model (q-r) variation := by
  have hsegment (segment : Fin segments) :
      segmentDofs model (q-r) segment = segmentDofs model q segment - segmentDofs model r segment := by
    exact (segmentDofsLinear model segment).map_sub q r
  have hslip (member : Fin members) (ending : Bool) (direction : Fin 3) :
      slipValue model (q-r) (member, ending) direction =
        slipValue model q (member, ending) direction - slipValue model r (member, ending) direction := by
    exact (slipLinear model (member, ending) direction).map_sub q r
  unfold residualWork stiffnessWork internalVirtualWork
  simp only [hsegment, hslip, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Absence of admissible deformation-free motion makes any two equilibria
identical, independently of whether either equilibrium exists. -/
theorem equilibrium_unique_if_no_mechanism (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (hstable : ∀ z, admissible model supports z → deformationMap model z = 0 → z = 0)
    (q r : Coordinate model → ℝ)
    (hq : equilibrium model actions supports q) (hr : equilibrium model actions supports r) : q = r := by
  have hqker := (admissible_iff_constraint_kernel model supports q).mp hq.1
  have hrker := (admissible_iff_constraint_kernel model supports r).mp hr.1
  have hzker : q-r ∈ LinearMap.ker (constraintMap model supports) := (LinearMap.ker _).sub_mem hqker hrker
  have hzadmissible := (admissible_iff_constraint_kernel model supports (q-r)).mpr hzker
  have hwork : stiffnessWork model (q-r) (q-r) = 0 := by
    rw [← residual_difference model actions q r (q-r), hq.2 (q-r) hzadmissible,
      hr.2 (q-r) hzadmissible]
    ring
  have hsegments := contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI hcontract
  rw [stiffness_work_energy model (q-r) hsegments] at hwork
  have henergy : totalEnergy model (q-r) = 0 := by linarith
  have hdeformation := energy_zero_implies_deformation_zero model actions supports cutParameter memberLength memberEA memberEI hcontract (q-r) henergy
  exact sub_eq_zero.mp (hstable (q-r) hzadmissible hdeformation)

/-- A model with no admissible mechanism has an equilibrium for every encoded
dead load. The proof uses finite-dimensional injectivity and does not infer
stability from a computed residual or a zero-load solve. -/
theorem equilibrium_exists_if_no_mechanism (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (hstable : ∀ z, admissible model supports z → deformationMap model z = 0 → z = 0) :
    ∃ q, equilibrium model actions supports q := by
  classical
  letI : Finite (ActivePoint model) := Finite.of_injective
    (fun point : ActivePoint model => point.val) Subtype.val_injective
  letI : Finite (Slip model) := Finite.of_injective
    (fun slip : Slip model => slip.val) Subtype.val_injective
  letI : Fintype (ActivePoint model) := Fintype.ofFinite _
  letI : Fintype (Slip model) := Fintype.ofFinite _
  letI : Fintype (Coordinate model) := inferInstance
  let U := admissibleSpace model supports
  let K := restrictedStiffness model supports
  let F : Module.Dual ℝ U := U.subtype.dualMap (externalFunctional model actions)
  have hinjective : Function.Injective K := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro z hz
      have hzK : K z = 0 := LinearMap.mem_ker.mp hz
      have hwork : stiffnessWork model z.val z.val = 0 := by
        have h := congrArg (fun f : Module.Dual ℝ U => f z) hzK
        change restrictedStiffness model supports z z = 0 at h
        rw [restricted_stiffness_apply] at h
        exact h
      have hsegments := contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI hcontract
      rw [stiffness_work_energy model z.val hsegments] at hwork
      have henergy : totalEnergy model z.val = 0 := by linarith
      have hdeformation := energy_zero_implies_deformation_zero model actions supports
        cutParameter memberLength memberEA memberEI hcontract z.val henergy
      have hadmissible : admissible model supports z.val :=
        (admissible_iff_constraint_kernel model supports z.val).mpr z.property
      have hzval := hstable z.val hadmissible hdeformation
      have hz0 : z = 0 := Subtype.ext hzval
      rw [hz0]
      exact Submodule.zero_mem _
    · exact bot_le
  have hdimension : Module.finrank ℝ U = Module.finrank ℝ (Module.Dual ℝ U) := by simp
  have hsurjective : Function.Surjective K :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimension).mp hinjective
  obtain ⟨solution, hsolution⟩ := hsurjective F
  refine ⟨solution.val, ?_⟩
  refine ⟨(admissible_iff_constraint_kernel model supports solution.val).mpr solution.property, ?_⟩
  intro variation hvariation
  let v : U := ⟨variation, (admissible_iff_constraint_kernel model supports variation).mp hvariation⟩
  have hv := congrArg (fun f : Module.Dual ℝ U => f v) hsolution
  have hwork : stiffnessWork model solution.val variation = externalWork model actions variation := by
    change restrictedStiffness model supports solution v = externalFunctional model actions v.val at hv
    rw [restricted_stiffness_apply, external_functional_apply] at hv
    exact hv
  unfold residualWork
  exact sub_eq_zero.mpr hwork

/-- Equilibrium exists exactly when the encoded applied load does no work on
any admissible zero-deformation motion. This covers unstable systems without
confusing a compatible load with stability. -/
theorem equilibrium_exists_iff_load_compatible (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI) :
    (∃ q, equilibrium model actions supports q) ↔
      ∀ z, admissible model supports z → deformationMap model z = 0 → externalWork model actions z = 0 := by
  classical
  constructor
  · rintro ⟨q, hq⟩ z hadmissible hdeformation
    have hnull := (stiffness_null_iff_deformation_zero model actions supports cutParameter
      memberLength memberEA memberEI hcontract z).mpr hdeformation
    have hwork : stiffnessWork model q z = 0 := by
      rw [stiffness_work_symmetric]
      exact hnull q
    have hresidual := hq.2 z hadmissible
    unfold residualWork at hresidual
    change stiffnessWork model q z - externalWork model actions z = 0 at hresidual
    linarith
  · intro hcompatible
    letI : Finite (ActivePoint model) := Finite.of_injective
      (fun point : ActivePoint model => point.val) Subtype.val_injective
    letI : Finite (Slip model) := Finite.of_injective
      (fun slip : Slip model => slip.val) Subtype.val_injective
    letI : Fintype (ActivePoint model) := Fintype.ofFinite _
    letI : Fintype (Slip model) := Fintype.ofFinite _
    letI : Fintype (Coordinate model) := inferInstance
    let U := admissibleSpace model supports
    let K := restrictedStiffness model supports
    let F : Module.Dual ℝ U := U.subtype.dualMap (externalFunctional model actions)
    have hsym : ∀ x y : U, K x y = K y x := restricted_stiffness_symmetric model supports
    have hFann : F ∈ (LinearMap.ker K).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro z hz
      have hzK : K z = 0 := LinearMap.mem_ker.mp hz
      have hwork : stiffnessWork model z.val z.val = 0 := by
        have h := congrArg (fun f : Module.Dual ℝ U => f z) hzK
        change restrictedStiffness model supports z z = 0 at h
        rw [restricted_stiffness_apply] at h
        exact h
      have hsegments := contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI hcontract
      rw [stiffness_work_energy model z.val hsegments] at hwork
      have henergy : totalEnergy model z.val = 0 := by linarith
      have hdeformation := energy_zero_implies_deformation_zero model actions supports
        cutParameter memberLength memberEA memberEI hcontract z.val henergy
      have hadmissible := (admissible_iff_constraint_kernel model supports z.val).mpr z.property
      change externalFunctional model actions z.val = 0
      rw [external_functional_apply]
      exact hcompatible z.val hadmissible hdeformation
    have hFrange : F ∈ LinearMap.range K := by
      rw [symmetric_range_eq_kernel_annihilator K hsym]
      exact hFann
    obtain ⟨solution, hsolution⟩ := hFrange
    refine ⟨solution.val, ?_⟩
    refine ⟨(admissible_iff_constraint_kernel model supports solution.val).mpr solution.property, ?_⟩
    intro variation hvariation
    let v : U := ⟨variation, (admissible_iff_constraint_kernel model supports variation).mp hvariation⟩
    have hv := congrArg (fun f : Module.Dual ℝ U => f v) hsolution
    have hwork : stiffnessWork model solution.val variation = externalWork model actions variation := by
      change restrictedStiffness model supports solution v = externalFunctional model actions v.val at hv
      rw [restricted_stiffness_apply, external_functional_apply] at hv
      exact hv
    unfold residualWork
    exact sub_eq_zero.mpr hwork

/-- Deformation restricted to the support-admissible subspace. -/
def restrictedDeformation (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) :
    admissibleSpace model supports →ₗ[ℝ] (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ) :=
  (deformationLinear model).comp (admissibleSpace model supports).subtype

/-- The exact mechanism subspace includes all active free-slip coordinates. -/
def mechanismSpace (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) :=
  LinearMap.ker (restrictedDeformation model supports)

/-- Generalized self-stress is the kernel of the transpose of D restricted to
admissible movements. Dependent support multiplier gauges are already removed. -/
def selfStressSpace (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) :=
  LinearMap.ker (restrictedDeformation model supports).dualMap

/-- A vector of member basic stresses and finite-spring forces defines its
work functional on the same D coordinates used in the statics map. -/
def basicStressFunctional (model : Model nodes members cuts segments)
    (stress : Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ) :
    Module.Dual ℝ (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ) := by
  classical
  letI : Finite (SpringIndex model) := Finite.of_injective
    (fun spring : SpringIndex model => spring.val) Subtype.val_injective
  letI : Fintype (SpringIndex model) := Fintype.ofFinite _
  exact ∑ index, stress index • LinearMap.proj index

/-- A physical generalized stress is self-equilibrated precisely when its
virtual work vanishes for every actual support-admissible movement. -/
theorem basic_stress_selfstress_iff (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (stress : Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ) :
    basicStressFunctional model stress ∈ selfStressSpace model supports ↔
      ∀ variation, admissible model supports variation →
        basicStressFunctional model stress (deformationMap model variation) = 0 := by
  change (restrictedDeformation model supports).dualMap (basicStressFunctional model stress) = 0 ↔ _
  constructor
  · intro h variation hvariation
    let v : admissibleSpace model supports :=
      ⟨variation, (admissible_iff_constraint_kernel model supports variation).mp hvariation⟩
    have hv := congrArg (fun f : Module.Dual ℝ (admissibleSpace model supports) => f v) h
    exact hv
  · intro h
    ext v
    exact h v.val ((admissible_iff_constraint_kernel model supports v.val).mpr v.property)

/-- Exact finite-dimensional mechanism and self-stress dimension relation.
This uses deformation coordinates, not the application's numerical count. -/
theorem mechanism_selfstress_dimension (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) :
    Module.finrank ℝ (admissibleSpace model supports) +
      Module.finrank ℝ (selfStressSpace model supports) =
    Module.finrank ℝ (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ) +
      Module.finrank ℝ (mechanismSpace model supports) := by
  classical
  letI : Finite (ActivePoint model) := Finite.of_injective
    (fun point : ActivePoint model => point.val) Subtype.val_injective
  letI : Finite (Slip model) := Finite.of_injective
    (fun slip : Slip model => slip.val) Subtype.val_injective
  letI : Finite (SpringIndex model) := Finite.of_injective
    (fun spring : SpringIndex model => spring.val) Subtype.val_injective
  letI : Fintype (ActivePoint model) := Fintype.ofFinite _
  letI : Fintype (Slip model) := Fintype.ofFinite _
  letI : Fintype (SpringIndex model) := Fintype.ofFinite _
  letI : Fintype (Coordinate model) := inferInstance
  let D := restrictedDeformation model supports
  have hmovement := LinearMap.finrank_range_add_finrank_ker D
  have hstatic := LinearMap.finrank_range_add_finrank_ker D.dualMap
  have hsameRank := LinearMap.finrank_range_dualMap_eq_finrank_range D
  have hdual := Subspace.dual_finrank_eq (K := ℝ)
    (V := (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ))
  change Module.finrank ℝ (admissibleSpace model supports) + Module.finrank ℝ (LinearMap.ker D.dualMap) =
    Module.finrank ℝ (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ) +
      Module.finrank ℝ (LinearMap.ker D)
  omega

/-- Including the actual independent constraint rank gives the exact statics
count. No independence of the original support rows is assumed. -/
theorem frame_statics_dimension (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) :
    Module.finrank ℝ (Coordinate model → ℝ) + Module.finrank ℝ (selfStressSpace model supports) =
      Module.finrank ℝ (LinearMap.range (constraintMap model supports)) +
      Module.finrank ℝ (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ) +
      Module.finrank ℝ (mechanismSpace model supports) := by
  classical
  letI : Finite (ActivePoint model) := Finite.of_injective
    (fun point : ActivePoint model => point.val) Subtype.val_injective
  letI : Finite (Slip model) := Finite.of_injective
    (fun slip : Slip model => slip.val) Subtype.val_injective
  letI : Finite (SpringIndex model) := Finite.of_injective
    (fun spring : SpringIndex model => spring.val) Subtype.val_injective
  letI : Fintype (ActivePoint model) := Fintype.ofFinite _
  letI : Fintype (Slip model) := Fintype.ofFinite _
  letI : Fintype (SpringIndex model) := Fintype.ofFinite _
  letI : Fintype (Coordinate model) := inferInstance
  have hconstraints := LinearMap.finrank_range_add_finrank_ker (constraintMap model supports)
  have hstatics := mechanism_selfstress_dimension model supports
  change Module.finrank ℝ (LinearMap.range (constraintMap model supports)) +
    Module.finrank ℝ (admissibleSpace model supports) = Module.finrank ℝ (Coordinate model → ℝ) at hconstraints
  omega

/-- The explicit member basic stresses and spring forces factor through the
actual deformation map. Thus their work is Dᵀσ, not an independently assumed
global stiffness equation. -/
theorem actual_basic_stress_factor (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q : Coordinate model → ℝ) :
    ∃ stress : Module.Dual ℝ (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ),
      ∀ variation, basicStressWork model q variation = stress (deformationMap model variation) := by
  let D := deformationLinear model
  let force := stiffnessOperator model q
  have hsegments := contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI hcontract
  have hann : force ∈ (LinearMap.ker D).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro variation hvariation
    have hd : deformationMap model variation = 0 := LinearMap.mem_ker.mp hvariation
    have hnull := (stiffness_null_iff_deformation_zero model actions supports cutParameter
      memberLength memberEA memberEI hcontract variation).mpr hd
    change stiffnessOperator model q variation = 0
    rw [stiffness_operator_apply, stiffness_work_symmetric]
    exact hnull q
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker D] at hann
  obtain ⟨stress, hstress⟩ := hann
  refine ⟨stress, ?_⟩
  intro variation
  have hv := congrArg (fun f : Module.Dual ℝ (Coordinate model → ℝ) => f variation) hstress
  change stress (deformationMap model variation) = stiffnessOperator model q variation at hv
  rw [stiffness_operator_apply, ← basic_stress_work_eq_stiffness model q variation hsegments] at hv
  exact hv.symm

/-- Actual equilibrium is equivalent to balancing an induced Dᵀσ against the
encoded load on every admissible movement. -/
theorem equilibrium_has_actual_basic_stress (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q : Coordinate model → ℝ) :
    ∃ stress : Module.Dual ℝ (Sum (Fin segments × Fin 3) (SpringIndex model) → ℝ),
      (∀ variation, basicStressWork model q variation = stress (deformationMap model variation)) ∧
      (equilibrium model actions supports q ↔ admissible model supports q ∧
        ∀ variation, admissible model supports variation →
          stress (deformationMap model variation) = externalWork model actions variation) := by
  obtain ⟨stress, hfactor⟩ := actual_basic_stress_factor model actions supports cutParameter
    memberLength memberEA memberEI hcontract q
  refine ⟨stress, hfactor, ?_⟩
  rw [equilibrium_iff_basic_stress_balance model actions supports q
    (contract_positive_segments model actions supports cutParameter memberLength memberEA memberEI hcontract)]
  simp only [hfactor]

/-- A deformation-free admissible motion is a mechanism exactly when nonzero. -/
def mechanism (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) (q : Coordinate model → ℝ) : Prop :=
  q ≠ 0 ∧ admissible model supports q ∧ deformationMap model q = 0


/-- A nonzero admissible zero-deformation motion generates a distinct
solution from any existing equilibrium. -/
theorem mechanism_generates_second_equilibrium (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ)
    (hcontract : ExactContract model actions supports cutParameter memberLength memberEA memberEI)
    (q z : Coordinate model → ℝ) (hq : equilibrium model actions supports q)
    (hz : mechanism model supports z) :
    equilibrium model actions supports (q+z) ∧ q+z ≠ q := by
  have hqker := (admissible_iff_constraint_kernel model supports q).mp hq.1
  have hzker := (admissible_iff_constraint_kernel model supports z).mp hz.2.1
  have hplusker : q+z ∈ LinearMap.ker (constraintMap model supports) := (LinearMap.ker _).add_mem hqker hzker
  have hplus := (admissible_iff_constraint_kernel model supports (q+z)).mpr hplusker
  have hnull := (stiffness_null_iff_deformation_zero model actions supports cutParameter
    memberLength memberEA memberEI hcontract z).mpr hz.2.2
  refine ⟨⟨hplus, ?_⟩, ?_⟩
  · intro variation hvariation
    have hdiff := residual_difference model actions (q+z) q variation
    have hzwork := hnull variation
    have hqwork := hq.2 variation hvariation
    simp only [add_sub_cancel_left] at hdiff
    linarith
  · intro heq
    have hz0 : z = 0 := by
      have h := congrArg (fun x : Coordinate model → ℝ => x-q) heq
      simpa using h
    exact hz.1 hz0

end
end FrameDeformation
