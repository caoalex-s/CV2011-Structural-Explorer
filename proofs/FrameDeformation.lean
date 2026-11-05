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

/-- A deformation-free admissible motion is a mechanism exactly when nonzero. -/
def mechanism (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) (q : Coordinate model → ℝ) : Prop :=
  q ≠ 0 ∧ admissible model supports q ∧ deformationMap model q = 0

end
end FrameDeformation
