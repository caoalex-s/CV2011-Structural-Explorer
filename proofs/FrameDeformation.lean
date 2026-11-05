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
        simpa [deformationMap, segmentDeformation, memberDeformationLinear,
          segment_dofs_smul, Pi.smul_apply, smul_eq_mul] using hp
    | inr spring =>
        simpa [deformationMap, slipLinear, Pi.smul_apply, smul_eq_mul] using
          (slipLinear model spring.val.1 spring.val.2).map_smul a q

/-- A deformation-free admissible motion is a mechanism exactly when nonzero. -/
def mechanism (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) (q : Coordinate model → ℝ) : Prop :=
  q ≠ 0 ∧ admissible model supports q ∧ deformationMap model q = 0

end
end FrameDeformation
