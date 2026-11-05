import FrameDeformation

/-!
Reuse over one fixed, exactly presegmented structure. Loading amplitudes may
change, but member ordering, end laws, supports and the cut partition do not.
No statement here identifies this exact model with browser preprocessing.
-/
open FrameInterfaces FrameTransform FrameAssemblyModel FrameAssembly FrameDeformation

namespace FrameReuse
noncomputable section

/-- Erase only distributed-load amplitudes; all structural fields and ordering
remain part of the core. Point-action and support locations are fixed separately. -/
def structuralCore (model : Model nodes members cuts segments) : Model nodes members cuts segments :=
  { model with segmentVerticalStart := fun _ => 0, segmentVerticalEnd := fun _ => 0 }

def sameCore (first second : Model nodes members cuts segments) : Prop :=
  structuralCore first = structuralCore second

/-- Replace only the two global-vertical intensity values on each segment. -/
def withLoads (core : Model nodes members cuts segments)
    (startValue endValue : Fin segments → ℝ) : Model nodes members cuts segments :=
  { core with segmentVerticalStart := startValue, segmentVerticalEnd := endValue }

/-- Fixed point-action locations with independently variable global components. -/
def pointActions (locations : Fin actionCount → Location members cuts)
    (components : Fin actionCount → Triple) : Fin actionCount → PointAction members cuts :=
  fun index => ⟨locations index, components index⟩

theorem rebuild_model (model : Model nodes members cuts segments) :
    withLoads (structuralCore model) model.segmentVerticalStart model.segmentVerticalEnd = model := by
  cases model
  rfl

theorem same_core_with_loads (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ) :
    sameCore (withLoads core start₁ end₁) (withLoads core start₂ end₂) := by
  rfl

/-- Both dependent coordinate types have identical active-point and slip
predicates: intensity amplitudes do not allocate coordinates. -/
def coordinateEquiv (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ) :
    Coordinate (withLoads core start₁ end₁) ≃ Coordinate (withLoads core start₂ end₂) :=
  Equiv.refl _

/-- Precomposition with the coordinate equivalence transports motion vectors. -/
def motionEquiv (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ) :
    (Coordinate (withLoads core start₁ end₁) → ℝ) ≃ₗ[ℝ]
      (Coordinate (withLoads core start₂ end₂) → ℝ) :=
  LinearEquiv.refl ℝ _

theorem active_points_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ) (point : Point nodes members cuts) :
    activePoint (withLoads core start₁ end₁) point ↔ activePoint (withLoads core start₂ end₂) point := by
  rfl

theorem active_slips_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ) (side : MemberEnd members) (direction : Fin 3) :
    hasSlip (withLoads core start₁ end₁) side direction ↔ hasSlip (withLoads core start₂ end₂) side direction := by
  rfl

theorem side_motion_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ)
    (q : Coordinate (withLoads core start₁ end₁) → ℝ) (location : Location members cuts) :
    sideMotion (withLoads core start₁ end₁) q location =
      sideMotion (withLoads core start₂ end₂) (motionEquiv core start₁ end₁ start₂ end₂ q) location := by
  rfl

theorem segment_dofs_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ)
    (q : Coordinate (withLoads core start₁ end₁) → ℝ) (segment : Fin segments) :
    segmentDofs (withLoads core start₁ end₁) q segment =
      segmentDofs (withLoads core start₂ end₂) (motionEquiv core start₁ end₁ start₂ end₂ q) segment := by
  rfl

theorem constraint_map_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ)
    (supports : Fin supportCount → SupportInput members cuts)
    (q : Coordinate (withLoads core start₁ end₁) → ℝ) :
    constraintMap (withLoads core start₁ end₁) supports q =
      constraintMap (withLoads core start₂ end₂) supports (motionEquiv core start₁ end₁ start₂ end₂ q) := by
  rfl

theorem stiffness_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ)
    (q v : Coordinate (withLoads core start₁ end₁) → ℝ) :
    stiffnessWork (withLoads core start₁ end₁) q v =
      stiffnessWork (withLoads core start₂ end₂)
        (motionEquiv core start₁ end₁ start₂ end₂ q) (motionEquiv core start₁ end₁ start₂ end₂ v) := by
  rfl

theorem admissible_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ)
    (supports : Fin supportCount → SupportInput members cuts)
    (q : Coordinate (withLoads core start₁ end₁) → ℝ) :
    admissible (withLoads core start₁ end₁) supports q ↔
      admissible (withLoads core start₂ end₂) supports (motionEquiv core start₁ end₁ start₂ end₂ q) := by
  rfl


/-- D retains the same segment and spring indices under amplitude changes. -/
theorem deformation_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ)
    (q : Coordinate (withLoads core start₁ end₁) → ℝ) :
    deformationMap (withLoads core start₁ end₁) q =
      deformationMap (withLoads core start₂ end₂) (motionEquiv core start₁ end₁ start₂ end₂ q) := by
  rfl

/-- The input contract concerns locations and properties, not load amplitudes. -/
theorem exact_contract_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ)
    (locations : Fin actionCount → Location members cuts)
    (forces₁ forces₂ : Fin actionCount → Triple)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ) :
    ExactContract (withLoads core start₁ end₁) (pointActions locations forces₁) supports cutsAt length EA EI ↔
      ExactContract (withLoads core start₂ end₂) (pointActions locations forces₂) supports cutsAt length EA EI := by
  constructor <;> intro h <;>
    exact ⟨h.ownership, h.ordered, h.coverage, h.disjointInteriors, h.canonicalLocations,
      h.memberEnds, h.interiorCuts, h.actionLocations, h.supportLocations,
      h.orientationNormalized, h.supportNormalized, h.positiveMember, h.segmentLengthMatches,
      h.segmentPropertiesMatch, h.positiveSpring⟩

/-- The admissible no-mechanism hypothesis is independent of load amplitude. -/
theorem no_mechanism_unchanged (core : Model nodes members cuts segments)
    (start₁ end₁ start₂ end₂ : Fin segments → ℝ)
    (supports : Fin supportCount → SupportInput members cuts) :
    (∀ z, admissible (withLoads core start₁ end₁) supports z →
      deformationMap (withLoads core start₁ end₁) z = 0 → z = 0) ↔
    (∀ z, admissible (withLoads core start₂ end₂) supports z →
      deformationMap (withLoads core start₂ end₂) z = 0 → z = 0) := by
  rfl


/-- Axial recovery is linear jointly in end movements and affine-load values. -/
theorem axial_recovery_combination (d₁ d₂ : LocalDofs) (a b L EA p₀ p₁ r₀ r₁ : ℝ) :
    LocalFrameFields.axialDisplacement (fun i => a * d₁ i + b * d₂ i) L EA
      (a * p₀ + b * r₀) (a * p₁ + b * r₁) =
    Polynomial.C a * LocalFrameFields.axialDisplacement d₁ L EA p₀ p₁ +
      Polynomial.C b * LocalFrameFields.axialDisplacement d₂ L EA r₀ r₁ := by
  simp only [LocalFrameFields.axialDisplacement, map_add, map_mul]
  ring

/-- Transverse recovery combines the movement interpolation and the actual
load particular field, rather than treating a loaded field as homogeneous. -/
theorem transverse_recovery_combination (d₁ d₂ : LocalDofs) (a b L EI q₀ q₁ r₀ r₁ : ℝ) :
    LocalFrameFields.transverseDisplacement (fun i => a * d₁ i + b * d₂ i) L EI
      (a * q₀ + b * r₀) (a * q₁ + b * r₁) =
    Polynomial.C a * LocalFrameFields.transverseDisplacement d₁ L EI q₀ q₁ +
      Polynomial.C b * LocalFrameFields.transverseDisplacement d₂ L EI r₀ r₁ := by
  simp only [LocalFrameFields.transverseDisplacement, map_add, map_mul, map_sub]
  ring


/-- At a fixed nonzero load the axial field is affine, not linear, in movement. -/
theorem axial_recovery_movement_affine (d₁ d₂ : LocalDofs) (L EA p₀ p₁ : ℝ) :
    LocalFrameFields.axialDisplacement (fun i => d₁ i + d₂ i) L EA p₀ p₁ =
      LocalFrameFields.axialDisplacement d₁ L EA p₀ p₁ +
      LocalFrameFields.axialDisplacement d₂ L EA p₀ p₁ -
      LocalFrameFields.axialDisplacement (fun _ => 0) L EA p₀ p₁ := by
  simp only [LocalFrameFields.axialDisplacement, map_add, map_zero]
  ring

/-- The same fixed-load affine correction applies to transverse recovery. -/
theorem transverse_recovery_movement_affine (d₁ d₂ : LocalDofs) (L EI q₀ q₁ : ℝ) :
    LocalFrameFields.transverseDisplacement (fun i => d₁ i + d₂ i) L EI q₀ q₁ =
      LocalFrameFields.transverseDisplacement d₁ L EI q₀ q₁ +
      LocalFrameFields.transverseDisplacement d₂ L EI q₀ q₁ -
      LocalFrameFields.transverseDisplacement (fun _ => 0) L EI q₀ q₁ := by
  simp only [LocalFrameFields.transverseDisplacement, map_add, map_mul, map_zero, mul_zero]
  ring

end
end FrameReuse
