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

/-- Supports and action slots are part of the reuse boundary. In particular,
changing a location requires a new partition rather than an amplitude update. -/
def sameStructure (first second : Model nodes members cuts segments)
    (supports₁ supports₂ : Fin supportCount → SupportInput members cuts)
    (locations₁ locations₂ : Fin actionCount → Location members cuts) : Prop :=
  sameCore first second ∧ supports₁ = supports₂ ∧ locations₁ = locations₂

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

/-- Transport coordinates of two independently supplied models whose erased
structural records are equal. The intermediate maps preserve the subtype IDs. -/
def sameCoreCoordinateEquiv (first second : Model nodes members cuts segments)
    (h : sameCore first second) : Coordinate first ≃ Coordinate second := by
  have coordinateTypes : Coordinate first = Coordinate second := by
    calc
      Coordinate first = Coordinate (withLoads (structuralCore first)
          first.segmentVerticalStart first.segmentVerticalEnd) :=
        congrArg Coordinate (rebuild_model first).symm
      _ = Coordinate (withLoads (structuralCore second)
          first.segmentVerticalStart first.segmentVerticalEnd) := by rw [h]
      _ = Coordinate (withLoads (structuralCore second)
          second.segmentVerticalStart second.segmentVerticalEnd) := rfl
      _ = Coordinate second := congrArg Coordinate (rebuild_model second)
  exact Equiv.cast coordinateTypes

/-- Coordinate transport induces a linear equivalence of full motion vectors. -/
def sameCoreMotionEquiv (first second : Model nodes members cuts segments)
    (h : sameCore first second) : (Coordinate first → ℝ) ≃ₗ[ℝ] (Coordinate second → ℝ) where
  toFun q := fun i => q ((sameCoreCoordinateEquiv first second h).symm i)
  invFun q := fun i => q (sameCoreCoordinateEquiv first second h i)
  left_inv q := by funext i; simp
  right_inv q := by funext i; simp
  map_add' q r := by rfl
  map_smul' a q := by rfl

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
  funext index
  cases index <;> rfl

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
  constructor
  · intro h z hz hd
    apply h z hz
    rw [deformation_unchanged core start₁ end₁ start₂ end₂ z]
    exact hd
  · intro h z hz hd
    apply h z hz
    rw [deformation_unchanged core start₂ end₂ start₁ end₁ z]
    exact hd


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


/-- Consistent segment loads vary linearly with both endpoint intensities. -/
theorem segment_load_combination (core : Model nodes members cuts segments)
    (a b : ℝ) (s₁ e₁ s₂ e₂ : Fin segments → ℝ) (segment : Fin segments) :
    segmentLoad (withLoads core (fun i => a*s₁ i+b*s₂ i) (fun i => a*e₁ i+b*e₂ i)) segment =
      a • segmentLoad (withLoads core s₁ e₁) segment + b • segmentLoad (withLoads core s₂ e₂) segment := by
  funext i
  fin_cases i <;> simp [segmentLoad, withLoads, LocalFrameFields.consistentLoad] <;> ring

/-- Point actions retain their fixed member-side location while components vary. -/
theorem point_work_combination (core : Model nodes members cuts segments)
    (a b : ℝ) (location : Location members cuts) (f₁ f₂ : Triple)
    (q : Coordinate core → ℝ) :
    pointActionWork core ⟨location, fun i => a*f₁ i+b*f₂ i⟩ q =
      a * pointActionWork core ⟨location, f₁⟩ q + b * pointActionWork core ⟨location, f₂⟩ q := by
  simp [pointActionWork, FrameTransform.work]
  ring


/-- Actual external work is linear in distributed amplitudes and fixed-slot
point-action components, including both member-side ownership and orientation. -/
theorem external_work_combination (core : Model nodes members cuts segments)
    (a b : ℝ) (s₁ e₁ s₂ e₂ : Fin segments → ℝ)
    (locations : Fin actionCount → Location members cuts)
    (f₁ f₂ : Fin actionCount → Triple) (q : Coordinate core → ℝ) :
    externalWork (withLoads core (fun i => a*s₁ i+b*s₂ i) (fun i => a*e₁ i+b*e₂ i))
      (pointActions locations (fun j i => a*f₁ j i+b*f₂ j i)) q =
    a * externalWork (withLoads core s₁ e₁) (pointActions locations f₁) q +
      b * externalWork (withLoads core s₂ e₂) (pointActions locations f₂) q := by
  have hsegment : ∀ segment i,
      segmentLoad (withLoads core (fun j => a*s₁ j+b*s₂ j) (fun j => a*e₁ j+b*e₂ j)) segment i *
          segmentDofs core q segment i =
      a * (segmentLoad (withLoads core s₁ e₁) segment i * segmentDofs core q segment i) +
        b * (segmentLoad (withLoads core s₂ e₂) segment i * segmentDofs core q segment i) := by
    intro segment i
    have h := congrFun (segment_load_combination core a b s₁ e₁ s₂ e₂ segment) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    ring
  have hpoint : ∀ j,
      pointActionWork core (pointActions locations (fun k i => a*f₁ k i+b*f₂ k i) j) q =
      a * pointActionWork core (pointActions locations f₁ j) q +
        b * pointActionWork core (pointActions locations f₂ j) q := by
    intro j
    exact point_work_combination core a b (locations j) (f₁ j) (f₂ j) q
  change (∑ segment : Fin segments, ∑ i : Fin 6,
      segmentLoad (withLoads core (fun j => a*s₁ j+b*s₂ j) (fun j => a*e₁ j+b*e₂ j)) segment i *
        segmentDofs core q segment i) +
    (∑ j : Fin actionCount, pointActionWork core (pointActions locations (fun k i => a*f₁ k i+b*f₂ k i) j) q) =
    a * ((∑ segment : Fin segments, ∑ i : Fin 6,
      segmentLoad (withLoads core s₁ e₁) segment i * segmentDofs core q segment i) +
      ∑ j : Fin actionCount, pointActionWork core (pointActions locations f₁ j) q) +
    b * ((∑ segment : Fin segments, ∑ i : Fin 6,
      segmentLoad (withLoads core s₂ e₂) segment i * segmentDofs core q segment i) +
      ∑ j : Fin actionCount, pointActionWork core (pointActions locations f₂ j) q)
  simp_rw [hsegment, hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring


/-- Constrained equilibria superpose for fixed structure and homogeneous
support rows, whether or not the system has a mechanism. -/
theorem equilibrium_combination (core : Model nodes members cuts segments)
    (a b : ℝ) (s₁ e₁ s₂ e₂ : Fin segments → ℝ)
    (locations : Fin actionCount → Location members cuts) (f₁ f₂ : Fin actionCount → Triple)
    (supports : Fin supportCount → SupportInput members cuts) (q₁ q₂ : Coordinate core → ℝ)
    (h₁ : equilibrium (withLoads core s₁ e₁) (pointActions locations f₁) supports q₁)
    (h₂ : equilibrium (withLoads core s₂ e₂) (pointActions locations f₂) supports q₂) :
    equilibrium (withLoads core (fun i => a*s₁ i+b*s₂ i) (fun i => a*e₁ i+b*e₂ i))
      (pointActions locations (fun j i => a*f₁ j i+b*f₂ j i)) supports (a • q₁ + b • q₂) := by
  have hq₁ : q₁ ∈ LinearMap.ker (constraintMap core supports) :=
    (admissible_iff_constraint_kernel core supports q₁).mp h₁.1
  have hq₂ : q₂ ∈ LinearMap.ker (constraintMap core supports) :=
    (admissible_iff_constraint_kernel core supports q₂).mp h₂.1
  have hq : a • q₁ + b • q₂ ∈ LinearMap.ker (constraintMap core supports) :=
    (LinearMap.ker _).add_mem ((LinearMap.ker _).smul_mem a hq₁) ((LinearMap.ker _).smul_mem b hq₂)
  constructor
  · exact (admissible_iff_constraint_kernel core supports (a • q₁ + b • q₂)).mpr hq
  · intro v hv
    have hw₁ := h₁.2 v hv
    have hw₂ := h₂.2 v hv
    have hk : stiffnessWork core (a • q₁ + b • q₂) v =
        a * stiffnessWork core q₁ v + b * stiffnessWork core q₂ v := by
      simp only [← stiffness_operator_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
    change stiffnessWork core (a • q₁ + b • q₂) v -
      externalWork (withLoads core (fun i => a*s₁ i+b*s₂ i) (fun i => a*e₁ i+b*e₂ i))
        (pointActions locations (fun j i => a*f₁ j i+b*f₂ j i)) v = 0
    change stiffnessWork core q₁ v - externalWork (withLoads core s₁ e₁) (pointActions locations f₁) v = 0 at hw₁
    change stiffnessWork core q₂ v - externalWork (withLoads core s₂ e₂) (pointActions locations f₂) v = 0 at hw₂
    rw [hk, external_work_combination]
    linear_combination a * hw₁ + b * hw₂


/-- Rotation is the derivative of the jointly linear transverse field. -/
theorem rotation_recovery_combination (d₁ d₂ : LocalDofs) (a b L EI q₀ q₁ r₀ r₁ : ℝ) :
    LocalFrameFields.rotation (fun i => a*d₁ i+b*d₂ i) L EI (a*q₀+b*r₀) (a*q₁+b*r₁) =
      Polynomial.C a * LocalFrameFields.rotation d₁ L EI q₀ q₁ +
        Polynomial.C b * LocalFrameFields.rotation d₂ L EI r₀ r₁ := by
  simp [LocalFrameFields.rotation, transverse_recovery_combination, Polynomial.derivative_add,
    Polynomial.derivative_mul]

/-- Normal force keeps the distributed axial-load contribution. -/
theorem normal_recovery_combination (d₁ d₂ : LocalDofs) (a b L EA p₀ p₁ r₀ r₁ : ℝ) :
    LocalFrameFields.normal (fun i => a*d₁ i+b*d₂ i) L EA (a*p₀+b*r₀) (a*p₁+b*r₁) =
      Polynomial.C a * LocalFrameFields.normal d₁ L EA p₀ p₁ +
        Polynomial.C b * LocalFrameFields.normal d₂ L EA r₀ r₁ := by
  simp [LocalFrameFields.normal, axial_recovery_combination, Polynomial.derivative_add,
    Polynomial.derivative_mul]
  ring

/-- Bending moment and shear follow by differentiation of the same field. -/
theorem moment_recovery_combination (d₁ d₂ : LocalDofs) (a b L EI q₀ q₁ r₀ r₁ : ℝ) :
    LocalFrameFields.moment (fun i => a*d₁ i+b*d₂ i) L EI (a*q₀+b*r₀) (a*q₁+b*r₁) =
      Polynomial.C a * LocalFrameFields.moment d₁ L EI q₀ q₁ +
        Polynomial.C b * LocalFrameFields.moment d₂ L EI r₀ r₁ := by
  simp [LocalFrameFields.moment, rotation_recovery_combination, Polynomial.derivative_add,
    Polynomial.derivative_mul]
  ring

theorem shear_recovery_combination (d₁ d₂ : LocalDofs) (a b L EI q₀ q₁ r₀ r₁ : ℝ) :
    LocalFrameFields.shear (fun i => a*d₁ i+b*d₂ i) L EI (a*q₀+b*r₀) (a*q₁+b*r₁) =
      Polynomial.C a * LocalFrameFields.shear d₁ L EI q₀ q₁ +
        Polynomial.C b * LocalFrameFields.shear d₂ L EI r₀ r₁ := by
  simp [LocalFrameFields.shear, moment_recovery_combination, Polynomial.derivative_add,
    Polynomial.derivative_mul]


/-- End actions use the established force and moment fields at both ends. -/
theorem end_actions_combination (d₁ d₂ : LocalDofs) (a b L EA EI p₀ p₁ r₀ r₁ q₀ q₁ t₀ t₁ : ℝ) :
    LocalFrameFields.endActions (fun i => a*d₁ i+b*d₂ i) L EA EI
      (a*p₀+b*r₀) (a*p₁+b*r₁) (a*q₀+b*t₀) (a*q₁+b*t₁) =
      a • LocalFrameFields.endActions d₁ L EA EI p₀ p₁ q₀ q₁ +
        b • LocalFrameFields.endActions d₂ L EA EI r₀ r₁ t₀ t₁ := by
  funext i
  fin_cases i <;>
    simp [LocalFrameFields.endActions, normal_recovery_combination, shear_recovery_combination,
      moment_recovery_combination, Polynomial.eval_add, Polynomial.eval_mul] <;> ring


/-- On physically valid segments the field-derived residual equals the actual
assembled Kq−F functional, independently of a multiplier representation. -/
theorem residual_eq_stiffness_minus_load (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts) (q : Coordinate model → ℝ)
    (hpositive : positiveSegments model) :
    residualFunctional model actions q = stiffnessOperator model q - externalFunctional model actions := by
  ext v
  rw [residual_functional_apply model actions q v hpositive]
  change residualWork model actions q v = stiffnessOperator model q v - externalFunctional model actions v
  rw [stiffness_operator_apply, external_functional_apply]
  rfl

/-- A combined residual gives the aggregate reaction when it satisfies the
actual support equations. No individual multiplier is selected here. -/
theorem combined_aggregate_reaction (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (coeff₁ coeff₂ : ConstraintIndex supports → ℝ) (a b : ℝ) :
    aggregateReaction model supports (a • coeff₁ + b • coeff₂) =
      a • aggregateReaction model supports coeff₁ + b • aggregateReaction model supports coeff₂ := by
  classical
  ext v
  simp [aggregateReaction, multiplierFunctional, LinearMap.dualMap_apply,
    Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_add, mul_assoc]


/-- Independent intensity endpoints and fixed-slot point-action components. -/
abbrev LoadCase (segments actionCount : Nat) :=
  ((Fin segments → ℝ) × (Fin segments → ℝ)) × (Fin actionCount → Triple)

def caseModel (core : Model nodes members cuts segments) (load : LoadCase segments actionCount) :
    Model nodes members cuts segments := withLoads core load.1.1 load.1.2

def caseActions (locations : Fin actionCount → Location members cuts) (load : LoadCase segments actionCount) :
    Fin actionCount → PointAction members cuts := pointActions locations load.2

theorem case_contract (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (baseContract : ExactContract (withLoads core 0 0) (pointActions locations 0) supports cutsAt length EA EI)
    (load : LoadCase segments actionCount) :
    ExactContract (caseModel core load) (caseActions locations load) supports cutsAt length EA EI := by
  exact (exact_contract_unchanged core 0 0 load.1.1 load.1.2 locations 0 load.2
    supports cutsAt length EA EI).mp baseContract

theorem case_stable (core : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (baseStable : ∀ z, admissible (withLoads core 0 0) supports z →
      deformationMap (withLoads core 0 0) z = 0 → z = 0)
    (load : LoadCase segments actionCount) :
    ∀ z, admissible (caseModel core load) supports z → deformationMap (caseModel core load) z = 0 → z = 0 := by
  exact (no_mechanism_unchanged core 0 0 load.1.1 load.1.2 supports).mp baseStable

/-- Existence follows from the existing restricted-stiffness theorem. Choice is
only used to name its solution; uniqueness below determines the linear map. -/
def solutionChoice (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (baseContract : ExactContract (withLoads core 0 0) (pointActions locations 0) supports cutsAt length EA EI)
    (baseStable : ∀ z, admissible (withLoads core 0 0) supports z →
      deformationMap (withLoads core 0 0) z = 0 → z = 0)
    (load : LoadCase segments actionCount) : Coordinate core → ℝ :=
  Classical.choose (equilibrium_exists_if_no_mechanism (caseModel core load) (caseActions locations load)
    supports cutsAt length EA EI (case_contract core locations supports cutsAt length EA EI baseContract load)
    (case_stable core supports baseStable load))

theorem solution_choice_equilibrium (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (baseContract : ExactContract (withLoads core 0 0) (pointActions locations 0) supports cutsAt length EA EI)
    (baseStable : ∀ z, admissible (withLoads core 0 0) supports z →
      deformationMap (withLoads core 0 0) z = 0 → z = 0)
    (load : LoadCase segments actionCount) :
    equilibrium (caseModel core load) (caseActions locations load) supports
      (solutionChoice core locations supports cutsAt length EA EI baseContract baseStable load) :=
  Classical.choose_spec (equilibrium_exists_if_no_mechanism (caseModel core load) (caseActions locations load)
    supports cutsAt length EA EI (case_contract core locations supports cutsAt length EA EI baseContract load)
    (case_stable core supports baseStable load))


/-- Unique stable equilibrium varies linearly on the fixed load space. -/
def stableSolutionLinear (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (baseContract : ExactContract (withLoads core 0 0) (pointActions locations 0) supports cutsAt length EA EI)
    (baseStable : ∀ z, admissible (withLoads core 0 0) supports z →
      deformationMap (withLoads core 0 0) z = 0 → z = 0) :
    LoadCase segments actionCount →ₗ[ℝ] (Coordinate core → ℝ) where
  toFun := solutionChoice core locations supports cutsAt length EA EI baseContract baseStable
  map_add' load₁ load₂ := by
    apply equilibrium_unique_if_no_mechanism (caseModel core (load₁+load₂))
      (caseActions locations (load₁+load₂)) supports cutsAt length EA EI
      (case_contract core locations supports cutsAt length EA EI baseContract (load₁+load₂))
      (case_stable core supports baseStable (load₁+load₂))
    · exact solution_choice_equilibrium core locations supports cutsAt length EA EI baseContract baseStable _
    · have h := equilibrium_combination core 1 1 load₁.1.1 load₁.1.2 load₂.1.1 load₂.1.2
        locations load₁.2 load₂.2 supports
        (solutionChoice core locations supports cutsAt length EA EI baseContract baseStable load₁)
        (solutionChoice core locations supports cutsAt length EA EI baseContract baseStable load₂)
        (solution_choice_equilibrium core locations supports cutsAt length EA EI baseContract baseStable load₁)
        (solution_choice_equilibrium core locations supports cutsAt length EA EI baseContract baseStable load₂)
      change equilibrium (withLoads core (fun i => load₁.1.1 i + load₂.1.1 i)
        (fun i => load₁.1.2 i + load₂.1.2 i))
        (pointActions locations (fun j i => load₁.2 j i + load₂.2 j i)) supports
        (solutionChoice core locations supports cutsAt length EA EI baseContract baseStable load₁ +
          solutionChoice core locations supports cutsAt length EA EI baseContract baseStable load₂)
      have hs : (fun i => (1:ℝ)*load₁.1.1 i+1*load₂.1.1 i) = (fun i => load₁.1.1 i+load₂.1.1 i) := by
        funext i; ring
      have he : (fun i => (1:ℝ)*load₁.1.2 i+1*load₂.1.2 i) = (fun i => load₁.1.2 i+load₂.1.2 i) := by
        funext i; ring
      have hf : (fun j i => (1:ℝ)*load₁.2 j i+1*load₂.2 j i) = (fun j i => load₁.2 j i+load₂.2 j i) := by
        funext j i; ring
      rw [hs, he, hf] at h
      simpa only [one_smul] using h
  map_smul' a load := by
    apply equilibrium_unique_if_no_mechanism (caseModel core (a • load))
      (caseActions locations (a • load)) supports cutsAt length EA EI
      (case_contract core locations supports cutsAt length EA EI baseContract (a • load))
      (case_stable core supports baseStable (a • load))
    · exact solution_choice_equilibrium core locations supports cutsAt length EA EI baseContract baseStable _
    · have h := equilibrium_combination core a 0 load.1.1 load.1.2 load.1.1 load.1.2
        locations load.2 load.2 supports
        (solutionChoice core locations supports cutsAt length EA EI baseContract baseStable load)
        (solutionChoice core locations supports cutsAt length EA EI baseContract baseStable load)
        (solution_choice_equilibrium core locations supports cutsAt length EA EI baseContract baseStable load)
        (solution_choice_equilibrium core locations supports cutsAt length EA EI baseContract baseStable load)
      change equilibrium (withLoads core (fun i => a * load.1.1 i) (fun i => a * load.1.2 i))
        (pointActions locations (fun j i => a * load.2 j i)) supports
        (a • solutionChoice core locations supports cutsAt length EA EI baseContract baseStable load)
      have hs : (fun i => a*load.1.1 i+0*load.1.1 i) = (fun i => a*load.1.1 i) := by
        funext i; ring
      have he : (fun i => a*load.1.2 i+0*load.1.2 i) = (fun i => a*load.1.2 i) := by
        funext i; ring
      have hf : (fun j i => a*load.2 j i+0*load.2 j i) = (fun j i => a*load.2 j i) := by
        funext j i; ring
      rw [hs, he, hf] at h
      simpa only [zero_smul, add_zero] using h


/-- Actual residual work combines the same movements and applied loads. -/
theorem residual_work_combination (core : Model nodes members cuts segments)
    (a b : ℝ) (s₁ e₁ s₂ e₂ : Fin segments → ℝ)
    (locations : Fin actionCount → Location members cuts) (f₁ f₂ : Fin actionCount → Triple)
    (q₁ q₂ v : Coordinate core → ℝ) :
    residualWork (withLoads core (fun i => a*s₁ i+b*s₂ i) (fun i => a*e₁ i+b*e₂ i))
      (pointActions locations (fun j i => a*f₁ j i+b*f₂ j i)) (a • q₁ + b • q₂) v =
    a * residualWork (withLoads core s₁ e₁) (pointActions locations f₁) q₁ v +
      b * residualWork (withLoads core s₂ e₂) (pointActions locations f₂) q₂ v := by
  have hk : stiffnessWork core (a • q₁ + b • q₂) v =
      a * stiffnessWork core q₁ v + b * stiffnessWork core q₂ v := by
    simp only [← stiffness_operator_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
  change stiffnessWork core (a • q₁ + b • q₂) v -
      externalWork (withLoads core (fun i => a*s₁ i+b*s₂ i) (fun i => a*e₁ i+b*e₂ i))
        (pointActions locations (fun j i => a*f₁ j i+b*f₂ j i)) v =
    a * (stiffnessWork core q₁ v - externalWork (withLoads core s₁ e₁) (pointActions locations f₁) v) +
      b * (stiffnessWork core q₂ v - externalWork (withLoads core s₂ e₂) (pointActions locations f₂) v)
  rw [hk, external_work_combination]
  ring

/-- Any chosen support representatives for the three equilibria give the
same aggregate combination, including when duplicate rows admit a gauge. -/
theorem aggregate_reaction_from_residuals (core : Model nodes members cuts segments)
    (a b : ℝ) (s₁ e₁ s₂ e₂ : Fin segments → ℝ)
    (locations : Fin actionCount → Location members cuts) (f₁ f₂ : Fin actionCount → Triple)
    (supports : Fin supportCount → SupportInput members cuts) (q₁ q₂ : Coordinate core → ℝ)
    (coeff₁ coeff₂ coeffCombined : ConstraintIndex supports → ℝ) (hpositive : positiveSegments core)
    (hr₁ : residualFunctional (withLoads core s₁ e₁) (pointActions locations f₁) q₁ =
      aggregateReaction core supports coeff₁)
    (hr₂ : residualFunctional (withLoads core s₂ e₂) (pointActions locations f₂) q₂ =
      aggregateReaction core supports coeff₂)
    (hrCombined : residualFunctional
      (withLoads core (fun i => a*s₁ i+b*s₂ i) (fun i => a*e₁ i+b*e₂ i))
      (pointActions locations (fun j i => a*f₁ j i+b*f₂ j i)) (a • q₁ + b • q₂) =
        aggregateReaction core supports coeffCombined) :
    aggregateReaction core supports coeffCombined =
      a • aggregateReaction core supports coeff₁ + b • aggregateReaction core supports coeff₂ := by
  rw [← hrCombined, ← hr₁, ← hr₂]
  ext v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hc := residual_functional_apply (withLoads core (fun i => a*s₁ i+b*s₂ i) (fun i => a*e₁ i+b*e₂ i))
    (pointActions locations (fun j i => a*f₁ j i+b*f₂ j i)) (a • q₁ + b • q₂) v hpositive
  have h₁ := residual_functional_apply (withLoads core s₁ e₁) (pointActions locations f₁) q₁ v hpositive
  have h₂ := residual_functional_apply (withLoads core s₂ e₂) (pointActions locations f₂) q₂ v hpositive
  exact hc.trans ((residual_work_combination core a b s₁ e₁ s₂ e₂ locations f₁ f₂ q₁ q₂ v).trans
    (congrArg₂ (fun x y : ℝ => a*x+b*y) h₁.symm h₂.symm))

/-- The same aggregate identity holds after selecting any global hub component. -/
theorem grouped_reaction_from_residuals (core : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts)
    (coeff₁ coeff₂ coeffCombined : ConstraintIndex supports → ℝ) (a b : ℝ)
    (h : aggregateReaction core supports coeffCombined =
      a • aggregateReaction core supports coeff₁ + b • aggregateReaction core supports coeff₂)
    (point : ActivePoint core) (direction : Fin 3) :
    groupedGroundAction core supports coeffCombined point direction =
      a * groupedGroundAction core supports coeff₁ point direction +
        b * groupedGroundAction core supports coeff₂ point direction := by
  have hv := congrArg (fun reaction : Module.Dual ℝ (Coordinate core → ℝ) =>
    reaction (coordinateBasis core (.inl (point, direction)))) h
  simpa [groupedGroundAction] using hv


set_option maxHeartbeats 1600000 in
/-- Actual assembled loads form a linear map from the frozen load slots. -/
def externalLoadLinear (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts) :
    LoadCase segments actionCount →ₗ[ℝ] Module.Dual ℝ (Coordinate core → ℝ) where
  toFun load := externalFunctional (caseModel core load) (caseActions locations load)
  map_add' load₁ load₂ := by
    ext v
    change externalFunctional (caseModel core (load₁+load₂)) (caseActions locations (load₁+load₂)) v =
      externalFunctional (caseModel core load₁) (caseActions locations load₁) v +
        externalFunctional (caseModel core load₂) (caseActions locations load₂) v
    have h := external_work_combination core 1 1 load₁.1.1 load₁.1.2 load₂.1.1 load₂.1.2
      locations load₁.2 load₂.2 v
    have hs : (fun i => (1:ℝ)*load₁.1.1 i+1*load₂.1.1 i) = (fun i => load₁.1.1 i+load₂.1.1 i) := by
      funext i; ring
    have he : (fun i => (1:ℝ)*load₁.1.2 i+1*load₂.1.2 i) = (fun i => load₁.1.2 i+load₂.1.2 i) := by
      funext i; ring
    have hf : (fun j i => (1:ℝ)*load₁.2 j i+1*load₂.2 j i) = (fun j i => load₁.2 j i+load₂.2 j i) := by
      funext j i; ring
    rw [hs, he, hf] at h
    have hh : externalWork (caseModel core (load₁+load₂)) (caseActions locations (load₁+load₂)) v =
        externalWork (caseModel core load₁) (caseActions locations load₁) v +
          externalWork (caseModel core load₂) (caseActions locations load₂) v := by
      simpa only [one_mul] using h
    exact (external_functional_apply (caseModel core (load₁+load₂)) (caseActions locations (load₁+load₂)) v).trans (hh.trans
      (congrArg₂ (· + ·) (external_functional_apply (caseModel core load₁) (caseActions locations load₁) v).symm
        (external_functional_apply (caseModel core load₂) (caseActions locations load₂) v).symm))
  map_smul' a load := by
    ext v
    change externalFunctional (caseModel core (a • load)) (caseActions locations (a • load)) v =
      a * externalFunctional (caseModel core load) (caseActions locations load) v
    have h := external_work_combination core a 0 load.1.1 load.1.2 load.1.1 load.1.2
      locations load.2 load.2 v
    have hs : (fun i => a*load.1.1 i+0*load.1.1 i) = (fun i => a*load.1.1 i) := by
      funext i; ring
    have he : (fun i => a*load.1.2 i+0*load.1.2 i) = (fun i => a*load.1.2 i) := by
      funext i; ring
    have hf : (fun j i => a*load.2 j i+0*load.2 j i) = (fun j i => a*load.2 j i) := by
      funext j i; ring
    rw [hs, he, hf] at h
    have hh : externalWork (caseModel core (a • load)) (caseActions locations (a • load)) v =
        a * externalWork (caseModel core load) (caseActions locations load) v := by
      simpa only [zero_mul, add_zero] using h
    exact (external_functional_apply (caseModel core (a • load)) (caseActions locations (a • load)) v).trans (hh.trans
      (congrArg (fun x : ℝ => a*x) (external_functional_apply (caseModel core load) (caseActions locations load) v).symm))

/-- Stable aggregate reaction as K composed with the stable solution map,
minus the independently derived load map. Individual support shares are not selected. -/
def stableReactionLinear (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (baseContract : ExactContract (withLoads core 0 0) (pointActions locations 0) supports cutsAt length EA EI)
    (baseStable : ∀ z, admissible (withLoads core 0 0) supports z →
      deformationMap (withLoads core 0 0) z = 0 → z = 0) :
    LoadCase segments actionCount →ₗ[ℝ] Module.Dual ℝ (Coordinate core → ℝ) :=
  (stiffnessOperator core).comp
    (stableSolutionLinear core locations supports cutsAt length EA EI baseContract baseStable) -
      externalLoadLinear core locations

theorem stable_reaction_is_residual (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (baseContract : ExactContract (withLoads core 0 0) (pointActions locations 0) supports cutsAt length EA EI)
    (baseStable : ∀ z, admissible (withLoads core 0 0) supports z →
      deformationMap (withLoads core 0 0) z = 0 → z = 0)
    (load : LoadCase segments actionCount) :
    residualFunctional (caseModel core load) (caseActions locations load)
      (stableSolutionLinear core locations supports cutsAt length EA EI baseContract baseStable load) =
    stableReactionLinear core locations supports cutsAt length EA EI baseContract baseStable load := by
  have hpositive := contract_positive_segments (caseModel core load) (caseActions locations load) supports
    cutsAt length EA EI (case_contract core locations supports cutsAt length EA EI baseContract load)
  rw [residual_eq_stiffness_minus_load _ _ _ hpositive]
  rfl


/-- The actual B map commutes with movement combinations. -/
theorem segment_dofs_combination (model : Model nodes members cuts segments)
    (a b : ℝ) (q₁ q₂ : Coordinate model → ℝ) (segment : Fin segments) :
    segmentDofs model (a • q₁ + b • q₂) segment =
      fun i => a * segmentDofs model q₁ segment i + b * segmentDofs model q₂ segment i := by
  funext i
  change segmentDofsLinear model segment (a • q₁ + b • q₂) i = _
  simp [map_add, map_smul, segmentDofsLinear, smul_eq_mul]

/-- Axial recovery through the assembled B map, for fixed segment properties. -/
theorem segment_axial_combination (model : Model nodes members cuts segments)
    (a b : ℝ) (q₁ q₂ : Coordinate model → ℝ) (segment : Fin segments) (p₀ p₁ r₀ r₁ : ℝ) :
    LocalFrameFields.axialDisplacement (segmentDofs model (a • q₁ + b • q₂) segment)
      (model.segmentLength segment) (model.segmentEA segment) (a*p₀+b*r₀) (a*p₁+b*r₁) =
    Polynomial.C a * LocalFrameFields.axialDisplacement (segmentDofs model q₁ segment)
      (model.segmentLength segment) (model.segmentEA segment) p₀ p₁ +
    Polynomial.C b * LocalFrameFields.axialDisplacement (segmentDofs model q₂ segment)
      (model.segmentLength segment) (model.segmentEA segment) r₀ r₁ := by
  rw [segment_dofs_combination]
  exact axial_recovery_combination _ _ a b _ _ p₀ p₁ r₀ r₁

/-- Transverse recovery through the same assembled B map. -/
theorem segment_transverse_combination (model : Model nodes members cuts segments)
    (a b : ℝ) (q₁ q₂ : Coordinate model → ℝ) (segment : Fin segments) (p₀ p₁ r₀ r₁ : ℝ) :
    LocalFrameFields.transverseDisplacement (segmentDofs model (a • q₁ + b • q₂) segment)
      (model.segmentLength segment) (model.segmentEI segment) (a*p₀+b*r₀) (a*p₁+b*r₁) =
    Polynomial.C a * LocalFrameFields.transverseDisplacement (segmentDofs model q₁ segment)
      (model.segmentLength segment) (model.segmentEI segment) p₀ p₁ +
    Polynomial.C b * LocalFrameFields.transverseDisplacement (segmentDofs model q₂ segment)
      (model.segmentLength segment) (model.segmentEI segment) r₀ r₁ := by
  rw [segment_dofs_combination]
  exact transverse_recovery_combination _ _ a b _ _ p₀ p₁ r₀ r₁

/-- The orientation map is linear for any fixed direction components. -/
theorem global_motion_combination (c s a b : ℝ) (v₁ v₂ : Triple) :
    toGlobal c s (fun i => a*v₁ i+b*v₂ i) =
      fun i => a*toGlobal c s v₁ i+b*toGlobal c s v₂ i := by
  funext i
  fin_cases i <;> simp [toGlobal] <;> ring


/-- A fixed hub component of the stable aggregate reaction is a linear
functional of the same load case. -/
def stableGroupedReactionLinear (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (baseContract : ExactContract (withLoads core 0 0) (pointActions locations 0) supports cutsAt length EA EI)
    (baseStable : ∀ z, admissible (withLoads core 0 0) supports z →
      deformationMap (withLoads core 0 0) z = 0 → z = 0)
    (point : ActivePoint core) (direction : Fin 3) : LoadCase segments actionCount →ₗ[ℝ] ℝ where
  toFun load := stableReactionLinear core locations supports cutsAt length EA EI baseContract baseStable load
    (coordinateBasis core (.inl (point, direction)))
  map_add' first second := by simp
  map_smul' a load := by simp

/-- A support-row representative projects to the same stable hub result.
The statement intentionally does not choose one representative of its gauge. -/
theorem stable_grouped_reaction_agrees (core : Model nodes members cuts segments)
    (locations : Fin actionCount → Location members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutsAt : Fin members → Fin cuts → ℝ) (length EA EI : Fin members → ℝ)
    (baseContract : ExactContract (withLoads core 0 0) (pointActions locations 0) supports cutsAt length EA EI)
    (baseStable : ∀ z, admissible (withLoads core 0 0) supports z →
      deformationMap (withLoads core 0 0) z = 0 → z = 0)
    (load : LoadCase segments actionCount) (coefficients : ConstraintIndex supports → ℝ)
    (h : residualFunctional (caseModel core load) (caseActions locations load)
      (stableSolutionLinear core locations supports cutsAt length EA EI baseContract baseStable load) =
        aggregateReaction core supports coefficients)
    (point : ActivePoint core) (direction : Fin 3) :
    stableGroupedReactionLinear core locations supports cutsAt length EA EI baseContract baseStable point direction load =
      groupedGroundAction core supports coefficients point direction := by
  have hres := stable_reaction_is_residual core locations supports cutsAt length EA EI baseContract baseStable load
  have hvalue := congrArg (fun reaction : Module.Dual ℝ (Coordinate core → ℝ) =>
    reaction (coordinateBasis core (.inl (point, direction)))) (hres.symm.trans h)
  exact hvalue

end
end FrameReuse
