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

end
end FrameReuse
