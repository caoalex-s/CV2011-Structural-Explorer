import RealBeamFields

/-!
Pending interfaces for the next frame-proof phases. These are data structures
only: no element stiffness, transformation, connection, assembly, stability, or
solver theorem is asserted by their presence. Input validation and semantic
links to the browser model remain future proof obligations.
-/
namespace FrameInterfaces

/-- Local end displacement order: u₁, v₁, θ₁, u₂, v₂, θ₂. -/
abbrev LocalDofs := Fin 6 → ℝ

/-- Local end action order follows the same six positions as the displacements. -/
abbrev LocalActions := Fin 6 → ℝ

structure MemberParameters where
  length : ℝ
  axialRigidity : ℝ
  flexuralRigidity : ℝ

/-- The unit-direction condition and geometry correspondence are not yet proved. -/
structure Orientation where
  cosine : ℝ
  sine : ℝ

/-- A finite spring requires a positive stiffness in any applicable theorem. -/
inductive EndLaw where
  | rigid
  | released
  | spring (stiffness : ℝ)

structure EndConnection where
  axial : EndLaw
  transverse : EndLaw
  rotation : EndLaw

/-- Consistent end actions and the local field must later be linked by proof. -/
structure LocalMemberState where
  displacement : LocalDofs
  action : LocalActions
  axialForce : RealBeamFields.Field
  shear : RealBeamFields.Field
  moment : RealBeamFields.Field
  axialDisplacement : RealBeamFields.Field
  transverseDisplacement : RealBeamFields.Field
  rotation : RealBeamFields.Field

end FrameInterfaces
