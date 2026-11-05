import FramePotential

/-!
Exact, finite presegmented frame input. Original nodes have shared reference
coordinates; interior cut points belong to one member. This representation
intentionally does not claim that browser snapping or floating geometry has
been refined to these exact inputs.
-/
open FrameInterfaces FrameTransform

namespace FrameAssemblyModel

noncomputable section

inductive JointKind where
  | rigid | pinned | semiRigid | custom
  deriving DecidableEq

structure JointInput (members : Nat) where
  kind : JointKind
  rotationStiffness : ℝ
  requestedReference : Option (Fin members)

/-- A member end is identified by its member and by false=start, true=end. -/
abbrev MemberEnd (members : Nat) := Fin members × Bool

structure MemberInput (nodes : Nat) where
  startNode : Fin nodes
  endNode : Fin nodes
  orientation : Orientation
  explicitStart : Option EndConnection
  explicitEnd : Option EndConnection

inductive Location (members cuts : Nat) where
  | endSide (side : MemberEnd members)
  | interior (member : Fin members) (cut : Fin cuts)
  deriving DecidableEq

structure Model (nodes members cuts segments : Nat) where
  joints : Fin nodes → JointInput members
  member : Fin members → MemberInput nodes
  /-- Segment location and loading data are supplied after exact segmentation. -/
  segmentMember : Fin segments → Fin members
  segmentLeft : Fin segments → Location members cuts
  segmentRight : Fin segments → Location members cuts
  segmentLength : Fin segments → ℝ
  segmentEA : Fin segments → ℝ
  segmentEI : Fin segments → ℝ
  segmentVerticalStart : Fin segments → ℝ
  segmentVerticalEnd : Fin segments → ℝ

/-- List order matches the original member order used by the first-incident fallback. -/
def incident (model : Model nodes members cuts segments) (node : Fin nodes) (m : Fin members) : Bool :=
  decide ((model.member m).startNode = node ∨ (model.member m).endNode = node)

def referenceMember (model : Model nodes members cuts segments) (node : Fin nodes) : Option (Fin members) :=
  match (model.joints node).requestedReference with
  | some m => if incident model node m then some m else (List.finRange members).find? (incident model node)
  | none => (List.finRange members).find? (incident model node)

def endNode (model : Model nodes members cuts segments) (side : MemberEnd members) : Fin nodes :=
  if side.2 then (model.member side.1).endNode else (model.member side.1).startNode

def rigidConnection : EndConnection := ⟨.rigid, .rigid, .rigid⟩

/-- The reference side is rigid even if an explicit release was provided. -/
def endConnection (model : Model nodes members cuts segments) (side : MemberEnd members) : EndConnection :=
  let node := endNode model side
  if referenceMember model node = some side.1 then rigidConnection
  else
    let explicit := if side.2 then (model.member side.1).explicitEnd else (model.member side.1).explicitStart
    match explicit with
    | some connection => connection
    | none =>
      let joint := model.joints node
      let rotation := match joint.kind with
        | .pinned => EndLaw.released
        | .semiRigid => EndLaw.spring joint.rotationStiffness
        | _ => EndLaw.rigid
      ⟨.rigid, .rigid, rotation⟩

/-- Direction order is local axial, transverse, rotation. -/
def directionLaw (connection : EndConnection) (direction : Fin 3) : EndLaw :=
  if direction = 0 then connection.axial else if direction = 1 then connection.transverse else connection.rotation

/-- Interior points carry member ownership, so crossing members stay distinct. -/
abbrev Point (nodes members cuts : Nat) := Sum (Fin nodes) (Fin members × Fin cuts)

/-- The physical reference point selected by an end or member-owned cut. -/
def locationPoint (model : Model nodes members cuts segments) : Location members cuts → Point nodes members cuts
  | .endSide side => .inl (endNode model side)
  | .interior member cut => .inr (member, cut)

/-- Actual nodeIndex allocation occurs only at an endpoint of a segment. -/
def activePoint (model : Model nodes members cuts segments) (point : Point nodes members cuts) : Prop :=
  ∃ segment, locationPoint model (model.segmentLeft segment) = point ∨
    locationPoint model (model.segmentRight segment) = point

/-- End slips are allocated only for member ends represented by a segment. -/
def activeEnd (model : Model nodes members cuts segments) (side : MemberEnd members) : Prop :=
  ∃ segment, model.segmentLeft segment = .endSide side ∨ model.segmentRight segment = .endSide side

def hasSlip (model : Model nodes members cuts segments) (side : MemberEnd members) (direction : Fin 3) : Prop :=
  activeEnd model side ∧ directionLaw (endConnection model side) direction ≠ .rigid

/-- A slip coordinate exists only for an active free or spring end direction. -/
def Slip (model : Model nodes members cuts segments) :=
  { pair : MemberEnd members × Fin 3 // hasSlip model pair.1 pair.2 }

def ActivePoint (model : Model nodes members cuts segments) :=
  { point : Point nodes members cuts // activePoint model point }

abbrev Coordinate (model : Model nodes members cuts segments) :=
  Sum (ActivePoint model × Fin 3) (Slip model)

/-- On an unrepresented location this total helper returns zero. Physical
loads and supports must satisfy the represented-location input contract. -/
def referenceMotion (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (point : Point nodes members cuts) : Triple := by
  classical
  exact fun direction => if h : activePoint model point then q (.inl (⟨point, h⟩, direction)) else 0

/-- Slip is zero for rigid directions, which have no associated coordinate. -/
def slipValue (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (side : MemberEnd members) (direction : Fin 3) : ℝ := by
  classical
  exact if h : hasSlip model side direction then q (.inr ⟨(side, direction), h⟩) else 0

/-- H: global movement on the selected member side, with local slips rotated
into global axes. Interior cuts use the member-owned reference movement. -/
def sideMotion (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) : Location members cuts → Triple
  | .interior member cut => referenceMotion model q (.inr (member, cut))
  | .endSide side =>
      let orientation := (model.member side.1).orientation
      endMotion orientation.cosine orientation.sine
        (referenceMotion model q (.inl (endNode model side)))
        (slipValue model q side)

/-- B applies the local rotation to both selected end motions. -/
def segmentMotion (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (member : Fin members)
    (left right : Location members cuts) : LocalDofs :=
  let orientation := (model.member member).orientation
  let a := sideMotion model q left
  let b := sideMotion model q right
  toLocal6 orientation.cosine orientation.sine ![a 0, a 1, a 2, b 0, b 1, b 2]


/-- An explicit reference choice takes precedence, but only for an incident member. -/
theorem requested_incident_is_reference (model : Model nodes members cuts segments)
    (node : Fin nodes) (member : Fin members)
    (hrequest : (model.joints node).requestedReference = some member)
    (hincident : incident model node member = true) :
    referenceMember model node = some member := by
  simp [referenceMember, hrequest, hincident]

/-- The engine makes the reference member rigid independently of end overrides. -/
theorem reference_end_is_rigid (model : Model nodes members cuts segments)
    (side : MemberEnd members)
    (hreference : referenceMember model (endNode model side) = some side.1) :
    endConnection model side = rigidConnection := by
  simp [endConnection, hreference]

/-- A rigid direction has no member-side relative coordinate. -/
theorem rigid_direction_has_zero_slip (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (side : MemberEnd members) (direction : Fin 3)
    (hrigid : directionLaw (endConnection model side) direction = .rigid) :
    slipValue model q side direction = 0 := by
  classical
  simp [slipValue, hasSlip, hrigid]

/-- Interior cut points do not connect different original members. -/
theorem distinct_member_cuts (member₁ member₂ : Fin members) (cut₁ cut₂ : Fin cuts)
    (h : member₁ ≠ member₂) :
    (Sum.inr (member₁, cut₁) : Point nodes members cuts) ≠ Sum.inr (member₂, cut₂) := by
  intro heq
  cases heq
  exact h rfl

inductive SupportKind where
  | pin | fixed | roller | guided | custom
  deriving DecidableEq

/-- Inclined directions are exact inputs; deriving them from a drawn angle is
outside this presegmented model. Custom supports use flags and ignore angle. -/
structure SupportInput (members cuts : Nat) where
  location : Location members cuts
  kind : SupportKind
  cosine : ℝ
  sine : ℝ
  fixX : Bool
  fixY : Bool
  fixRotation : Bool

/-- Up to three blocked global directions, in the engine's support order. -/
def supportDirections (support : SupportInput members cuts) : List Triple :=
  let x : Triple := ![1, 0, 0]
  let y : Triple := ![0, 1, 0]
  let rotation : Triple := ![0, 0, 1]
  let inclined : Triple := ![support.cosine, support.sine, 0]
  match support.kind with
  | .pin => [x, y]
  | .fixed => [x, y, rotation]
  | .roller => [inclined]
  | .guided => [rotation, inclined]
  | .custom => (if support.fixX then [x] else []) ++
      (if support.fixY then [y] else []) ++ (if support.fixRotation then [rotation] else [])

/-- Each constraint acts on the selected member side, including its slip. -/
def supportRow (model : Model nodes members cuts segments) (support : SupportInput members cuts)
    (direction : Triple) (q : Coordinate model → ℝ) : ℝ :=
  work direction (sideMotion model q support.location)

/-- A direct point action retains its member-side owner. -/
structure PointAction (members cuts : Nat) where
  location : Location members cuts
  globalAction : Triple

def pointActionWork (model : Model nodes members cuts segments)
    (action : PointAction members cuts) (q : Coordinate model → ℝ) : ℝ :=
  work action.globalAction (sideMotion model q action.location)

/-- The stored distributed intensity is global vertical, not an independent
global horizontal intensity. -/
def segmentLoad (model : Model nodes members cuts segments) (segment : Fin segments) : LocalActions :=
  let orientation := (model.member (model.segmentMember segment)).orientation
  let q₀ := model.segmentVerticalStart segment
  let q₁ := model.segmentVerticalEnd segment
  LocalFrameFields.consistentLoad (model.segmentLength segment)
    (orientation.sine*q₀) (orientation.sine*q₁)
    (orientation.cosine*q₀) (orientation.cosine*q₁)

/-- A segment endpoint belongs to the same original member, whether it is
an original end or an interior cut. This excludes accidental cross-member cuts. -/
def locationBelongs (member : Fin members) : Location members cuts → Prop
  | .endSide side => side.1 = member
  | .interior owner _ => owner = member

def segmentOwnershipValid (model : Model nodes members cuts segments) : Prop :=
  ∀ segment, locationBelongs (model.segmentMember segment) (model.segmentLeft segment) ∧
    locationBelongs (model.segmentMember segment) (model.segmentRight segment)

/-- A segment takes both ends from the actual presegmented model. -/
def segmentDofs (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (segment : Fin segments) : LocalDofs :=
  segmentMotion model q (model.segmentMember segment)
    (model.segmentLeft segment) (model.segmentRight segment)


/-- End mapping is linear in the complete coordinate vector, including slips. -/
theorem side_motion_add (model : Model nodes members cuts segments)
    (q r : Coordinate model → ℝ) (location : Location members cuts) :
    sideMotion model (q + r) location = sideMotion model q location + sideMotion model r location := by
  classical
  cases location with
  | interior member cut =>
      funext i
      simp [sideMotion, referenceMotion, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
  | endSide side =>
      funext i
      fin_cases i <;>
        simp [sideMotion, referenceMotion, endMotion, slipValue, Pi.add_apply] <;>
        split_ifs <;> ring

/-- End mapping preserves scaling of reference movements and member-side slips. -/
theorem side_motion_smul (model : Model nodes members cuts segments)
    (a : ℝ) (q : Coordinate model → ℝ) (location : Location members cuts) :
    sideMotion model (a • q) location = a • sideMotion model q location := by
  classical
  cases location with
  | interior member cut =>
      funext i
      simp [sideMotion, referenceMotion, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
  | endSide side =>
      funext i
      fin_cases i <;>
        simp [sideMotion, referenceMotion, endMotion, slipValue, Pi.smul_apply, smul_eq_mul] <;>
        split_ifs <;> ring

/-- The actual end builder as a linear map H. -/
def sideMotionLinear (model : Model nodes members cuts segments)
    (location : Location members cuts) : (Coordinate model → ℝ) →ₗ[ℝ] Triple where
  toFun := fun q => sideMotion model q location
  map_add' := fun q r => side_motion_add model q r location
  map_smul' := fun a q => side_motion_smul model a q location


/-- Both endpoints of an encoded segment necessarily allocate a reference point. -/
theorem segment_left_point_active (model : Model nodes members cuts segments) (segment : Fin segments) :
    activePoint model (locationPoint model (model.segmentLeft segment)) :=
  ⟨segment, Or.inl rfl⟩

theorem segment_right_point_active (model : Model nodes members cuts segments) (segment : Fin segments) :
    activePoint model (locationPoint model (model.segmentRight segment)) :=
  ⟨segment, Or.inr rfl⟩

/-- An action or support must be attached to an actual presegmented location. -/
def representedLocation (model : Model nodes members cuts segments) (location : Location members cuts) : Prop :=
  ∃ segment, model.segmentLeft segment = location ∨ model.segmentRight segment = location

/-- Position along an original member, before any floating-point snapping. -/
def locationParameter (cutParameter : Fin members → Fin cuts → ℝ) : Location members cuts → ℝ
  | .endSide (_, false) => 0
  | .endSide (_, true) => 1
  | .interior member cut => cutParameter member cut

/-- Exact presegmentation assumptions, separate from drawing and numerical
refinement. Segment interiors partition each member; their end locations also
cover all selected point actions and support rows. -/
structure ExactContract (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (memberLength memberEA memberEI : Fin members → ℝ) : Prop where
  ownership : segmentOwnershipValid model
  ordered : ∀ segment,
    0 ≤ locationParameter cutParameter (model.segmentLeft segment) ∧
    locationParameter cutParameter (model.segmentLeft segment) <
      locationParameter cutParameter (model.segmentRight segment) ∧
    locationParameter cutParameter (model.segmentRight segment) ≤ 1
  coverage : ∀ member t, 0 ≤ t → t ≤ 1 → ∃ segment,
    model.segmentMember segment = member ∧
    locationParameter cutParameter (model.segmentLeft segment) ≤ t ∧
    t ≤ locationParameter cutParameter (model.segmentRight segment)
  disjointInteriors : ∀ a b, a ≠ b → model.segmentMember a = model.segmentMember b →
    locationParameter cutParameter (model.segmentRight a) ≤ locationParameter cutParameter (model.segmentLeft b) ∨
    locationParameter cutParameter (model.segmentRight b) ≤ locationParameter cutParameter (model.segmentLeft a)
  memberEnds : ∀ member, representedLocation model (.endSide (member, false)) ∧
    representedLocation model (.endSide (member, true))
  interiorCuts : ∀ member cut, representedLocation model (.interior member cut) →
    0 < cutParameter member cut ∧ cutParameter member cut < 1
  actionLocations : ∀ action, representedLocation model (actions action).location
  supportLocations : ∀ support, representedLocation model (supports support).location
  orientationNormalized : ∀ member,
    (model.member member).orientation.cosine^2 + (model.member member).orientation.sine^2 = 1
  positiveMember : ∀ member, 0 < memberLength member ∧ 0 < memberEA member ∧ 0 < memberEI member
  segmentLengthMatches : ∀ segment,
    model.segmentLength segment = memberLength (model.segmentMember segment) *
      (locationParameter cutParameter (model.segmentRight segment) -
       locationParameter cutParameter (model.segmentLeft segment))
  segmentPropertiesMatch : ∀ segment,
    model.segmentEA segment = memberEA (model.segmentMember segment) ∧
    model.segmentEI segment = memberEI (model.segmentMember segment)
  positiveSpring : ∀ side direction stiffness, activeEnd model side →
    directionLaw (endConnection model side) direction = .spring stiffness → 0 < stiffness

/-- The segment transformation B is built from the two actual member-side
end maps and the segment's local axes. -/
theorem segment_dofs_add (model : Model nodes members cuts segments)
    (q r : Coordinate model → ℝ) (segment : Fin segments) :
    segmentDofs model (q+r) segment = segmentDofs model q segment + segmentDofs model r segment := by
  funext i
  fin_cases i <;>
    simp [segmentDofs, segmentMotion, toLocal6, side_motion_add, Pi.add_apply] <;> ring

theorem segment_dofs_smul (model : Model nodes members cuts segments)
    (a : ℝ) (q : Coordinate model → ℝ) (segment : Fin segments) :
    segmentDofs model (a • q) segment = a • segmentDofs model q segment := by
  funext i
  fin_cases i <;>
    simp [segmentDofs, segmentMotion, toLocal6, side_motion_smul, Pi.smul_apply, smul_eq_mul] <;> ring

def segmentDofsLinear (model : Model nodes members cuts segments) (segment : Fin segments) :
    (Coordinate model → ℝ) →ₗ[ℝ] LocalDofs where
  toFun := fun q => segmentDofs model q segment
  map_add' := fun q r => segment_dofs_add model q r segment
  map_smul' := fun a q => segment_dofs_smul model a q segment


/-- A support row is a linear functional of the complete model coordinates. -/
def supportRowLinear (model : Model nodes members cuts segments)
    (support : SupportInput members cuts) (direction : Triple) :
    (Coordinate model → ℝ) →ₗ[ℝ] ℝ where
  toFun := supportRow model support direction
  map_add' := by
    intro q r
    simp [supportRow, side_motion_add, work, Pi.add_apply]
    ring
  map_smul' := by
    intro a q
    simp [supportRow, side_motion_smul, work, Pi.smul_apply, smul_eq_mul]
    ring

/-- Constraint indices retain duplicate rows and their separate ownership. -/
abbrev ConstraintIndex (supports : Fin supportCount → SupportInput members cuts) :=
  Σ support : Fin supportCount, Fin (supportDirections (supports support)).length

/-- C maps model coordinates to every actual member-side support row. -/
def constraintMap (model : Model nodes members cuts segments)
    (supports : Fin supportCount → SupportInput members cuts) :
    (Coordinate model → ℝ) →ₗ[ℝ] (ConstraintIndex supports → ℝ) where
  toFun := fun q row => supportRowLinear model (supports row.1)
    ((supportDirections (supports row.1)).get row.2) q
  map_add' := by
    intro q r
    funext row
    exact map_add (supportRowLinear model (supports row.1)
      ((supportDirections (supports row.1)).get row.2)) q r
  map_smul' := by
    intro a q
    funext row
    exact map_smul (supportRowLinear model (supports row.1)
      ((supportDirections (supports row.1)).get row.2)) a q

end
end FrameAssemblyModel
