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

def hasSlip (model : Model nodes members cuts segments) (side : MemberEnd members) (direction : Fin 3) : Prop :=
  directionLaw (endConnection model side) direction ≠ .rigid

/-- A slip coordinate exists exactly when the end law is free or spring. -/
def Slip (model : Model nodes members cuts segments) :=
  { pair : MemberEnd members × Fin 3 // hasSlip model pair.1 pair.2 }

/-- Interior points carry member ownership, so crossing members stay distinct. -/
abbrev Point (nodes members cuts : Nat) := Sum (Fin nodes) (Fin members × Fin cuts)

abbrev Coordinate (model : Model nodes members cuts segments) :=
  Sum (Point nodes members cuts × Fin 3) (Slip model)

/-- The physical reference point selected by an end or member-owned cut. -/
def locationPoint (model : Model nodes members cuts segments) : Location members cuts → Point nodes members cuts
  | .endSide side => .inl (endNode model side)
  | .interior member cut => .inr (member, cut)

/-- Reference global movement at any exact point, before member-end slip. -/
def referenceMotion (model : Model nodes members cuts segments)
    (q : Coordinate model → ℝ) (point : Point nodes members cuts) : Triple :=
  fun direction => q (.inl (point, direction))

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

end
end FrameAssemblyModel
