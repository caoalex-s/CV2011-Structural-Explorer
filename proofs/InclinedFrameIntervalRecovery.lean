import InclinedFrameIntervalAssembly
import FrameIntervalRecovery

/-! Source-owned recovery evaluation. The decoder binds the original query;
    one-sided selection is checked against the source partition. Stored nodal
    intervals are not inputs: they are obtained from checked column bounds. -/
namespace InclinedFrameIntervalRecovery
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly FrameIntervalOps

def SideContains (piece : Piece) (query : RationalFrame.Query) : Prop :=
  piece.member = query.member ∧ if query.right then piece.left ≤ query.t ∧ query.t < piece.right
    else piece.left < query.t ∧ query.t ≤ piece.right

instance (piece : Piece) (query : RationalFrame.Query) : Decidable (SideContains piece query) := by
  unfold SideContains
  infer_instance

def selectedPiece (data : Partition) (query : RationalFrame.Query) : Option (Fin data.pieces.size) :=
  (List.finRange data.pieces.size).find? (fun index => decide (SideContains data.pieces[index.val]! query))

def queryValid (data : Partition) (query : RationalFrame.Query) : Bool :=
  query.member < data.source.members.size && decide (0 ≤ query.t ∧ query.t ≤ 1) && query.convention == 1 &&
    (query.t != 0 || query.right) && (query.t != 1 || !query.right) &&
    match selectedPiece data query with
    | none => false
    | some index => decide (SideContains data.pieces[index.val]! query)

def nodalMotion {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (point : Nat) : Option (Fin 3 → Bounds) := do
  let horizontal ← FrameIntervalVector.dot bits
    (fun column => pointColumnAt certificate point column 0) certificate.solve.solution
  let vertical ← FrameIntervalVector.dot bits
    (fun column => pointColumnAt certificate point column 1) certificate.solve.solution
  let rotation ← FrameIntervalVector.dot bits
    (fun column => pointColumnAt certificate point column 2) certificate.solve.solution
  some ![horizontal, vertical, rotation]

def localMotion {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (index : Fin data.pieces.size) : Option (Fin 6 → Bounds) := do
  let segment := data.pieces[index.val]!
  let first ← nodalMotion bits certificate segment.a
  let second ← nodalMotion bits certificate segment.b
  FrameIntervalTransform.localPiece bits (certificate.geometry index).cosine
    (certificate.geometry index).sine first second

def endAction {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (index : Fin data.pieces.size) (motion : Fin 6 → Bounds) (component : Fin 6) : Option Bounds := do
  let elastic ← FrameIntervalVector.dot bits (localStiffness certificate index component) motion
  subtract bits elastic (certificate.distributed index component)

/-- Keep the fixed input layout separate from the monadic arithmetic sequence.
    Component order is exactly the source-authored recovery expression order. -/
@[noinline] def inputVector (actionX actionY actionMoment : Bounds) (motion : Fin 6 → Bounds)
    (p dp q dq x EA EI cosine sine : Bounds) : Fin 15 → Bounds :=
  ![actionX, actionY, actionMoment, motion 0, motion 1, motion 2,
    p, dp, q, dq, x, EA, EI, cosine, sine]

structure LoadComponents where
  p : Bounds
  pEnd : Bounds
  q : Bounds
  qEnd : Bounds

/-- Project both affine load endpoints before forming either slope. -/
@[noinline] def loadComponents (bits : Nat) (segment : Piece)
    (geometry : InclinedFrameIntervalGeometry.PieceBounds) : Option LoadComponents := do
  let left ← point bits segment.vertical
  let right ← point bits segment.verticalEnd
  let p ← multiply bits geometry.sine left
  let pEnd ← multiply bits geometry.sine right
  let q ← multiply bits geometry.cosine left
  let qEnd ← multiply bits geometry.cosine right
  some ⟨p, pEnd, q, qEnd⟩

structure LoadSlopes where
  dp : Bounds
  dq : Bounds

@[noinline] def loadSlopes (bits : Nat) (loads : LoadComponents)
    (length : Bounds) : Option LoadSlopes := do
  let pChange ← subtract bits loads.pEnd loads.p
  let qChange ← subtract bits loads.qEnd loads.q
  let dp ← divide bits pChange length
  let dq ← divide bits qChange length
  some ⟨dp, dq⟩

structure PositionMaterial where
  x : Bounds
  EA : Bounds
  EI : Bounds

@[noinline] def positionMaterial (bits : Nat) (segment : Piece)
    (parameter : Rat) (length : Bounds) (axial flexural : Rat) : Option PositionMaterial := do
  let offset ← point bits ((parameter-segment.left)/(segment.right-segment.left))
  let x ← multiply bits length offset
  let EA ← point bits axial
  let EI ← point bits flexural
  some ⟨x, EA, EI⟩

/-- Build the fixed fifteen field inputs from the same source piece and
    enclosed solved motion, including affine slopes and actual physical x. -/
def fieldInputs {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (index : Fin data.pieces.size) (parameter : Rat) : Option (Fin 15 → Bounds) := do
  let segment := data.pieces[index.val]!
  let member := data.source.members[segment.member]!
  let geometry := certificate.geometry index
  let motion ← localMotion bits certificate index
  let actionX ← endAction bits certificate index motion 0
  let actionY ← endAction bits certificate index motion 1
  let actionMoment ← endAction bits certificate index motion 2
  let loads ← loadComponents bits segment geometry
  let slopes ← loadSlopes bits loads geometry.length
  let properties ← positionMaterial bits segment parameter geometry.length member.EA member.EI
  some (inputVector actionX actionY actionMoment motion
    loads.p slopes.dp loads.q slopes.dq properties.x properties.EA properties.EI geometry.cosine geometry.sine)

def field {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (query : RationalFrame.Query) (component : Fin 6) : Option Bounds := do
  if !queryValid data query then none else
    let index ← selectedPiece data query
    let inputs ← fieldInputs bits certificate index query.t
    FrameIntervalRecovery.field bits inputs component

end InclinedFrameIntervalRecovery
