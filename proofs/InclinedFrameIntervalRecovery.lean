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
  let left ← point bits segment.vertical
  let right ← point bits segment.verticalEnd
  let p ← multiply bits geometry.sine left
  let pEnd ← multiply bits geometry.sine right
  let q ← multiply bits geometry.cosine left
  let qEnd ← multiply bits geometry.cosine right
  let pChange ← subtract bits pEnd p
  let qChange ← subtract bits qEnd q
  let dp ← divide bits pChange geometry.length
  let dq ← divide bits qChange geometry.length
  let offset ← point bits ((parameter-segment.left)/(segment.right-segment.left))
  let x ← multiply bits geometry.length offset
  let EA ← point bits member.EA
  let EI ← point bits member.EI
  some ![actionX, actionY, actionMoment, motion 0, motion 1, motion 2,
    p, dp, q, dq, x, EA, EI, geometry.cosine, geometry.sine]

def field {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (query : RationalFrame.Query) (component : Fin 6) : Option Bounds := do
  if !queryValid data query then none else
    let index ← selectedPiece data query
    let inputs ← fieldInputs bits certificate index query.t
    FrameIntervalRecovery.field bits inputs component

end InclinedFrameIntervalRecovery
