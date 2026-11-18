import HingeFrameChecker

namespace HingeFrame.Wire
open RationalFrame
open RationalFrame.Wire (Decoder token natural rational identifier vector)

structure HingePacket extends RationalFrame.Wire.Packet where
  rules : Connections

def packet (fields : Array String) : Decoder HingePacket := do
  if (← token fields) != "CV2011_HINGE_1" then throw ()
  let nodeCount ← natural fields 16
  let memberCount ← natural fields 8
  let supportCount ← natural fields 16
  let loadCount ← natural fields 16
  if nodeCount == 0 || memberCount == 0 then throw ()
  let mut joints := #[]
  let mut ends := #[]
  let mut nodes : Array Node := #[]
  let mut members : Array Member := #[]
  let mut supports : Array Support := #[]
  let mut loads : Array Load := #[]
  for _ in [:nodeCount] do
    let id ← identifier fields
    let x ← rational fields
    let y ← rational fields
    let joint ← natural fields 2
    joints := joints.push joint
    let reference ← natural fields memberCount
    let rotationStiffness ← rational fields
    nodes := nodes.push {
      id := id, x := x, y := y, joint := 0,
      reference := if reference == 0 then none else some (reference - 1),
      rotationStiffness := rotationStiffness }
  for _ in [:memberCount] do
    let id ← identifier fields
    let a ← natural fields (nodeCount - 1)
    let b ← natural fields (nodeCount - 1)
    let EA ← rational fields
    let EI ← rational fields
    let endA ← natural fields 2
    let endB ← natural fields 2
    ends := (ends.push endA).push endB
    members := members.push { id := id, a := a, b := b, EA := EA, EI := EI, rigidEnds := true }
  for _ in [:supportCount] do
    let id ← identifier fields
    let member ← natural fields (memberCount - 1)
    let t ← rational fields
    let kind ← natural fields 2
    let angle ← rational fields
    supports := supports.push { id := id, member := member, t := t, kind := kind, angle := angle }
  for _ in [:loadCount] do
    let id ← identifier fields
    let member ← natural fields (memberCount - 1)
    let kind ← natural fields 2
    let t ← rational fields
    let ending ← rational fields
    let fx ← rational fields
    let fy ← rational fields
    let mz ← rational fields
    let qEnd ← rational fields
    loads := loads.push {
      id := id, member := member, kind := kind, t := t,
      ending := ending, fx := fx, fy := fy, mz := mz, qEnd := qEnd }
  let member ← natural fields (memberCount - 1)
  let t ← rational fields
  let right ← natural fields 1
  let convention ← natural fields 1
  let mechanism ← natural fields 1
  let motionCount ← natural fields 48
  let freeCount ← natural fields 48
  let pointCount ← natural fields 16
  if motionCount ≤ 3 * pointCount then throw ()
  let mut points : Array Point := #[]
  for _ in [:pointCount] do
    let owned ← natural fields 1
    let index ← natural fields (if owned == 0 then nodeCount - 1 else memberCount - 1)
    let parameter ← rational fields
    let x ← rational fields
    let y ← rational fields
    points := points.push {
      owner := if owned == 0 then none else some index,
      index := index, t := parameter, x := x, y := y }
  let motion ← vector fields motionCount
  let mut reactions := #[]
  let mut lower := #[]
  let mut diagonal := #[]
  let mut readouts := #[]
  if mechanism == 0 then
    reactions ← vector fields motionCount
    for _ in [:freeCount] do lower := lower.push (← vector fields freeCount)
    diagonal ← vector fields freeCount
    readouts ← vector fields 6
  else if freeCount != 0 then throw ()
  let loadWork ← rational fields
  if (← get) != fields.size then throw ()
  return {
    rules := ⟨joints, ends⟩
    source := { nodes := nodes, members := members, supports := supports, loads := loads }
    query := { member := member, t := t, right := right == 1, convention := convention }
    certificate := {
      mechanism := mechanism == 1, points := points, motion := motion, reactions := reactions,
      lower := lower, diagonal := diagonal, readouts := readouts, loadWork := loadWork } }

/-- The C entry performs the same byte/line caps before constructing a String.
    These bounds also protect direct native calls used by the Linux CI tests. -/
def decode (input : String) : Option HingePacket := do
  if input.utf8ByteSize > 1048576 then none else do
    -- Count and reject non-ASCII bytes before allocating the field array.
    let limits := input.foldl (fun (state : Nat × Bool) character =>
      (state.1 + (if character == '\n' then 1 else 0),
       state.2 && (character == '\n' || (character ≥ ' ' && character ≤ '~')))) (1, true)
    if limits.1 > 6000 || !limits.2 then none else do
      let fields := (input.splitOn "\n").toArray
      match (packet fields).run 0 with
      | .error _ => none
      | .ok (value, _) => some value

@[export hinge_frame_check]
def checkString (input : String) : UInt32 :=
  match decode input with
  | none => 2
  | some value => if HingeFrame.accepts value.source value.rules value.query value.certificate then 1 else 0

end HingeFrame.Wire
