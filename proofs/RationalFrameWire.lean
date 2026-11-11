import RationalFrameChecker

/-! Bounded canonical source/witness decoder. This module never accepts a
    caller-created Compiled record. Counts are checked before array allocation;
    the entry always calls RationalFrame.accepts on the decoded source. -/
namespace RationalFrame.Wire

structure Packet where
  source : Source
  query : Query
  certificate : Certificate

abbrev Decoder := StateT Nat (Except Unit)

def token (fields : Array String) : Decoder String := do
  let index ← get
  if index ≥ fields.size then throw ()
  set (index + 1)
  return fields[index]!

def natural (fields : Array String) (maximum : Nat) : Decoder Nat := do
  let text ← token fields
  if text.isEmpty || text.length > 3 || !(text.toList.all Char.isDigit) then throw ()
  let some value := text.toNat? | throw ()
  if toString value != text || value > maximum then throw ()
  return value

def rational (fields : Array String) : Decoder Rat := do
  let numerator ← token fields
  let denominator ← token fields
  if numerator.isEmpty || denominator.isEmpty || numerator.length > 129 || denominator.length > 128 then throw ()
  let digits := if numerator.startsWith "-" then numerator.drop 1 else numerator
  if digits.isEmpty || digits.length > 128 || !(digits.toList.all Char.isDigit) then throw ()
  if !(denominator.toList.all Char.isDigit) then throw ()
  let some n := numerator.toInt? | throw ()
  let some d := denominator.toNat? | throw ()
  if d == 0 || toString n != numerator || toString d != denominator then throw ()
  let value := mkRat n d
  -- Reduced form prevents equivalent encodings from evading packet identity.
  if value.num != n || value.den != d then throw ()
  return value

def identifier (fields : Array String) : Decoder String := do
  let value ← token fields
  if value.isEmpty || value.length > 1024 || value.length % 4 != 0 then throw ()
  if !(value.toList.all fun c => c.isDigit || (c ≥ 'a' && c ≤ 'f')) then throw ()
  return value

def vector (fields : Array String) (count : Nat) : Decoder (Array Rat) := do
  if count > 48 then throw ()
  let mut values := #[]
  for _ in [:count] do values := values.push (← rational fields)
  return values

def packet (fields : Array String) : Decoder Packet := do
  if (← token fields) != "CV2011_FRAME_1" then throw ()
  let nodeCount ← natural fields 16
  let memberCount ← natural fields 8
  let supportCount ← natural fields 16
  let loadCount ← natural fields 16
  if nodeCount == 0 || memberCount == 0 then throw ()
  let mut nodes : Array Node := #[]
  let mut members : Array Member := #[]
  let mut supports : Array Support := #[]
  let mut loads : Array Load := #[]
  for _ in [:nodeCount] do
    let id ← identifier fields
    let x ← rational fields
    let y ← rational fields
    let joint ← natural fields 0
    let reference ← natural fields memberCount
    let rotationStiffness ← rational fields
    nodes := nodes.push {
      id := id, x := x, y := y, joint := joint,
      reference := if reference == 0 then none else some (reference - 1),
      rotationStiffness := rotationStiffness }
  for _ in [:memberCount] do
    let id ← identifier fields
    let a ← natural fields (nodeCount - 1)
    let b ← natural fields (nodeCount - 1)
    let EA ← rational fields
    let EI ← rational fields
    let rigidEnds ← natural fields 1
    members := members.push { id := id, a := a, b := b, EA := EA, EI := EI, rigidEnds := rigidEnds == 1 }
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
    source := { nodes := nodes, members := members, supports := supports, loads := loads }
    query := { member := member, t := t, right := right == 1, convention := convention }
    certificate := {
      mechanism := mechanism == 1, motion := motion, reactions := reactions,
      lower := lower, diagonal := diagonal, readouts := readouts, loadWork := loadWork } }

/-- The C entry performs the same byte/line caps before constructing a String.
    These bounds also protect direct native calls used by the Linux CI tests. -/
def decode (input : String) : Option Packet := do
  if input.utf8ByteSize > 1048576 then none else do
    let fields := (input.splitOn "\n").toArray
    if fields.size > 6000 then none else
      match (packet fields).run 0 with
      | .error _ => none
      | .ok (value, _) => some value

@[export frame_check]
def checkString (input : String) : UInt32 :=
  match decode input with
  | none => 2
  | some value => if accepts value.source value.query value.certificate then 1 else 0

end RationalFrame.Wire
