import FrameSpring

namespace FrameSpring.Wire
open InclinedRelease InclinedRelease.Wire
open RationalFrame RationalFrame.Wire FrameIntervalOps
open InclinedFrameIntervalReport (intervalFields rationalFields)
open InclinedFrameIntervalBuild (tabulate)

structure Packet extends InclinedFrameIntervalWire.Packet where
  rules : Rules

def packet (fields : Array String) : Decoder Packet := do
  if (← token fields) != "CV2011_ROTATIONAL_SPRING_1" then throw ()
  let nodeCount ← natural fields 16
  let memberCount ← natural fields 8
  let supportCount ← natural fields 16
  let loadCount ← natural fields 16
  if nodeCount == 0 || memberCount == 0 then throw ()
  let mut joints := #[]
  let mut ends := #[]
  let mut stiffnesses := #[]
  let mut nodes : Array Node := #[]
  let mut members : Array Member := #[]
  let mut supports : Array Support := #[]
  let mut loads : Array Load := #[]
  for _ in [:nodeCount] do
    let id ← identifier fields
    let x ← rational fields
    let y ← rational fields
    let joint ← natural fields 3
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
    let endA ← natural fields 3
    let kA ← rational fields
    let endB ← natural fields 3
    let kB ← rational fields
    stiffnesses := (stiffnesses.push kA).push kB
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
  let original : Source := ⟨nodes, members, supports, loads⟩
  let rules : Rules := ⟨joints, ends, stiffnesses⟩
  let member ← natural fields (original.members.size - 1)
  let t ← rational fields
  let right ← natural fields 1
  let convention ← natural fields 1
  let query : Query := { member := member, t := t, right := right == 1, convention := convention }
  let bits ← natural fields 128
  if !precisionValid bits then throw ()

  -- Derive all dimensions from the original graph before reading dense data.
  let some (l, _) := resolve original rules | throw ()
  let basis := l.basis
  if !InclinedFrameIntervalRecovery.queryValid l.expanded query then throw ()
  let mut roots : Array Bounds := #[]
  for _ in [:original.members.size] do
    let lower ← rational fields
    let upper ← rational fields
    let bounds : Bounds := ⟨lower, upper⟩
    if !valid bounds then throw ()
    roots := roots.push bounds
  let mut inverse : Array (Array Rat) := #[]
  for _ in [:basis.columns.size] do
    inverse := inverse.push (← vector fields basis.columns.size)
  let estimate ← vector fields basis.columns.size
  if (← get) != fields.size then throw ()
  return ⟨⟨original, query, bits, roots, inverse, estimate⟩, rules⟩

/-- Reject oversized/non-ASCII input before splitting or allocating field arrays.
    The native ABI must enforce the same byte cap before constructing a String. -/
def decode (input : String) : Option Packet := do
  if input.utf8ByteSize > 1048576 then none else do
    let limits := input.foldl (fun (state : Nat × Bool) character =>
      (state.1 + (if character == '\n' then 1 else 0),
       state.2 && (character == '\n' || (character ≥ ' ' && character ≤ '~')))) (1, true)
    if limits.1 > 6000 || !limits.2 then none else do
      let fields := (input.splitOn "\n").toArray
      match (packet fields).run 0 with
      | .error _ => none
      | .ok (value, _) => some value

/-- Append each constitutive readout to the field report from the same solve. -/
def springValues (l : Layout) (bits : Nat) (c : Cert l) (side : Nat) (k : Rat) : Option (Bounds × Bounds) := do
  let own ← InclinedFrameIntervalRecovery.nodalMotion bits c (facePoint l side)
  let ref ← InclinedFrameIntervalRecovery.nodalMotion bits c (faceNode l side)
  let slip ← measure 3 (subtract bits (own 2) (ref 2))
  let moment ← measure 2 (multiply bits ⟨k,k⟩ slip.value)
  return (slip.value, moment.value)

def activeSides (l : Layout) (ks : Array Rat) := l.sides.filter fun side => ks[side]! > 0

abbrev Transfers (l : Layout) (ks : Array Rat) (bits : Nat) (c : Cert l) :=
  (i : Fin (activeSides l ks).size) →
    let side := (activeSides l ks)[i.val]!
    Evaluated (springValues l bits c side ks[side]!)

def readTransfers (l : Layout) (ks : Array Rat) (bits : Nat) (c : Cert l) : Option (Transfers l ks bits c) :=
  gather (activeSides l ks).size _ fun i =>
    let side := (activeSides l ks)[i.val]!
    evaluate (springValues l bits c side ks[side]!)

def encodeSprings (l : Layout) (ks : Array Rat) (bits : Nat) (c : Cert l)
    {q : RationalFrame.Query} (fields : Values l bits c q) (transfers : Transfers l ks bits c) : String := Id.run do
  let mut out := [InclinedRelease.Wire.encode fields, "CV2011_SPRINGS_1"]
  for i in List.finRange (activeSides l ks).size do
    let side := (activeSides l ks)[i.val]!
    let (slip, moment) := (transfers i).value
    out := out ++ [toString side] ++ rationalFields ks[side]! ++ intervalFields slip ++ intervalFields moment
  return String.intercalate "\n" out

def proposalFor (l : Layout) (value : Packet) : Option (InclinedFrameIntervalBuild.Proposal l.expanded l.basis) := do
  let n := l.basis.columns.size
  guard (value.roots.size == l.expanded.source.members.size && value.inverse.size == n &&
    value.estimate.size == n && value.inverse.all (fun row => row.size == n))
  return {
    roots := fun i => value.roots[i.val]!, inverse := fun i j => value.inverse[i.val]![j.val]!,
    estimate := fun i => value.estimate[i.val]! }

def report (value : Packet) : Option String := do
  let (l, ks) ← resolve value.source value.rules
  let proposal ← proposalFor l value
  let cert ← FrameSpring.build l ks value.bits proposal
  if FrameSpring.verified l ks value.bits cert then
    let fields ← readValues l value.bits cert value.query
    let transfers ← readTransfers l ks value.bits cert
    let result := encodeSprings l ks value.bits cert fields transfers
    if result.utf8ByteSize ≤ 262144 then some result else none
  else none

@[export frame_spring_report]
def checkReport (input : String) : Option String := do report (← decode input)

end FrameSpring.Wire
