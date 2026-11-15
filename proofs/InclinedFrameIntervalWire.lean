import RationalFrameWire
import InclinedFrameIntervalBuild

/-! Compact bounded inclined-frame packet. Only original source/query data and
    root/inverse/estimate proposals cross this boundary. Partition, support
    basis, interval tables and returned outputs are reconstructed by Lean.
    This draft has no exported ABI or browser acceptance path. -/
namespace InclinedFrameIntervalWire
open RationalFrame RationalFrame.Wire FrameIntervalOps

structure Packet where
  source : Source
  query : Query
  bits : Nat
  roots : Array Bounds
  inverse : Array (Array Rat)
  estimate : Array Rat

/-- Parse the established canonical source fields with the same primitive
    digit, identifier and dimension limits as the exact-cardinal protocol. -/
def source (fields : Array String) : Decoder Source := do
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
  return { nodes := nodes, members := members, supports := supports, loads := loads }

def packet (fields : Array String) : Decoder Packet := do
  if (← token fields) != "CV2011_INCLINED_1" then throw ()
  let original ← source fields
  let member ← natural fields (original.members.size - 1)
  let t ← rational fields
  let right ← natural fields 1
  let convention ← natural fields 1
  let query : Query := { member := member, t := t, right := right == 1, convention := convention }
  let bits ← natural fields 128
  if !precisionValid bits then throw ()

  -- Derive all dimensions from the original graph before reading dense data.
  let some data := InclinedFrameSource.checkedPartition original | throw ()
  let some basis := InclinedFrameBasis.checkedGlobalBasis data | throw ()
  if InclinedFrameIntervalBuild.workScore data basis > 2000000 ||
      !InclinedFrameIntervalRecovery.queryValid data query then throw ()
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
  return ⟨original, query, bits, roots, inverse, estimate⟩

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

structure Result where
  data : InclinedFrameSource.Partition
  outputs : InclinedFrameIntervalOutputs.Outputs data

/-- Recheck dimensions for direct typed callers too. No packet-supplied graph,
    support allocation, interval table or readout can replace reconstructed data. -/
def checkPacket (value : Packet) : Option Result := do
  let data ← InclinedFrameSource.checkedPartition value.source
  let basis ← InclinedFrameBasis.checkedGlobalBasis data
  if value.roots.size != data.source.members.size || value.inverse.size != basis.columns.size ||
      value.estimate.size != basis.columns.size ||
      !(value.inverse.all (fun row => row.size == basis.columns.size)) then none else
    let proposal : InclinedFrameIntervalBuild.Proposal data basis := {
      roots := fun index => value.roots[index.val]!,
      inverse := fun row column => (value.inverse[row.val]!)[column.val]!,
      estimate := fun row => value.estimate[row.val]! }
    let outputs ← InclinedFrameIntervalBuild.checked value.bits proposal value.query
    return ⟨data, outputs⟩

def decodeAndCheck (input : String) : Option Result := do
  let value ← decode input
  checkPacket value

end InclinedFrameIntervalWire
