import InclinedRelease

namespace InclinedRelease.Wire
open RationalFrame RationalFrame.Wire FrameIntervalOps
open InclinedFrameIntervalReport (intervalFields rationalFields)
open InclinedFrameIntervalBuild (tabulate)

structure Packet extends InclinedFrameIntervalWire.Packet where
  rules : HingeFrame.Connections

def packet (fields : Array String) : Decoder Packet := do
  if (← token fields) != "CV2011_INCLINED_RELEASE_1" then throw ()
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
  let original : Source := ⟨nodes, members, supports, loads⟩
  let rules : HingeFrame.Connections := ⟨joints, ends⟩
  let member ← natural fields (original.members.size - 1)
  let t ← rational fields
  let right ← natural fields 1
  let convention ← natural fields 1
  let query : Query := { member := member, t := t, right := right == 1, convention := convention }
  let bits ← natural fields 128
  if !precisionValid bits then throw ()

  -- Derive all dimensions from the original graph before reading dense data.
  let some l := layout original rules | throw ()
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

/-- Sum residuals on all ends sharing a joint. Relative hinge forces cancel
    and the total is the ground reaction at the original source point. -/
def resultFields (l : Layout) (bits : Nat) (cert : InclinedFrameIntervalAssembly.Certificate l.expanded l.basis)
    (q : Query) : Option (List String) := do
  let fields ← tabulate 6 fun component => InclinedFrameIntervalRecovery.field bits cert q component
  let raw ← tabulate l.expanded.points.size fun i =>
    tabulate 3 fun d => InclinedFrameIntervalReactions.reaction bits cert i d
  let mut out := ["CV2011_RELEASE_RESULT_1", l.original.source.members[q.member]!.id] ++
    rationalFields q.t ++ [if q.right then "1" else "0", "1", toString l.original.points.size]
  for i in List.finRange 6 do
    guard (FrameIntervalAccuracy.check (InclinedFrameIntervalOutputs.fieldQuantity i) (fields i))
    out := out ++ intervalFields (fields i)
  for p in l.original.points do
    let member := p.owner.isSome
    let point := if member then InclinedFrameSource.locate l.expanded p.index p.t else p.index
    let id := if member then l.original.source.members[p.index]!.id else l.original.source.nodes[p.index]!.id
    out := out ++ [if member then "1" else "0", toString p.index, id] ++ rationalFields p.t
    for d in List.finRange 3 do
      let reaction ← FrameIntervalAssembly.sumTerms bits fun i : Fin l.expanded.points.size =>
        if l.parent[i.val]! == point then some (raw i d) else some ⟨0,0⟩
      guard (FrameIntervalAccuracy.check (InclinedFrameIntervalOutputs.reactionQuantity d) reaction)
      out := out ++ intervalFields reaction
  let sideNode := fun side => endpoint l.original.source.members[side/2]! side
  let faces := (List.range (2*l.original.source.members.size)).filter fun side =>
    l.sides.any fun released => sideNode released == sideNode side
  out := out ++ [toString faces.length]
  for side in faces do
    let member := side/2
    let face := HingeFrame.faceQuery side
    let point := InclinedFrameSource.locate l.expanded member face.t
    let motion ← InclinedFrameIntervalRecovery.nodalMotion bits cert point
    let moment ← InclinedFrameIntervalRecovery.field bits cert face 2
    guard (FrameIntervalAccuracy.check 2 moment && FrameIntervalAccuracy.check 3 (motion 2))
    guard (FrameIntervalAccuracy.check 4 (motion 0) && FrameIntervalAccuracy.check 5 (motion 1))
    out := out ++ [l.original.source.nodes[sideNode side]!.id, l.original.source.members[member]!.id,
      toString (side%2), if l.sides.contains side then "1" else "0"] ++
      intervalFields (motion 0) ++ intervalFields (motion 1) ++ intervalFields (motion 2) ++ intervalFields moment
  return out

def report (value : Packet) : Option String := do
  let l ← layout value.source value.rules
  let n := l.basis.columns.size
  guard (value.roots.size == l.expanded.source.members.size && value.inverse.size == n &&
    value.estimate.size == n && value.inverse.all (fun row => row.size == n))
  let proposal : InclinedFrameIntervalBuild.Proposal l.expanded l.basis := {
    roots := fun i => value.roots[i.val]!, inverse := fun i j => value.inverse[i.val]![j.val]!,
    estimate := fun i => value.estimate[i.val]! }
  let cert ← build l value.bits proposal
  guard (verified l value.bits cert)
  let fields ← resultFields l value.bits cert value.query
  let result := String.intercalate "\n" fields
  guard (result.utf8ByteSize ≤ 262144)
  return result

@[export inclined_release_report]
def checkReport (input : String) : Option String := do report (← decode input)

end InclinedRelease.Wire
