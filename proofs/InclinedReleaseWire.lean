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

def groupReaction (l : Layout) (bits : Nat) (point : Nat) (d : Fin 3)
    (raw : Fin l.expanded.points.size → Fin 3 → Bounds) : Option Bounds :=
  FrameIntervalAssembly.sumTerms bits fun i : Fin l.expanded.points.size =>
    if l.parent[i.val]! == point then some (raw i d) else some ⟨0,0⟩

/-- Retain the checked calculation alongside its result. Proof fields erase
    during compilation and let the report theorem refer to each emitted value. -/
structure Evaluated {α : Type} (op : Option α) where
  value : α
  computed : op = some value

def evaluate {α : Type} (op : Option α) : Option (Evaluated op) :=
  match h : op with
  | none => none
  | some value => some ⟨value, h⟩

structure Accurate (quantity : Fin 9) (op : Option Bounds) extends Evaluated op where
  accuracy : FrameIntervalAccuracy.check quantity value = true

def measure (quantity : Fin 9) (op : Option Bounds) : Option (Accurate quantity op) := do
  let result ← evaluate op
  if h : FrameIntervalAccuracy.check quantity result.value = true then return ⟨result, h⟩ else none

def gather : (n : Nat) → (V : Fin n → Type) → ((i : Fin n) → Option (V i)) → Option ((i : Fin n) → V i)
  | 0, _, _ => some (fun i => Fin.elim0 i)
  | n+1, V, entry => do
    let head ← entry 0
    let tail ← gather n (fun i => V i.succ) (fun i => entry i.succ)
    return Fin.cases head tail

def expandedPoint (l : Layout) (i : Fin l.original.points.size) : Nat :=
  let p := l.original.points[i.val]!
  if p.owner.isSome then InclinedFrameSource.locate l.expanded p.index p.t else p.index

def faceNode (l : Layout) (side : Nat) := endpoint l.original.source.members[side/2]! side

def faceSides (l : Layout) : Array Nat :=
  ((List.range (2*l.original.source.members.size)).filter fun side =>
    l.sides.any fun released => faceNode l released == faceNode l side).toArray

def facePoint (l : Layout) (side : Nat) := InclinedFrameSource.locate l.expanded (side/2) (HingeFrame.faceQuery side).t

abbrev Cert (l : Layout) := InclinedFrameIntervalAssembly.Certificate l.expanded l.basis

structure Face (l : Layout) (bits : Nat) (c : Cert l) (side : Nat) where
  motion : Evaluated (InclinedFrameIntervalRecovery.nodalMotion bits c (facePoint l side))
  ux : FrameIntervalAccuracy.check 4 (motion.value 0) = true
  uy : FrameIntervalAccuracy.check 5 (motion.value 1) = true
  rotation : FrameIntervalAccuracy.check 3 (motion.value 2) = true
  moment : Accurate 2 (InclinedFrameIntervalRecovery.field bits c (HingeFrame.faceQuery side) 2)

def readFace (l : Layout) (bits : Nat) (c : Cert l) (side : Nat) : Option (Face l bits c side) := do
  let motion ← evaluate (InclinedFrameIntervalRecovery.nodalMotion bits c (facePoint l side))
  let moment ← measure 2 (InclinedFrameIntervalRecovery.field bits c (HingeFrame.faceQuery side) 2)
  if h : FrameIntervalAccuracy.check 4 (motion.value 0) = true ∧
      FrameIntervalAccuracy.check 5 (motion.value 1) = true ∧ FrameIntervalAccuracy.check 3 (motion.value 2) = true
    then return ⟨motion, h.1, h.2.1, h.2.2, moment⟩ else none

structure Values (l : Layout) (bits : Nat) (c : Cert l) (q : Query) where
  fields : (d : Fin 6) → Accurate (InclinedFrameIntervalOutputs.fieldQuantity d) (InclinedFrameIntervalRecovery.field bits c q d)
  raw : (p : Fin l.expanded.points.size) → (d : Fin 3) → Evaluated (InclinedFrameIntervalReactions.reaction bits c p d)
  reactions : (p : Fin l.original.points.size) → (d : Fin 3) → Accurate (InclinedFrameIntervalOutputs.reactionQuantity d)
    (groupReaction l bits (expandedPoint l p) d fun i k => (raw i k).value)
  faces : (i : Fin (faceSides l).size) → Face l bits c (faceSides l)[i.val]!

def readValues (l : Layout) (bits : Nat) (c : Cert l) (q : Query) : Option (Values l bits c q) := do
  let fields ← gather 6 _ fun d => measure (InclinedFrameIntervalOutputs.fieldQuantity d) (InclinedFrameIntervalRecovery.field bits c q d)
  let raw ← gather l.expanded.points.size _ fun p => gather 3 _ fun d => evaluate (InclinedFrameIntervalReactions.reaction bits c p d)
  let reactions ← gather l.original.points.size _ fun p => gather 3 _ fun d =>
    measure (InclinedFrameIntervalOutputs.reactionQuantity d) (groupReaction l bits (expandedPoint l p) d fun i k => (raw i k).value)
  let faces ← gather (faceSides l).size _ fun i => readFace l bits c (faceSides l)[i.val]!
  return ⟨fields, raw, reactions, faces⟩

def encode {l : Layout} {bits : Nat} {c : Cert l} {q : Query} (v : Values l bits c q) : String := Id.run do
  let mut out := ["CV2011_RELEASE_RESULT_1", l.original.source.members[q.member]!.id] ++
    rationalFields q.t ++ [if q.right then "1" else "0", "1", toString l.original.points.size]
  for i in List.finRange 6 do out := out ++ intervalFields (v.fields i).value
  for i in List.finRange l.original.points.size do
    let p := l.original.points[i.val]!
    let member := p.owner.isSome
    let id := if member then l.original.source.members[p.index]!.id else l.original.source.nodes[p.index]!.id
    out := out ++ [if member then "1" else "0", toString p.index, id] ++ rationalFields p.t
    for d in List.finRange 3 do out := out ++ intervalFields (v.reactions i d).value
  out := out ++ [toString (faceSides l).size]
  for i in List.finRange (faceSides l).size do
    let side := (faceSides l)[i.val]!
    let f := v.faces i
    out := out ++ [l.original.source.nodes[faceNode l side]!.id, l.original.source.members[side/2]!.id,
      toString (side%2), if l.sides.contains side then "1" else "0"] ++
      intervalFields (f.motion.value 0) ++ intervalFields (f.motion.value 1) ++
      intervalFields (f.motion.value 2) ++ intervalFields f.moment.value
  return String.intercalate "\n" out


def proposalFor (l : Layout) (value : Packet) : Option (InclinedFrameIntervalBuild.Proposal l.expanded l.basis) := do
  let n := l.basis.columns.size
  guard (value.roots.size == l.expanded.source.members.size && value.inverse.size == n &&
    value.estimate.size == n && value.inverse.all (fun row => row.size == n))
  return {
    roots := fun i => value.roots[i.val]!, inverse := fun i j => value.inverse[i.val]![j.val]!,
    estimate := fun i => value.estimate[i.val]! }

def report (value : Packet) : Option String := do
  let l ← layout value.source value.rules
  let proposal ← proposalFor l value
  let cert ← build l value.bits proposal
  if verified l value.bits cert then
    let fields ← readValues l value.bits cert value.query
    let result := encode fields
    if result.utf8ByteSize ≤ 262144 then some result else none
  else none

@[export inclined_release_report]
def checkReport (input : String) : Option String := do report (← decode input)

end InclinedRelease.Wire
