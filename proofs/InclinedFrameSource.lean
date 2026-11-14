import RationalFrameModel

/-! Original-source subdivision for rigid inclined frames. This shares the
    established exact source types and cut/load functions, but never calls the
    cardinal compiler or substitutes its Manhattan length for a physical length.
    All identifiers here retain the existing wire's UTF-16 hexadecimal encoding. -/
namespace InclinedFrameSource
open RationalFrame

structure Piece where
  member : Nat
  a : Nat
  b : Nat
  left : Rat
  right : Rat
  vertical : Rat
  verticalEnd : Rat
  deriving Inhabited, Repr, DecidableEq

structure Partition where
  source : Source
  points : Array Point
  pieces : Array Piece
  deriving Inhabited, Repr

/-- The geometry gate rejects coincident endpoints, not inclined members.
    All degree angles are retained exactly; arbitrary force components are
    already independent rational fields of each original point load. -/
def SourceValid (source : Source) : Prop :=
  0 < source.nodes.size ∧ source.nodes.size ≤ 16 ∧
  0 < source.members.size ∧ source.members.size ≤ 8 ∧
  source.supports.size ≤ 16 ∧ source.loads.size ≤ 16 ∧
  uniqueIds (source.nodes.map (·.id)) = true ∧ uniqueIds (source.members.map (·.id)) = true ∧
  uniqueIds (source.supports.map (·.id)) = true ∧ uniqueIds (source.loads.map (·.id)) = true ∧
  (∀ i : Fin source.nodes.size,
    source.nodes[i.val]!.joint = 0 ∧
    source.members.any (fun m => m.a == i.val || m.b == i.val) = true ∧
    source.nodes[i.val]!.reference.all (fun reference => decide (
      reference < source.members.size ∧
      (source.members[reference]!.a = i.val ∨ source.members[reference]!.b = i.val))) = true) ∧
  (∀ i : Fin source.members.size,
    let m := source.members[i.val]!
    m.a < source.nodes.size ∧ m.b < source.nodes.size ∧ m.a ≠ m.b ∧
    0 < m.EA ∧ 0 < m.EI ∧ m.rigidEnds = true ∧
    (source.nodes[m.a]!.x ≠ source.nodes[m.b]!.x ∨ source.nodes[m.a]!.y ≠ source.nodes[m.b]!.y)) ∧
  (∀ i : Fin source.supports.size,
    let s := source.supports[i.val]!
    s.member < source.members.size ∧ 0 ≤ s.t ∧ s.t ≤ 1 ∧ s.kind ≤ 2) ∧
  (∀ i : Fin source.loads.size,
    let load := source.loads[i.val]!
    load.member < source.members.size ∧ 0 ≤ load.t ∧ load.t ≤ 1 ∧
    0 ≤ load.ending ∧ load.ending ≤ 1 ∧ load.kind ≤ 2 ∧ (load.kind = 2 → load.t < load.ending))

instance (source : Source) : Decidable (SourceValid source) := by
  unfold SourceValid
  infer_instance

def locate (data : Partition) (member : Nat) (t : Rat) : Nat :=
  if t = 0 then data.source.members[member]!.a
  else if t = 1 then data.source.members[member]!.b
  else ((List.range data.points.size).find? (fun i =>
    data.points[i]!.owner == some member && data.points[i]!.t == t)).getD data.points.size

def restricted (source : Source) (member : Nat) (left right t : Rat) : Rat :=
  source.loads.foldl (fun total load =>
    if load.member == member && load.kind == 2 && load.t ≤ left && right ≤ load.ending
    then total + loadIntensity load t else total) 0

/-- Every interior point is allocated under its original member owner. Equal
    spatial coordinates on two members do not create a new rigid connection. -/
def compilePartition (source : Source) : Option Partition := Id.run do
  if !decide (SourceValid source) then return none
  let mut points := source.nodes.mapIdx fun i node =>
    ({ owner := none, index := i, t := 0, x := node.x, y := node.y } : Point)
  let mut pieces : Array Piece := #[]
  for memberIndex in [:source.members.size] do
    let member := source.members[memberIndex]!
    let a := source.nodes[member.a]!
    let b := source.nodes[member.b]!
    let cuts := (memberCuts source memberIndex).toArray
    let mut indices : Array Nat := #[]
    for t in cuts do
      if t = 0 then indices := indices.push member.a
      else if t = 1 then indices := indices.push member.b
      else
        if points.size ≥ 16 then return none
        indices := indices.push points.size
        points := points.push { owner := some memberIndex, index := memberIndex, t := t,
          x := a.x + t*(b.x-a.x), y := a.y + t*(b.y-a.y) }
    for i in [:cuts.size-1] do
      if pieces.size ≥ 16 then return none
      let left := cuts[i]!
      let right := cuts[i+1]!
      pieces := pieces.push { member := memberIndex, a := indices[i]!, b := indices[i+1]!,
        left := left, right := right,
        vertical := restricted source memberIndex left right left,
        verticalEnd := restricted source memberIndex left right right }
  return some { source := source, points := points, pieces := pieces }

def PointValid (data : Partition) (i : Fin data.points.size) : Prop :=
  let point := data.points[i.val]!
  match point.owner with
  | none => point.index = i.val ∧ i.val < data.source.nodes.size ∧ point.t = 0 ∧
      point.x = data.source.nodes[i.val]!.x ∧ point.y = data.source.nodes[i.val]!.y
  | some owner =>
      let member := data.source.members[owner]!
      let a := data.source.nodes[member.a]!
      let b := data.source.nodes[member.b]!
      data.source.nodes.size ≤ i.val ∧ owner < data.source.members.size ∧ point.index = owner ∧
      0 < point.t ∧ point.t < 1 ∧
      point.x = a.x + point.t*(b.x-a.x) ∧ point.y = a.y + point.t*(b.y-a.y)

def LocationValid (data : Partition) (member : Nat) (t : Rat) (index : Nat) : Prop :=
  member < data.source.members.size ∧ index < data.points.size ∧
  if t = 0 then index = data.source.members[member]!.a
  else if t = 1 then index = data.source.members[member]!.b
  else data.points[index]!.owner = some member ∧ data.points[index]!.t = t

def PieceValid (data : Partition) (piece : Piece) : Prop :=
  LocationValid data piece.member piece.left piece.a ∧
  LocationValid data piece.member piece.right piece.b ∧
  0 ≤ piece.left ∧ piece.left < piece.right ∧ piece.right ≤ 1 ∧ piece.a ≠ piece.b ∧
  piece.vertical = restricted data.source piece.member piece.left piece.right piece.left ∧
  piece.verticalEnd = restricted data.source piece.member piece.left piece.right piece.right ∧
  (∀ i : Fin data.source.loads.size,
    let load := data.source.loads[i.val]!
    load.member = piece.member → load.kind = 2 →
      (load.t ≤ piece.left ∨ piece.right ≤ load.t) ∧
      (load.ending ≤ piece.left ∨ piece.right ≤ load.ending))

def chainFrom (start : Rat) : List Piece → Bool
  | [] => start == 1
  | piece :: rest => piece.left == start && decide (piece.left < piece.right) && chainFrom piece.right rest

def represented (data : Partition) (member : Nat) (t : Rat) (point : Nat) : Bool :=
  data.pieces.any fun piece => piece.member == member &&
    ((piece.left == t && piece.a == point) || (piece.right == t && piece.b == point))

/-- Executable postconditions expose ownership and coverage to the real bridge.
    They are checked on the compiler's result, never on an alternative graph
    chosen by a certificate producer. Every original support and load is included. -/
def PartitionValid (data : Partition) : Prop :=
  SourceValid data.source ∧ data.source.nodes.size ≤ data.points.size ∧
  data.points.size ≤ 16 ∧ data.pieces.size ≤ 16 ∧
  (∀ i : Fin data.points.size, PointValid data i) ∧
  (∀ i j : Fin data.points.size,
    data.points[i.val]!.owner = data.points[j.val]!.owner →
    data.points[i.val]!.index = data.points[j.val]!.index →
    data.points[i.val]!.t = data.points[j.val]!.t → i = j) ∧
  (∀ i : Fin data.points.size,
    data.pieces.any (fun piece => piece.a == i.val || piece.b == i.val) = true) ∧
  (∀ i : Fin data.pieces.size, PieceValid data data.pieces[i.val]!) ∧
  (∀ i : Fin data.source.members.size,
    chainFrom 0 (data.pieces.toList.filter (fun piece => piece.member == i.val)) = true) ∧
  (∀ i j : Fin data.pieces.size, i ≠ j → data.pieces[i.val]!.member = data.pieces[j.val]!.member →
    data.pieces[i.val]!.right ≤ data.pieces[j.val]!.left ∨ data.pieces[j.val]!.right ≤ data.pieces[i.val]!.left) ∧
  (∀ i : Fin data.source.supports.size,
    let support := data.source.supports[i.val]!
    LocationValid data support.member support.t (locate data support.member support.t) ∧
    represented data support.member support.t (locate data support.member support.t) = true) ∧
  (∀ i : Fin data.source.loads.size,
    let load := data.source.loads[i.val]!
    LocationValid data load.member load.t (locate data load.member load.t) ∧
    represented data load.member load.t (locate data load.member load.t) = true ∧
    (load.kind = 2 → LocationValid data load.member load.ending (locate data load.member load.ending) ∧
      represented data load.member load.ending (locate data load.member load.ending) = true))

instance (data : Partition) (i : Fin data.points.size) : Decidable (PointValid data i) := by
  unfold PointValid
  dsimp only
  cases data.points[i.val]!.owner <;> infer_instance
instance (data : Partition) (member : Nat) (t : Rat) (index : Nat) : Decidable (LocationValid data member t index) := by
  unfold LocationValid
  infer_instance
instance (data : Partition) (piece : Piece) : Decidable (PieceValid data piece) := by
  unfold PieceValid
  infer_instance
instance (data : Partition) : Decidable (PartitionValid data) := by
  unfold PartitionValid
  infer_instance

def checkedPartition (source : Source) : Option Partition := do
  let data ← compilePartition source
  if data.source = source ∧ PartitionValid data then some data else none

theorem checkedPartition_source {source : Source} {data : Partition}
    (h : checkedPartition source = some data) : data.source = source ∧ PartitionValid data := by
  unfold checkedPartition at h
  obtain ⟨compiled, hcompiled, hcheck⟩ := Option.bind_eq_some.mp h
  split at hcheck
  next accepted =>
    have heq : compiled = data := Option.some.inj hcheck
    simpa [heq] using accepted
  · simp at hcheck

end InclinedFrameSource
