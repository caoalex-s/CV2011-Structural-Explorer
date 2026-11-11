import RationalFrameModel

/-! Executable postconditions for the source-derived subdivision. They expose
    the exact ownership/coverage premises needed by the real-model bridge,
    without trusting the imperative subdivision algorithm or supplied tables. -/
namespace RationalFrame

def memberLength (source : Source) (member : Nat) : Rat :=
  let m := source.members[member]!
  absolute (source.nodes[m.b]!.x - source.nodes[m.a]!.x) +
    absolute (source.nodes[m.b]!.y - source.nodes[m.a]!.y)

def memberCosine (source : Source) (member : Nat) : Rat :=
  let m := source.members[member]!
  (source.nodes[m.b]!.x - source.nodes[m.a]!.x) / memberLength source member

def memberSine (source : Source) (member : Nat) : Rat :=
  let m := source.members[member]!
  (source.nodes[m.b]!.y - source.nodes[m.a]!.y) / memberLength source member

/-- Stored original nodes are a prefix. Interior point identities use both
    the original member and its exact parameter, independently of coordinates. -/
def PointValid (model : Compiled) (i : Fin model.points.size) : Prop :=
  let p := model.points[i.val]!
  match p.owner with
  | none => p.index = i.val ∧ i.val < model.source.nodes.size ∧ p.t = 0 ∧
      p.x = model.source.nodes[i.val]!.x ∧ p.y = model.source.nodes[i.val]!.y
  | some member =>
      let m := model.source.members[member]!
      let a := model.source.nodes[m.a]!
      let b := model.source.nodes[m.b]!
      model.source.nodes.size ≤ i.val ∧ member < model.source.members.size ∧ p.index = member ∧
      0 < p.t ∧ p.t < 1 ∧ p.x = a.x + p.t * (b.x-a.x) ∧ p.y = a.y + p.t * (b.y-a.y)

def LocationValid (model : Compiled) (member : Nat) (t : Rat) (index : Nat) : Prop :=
  member < model.source.members.size ∧ index < model.points.size ∧
    if t = 0 then index = model.source.members[member]!.a
    else if t = 1 then index = model.source.members[member]!.b
    else model.points[index]!.owner = some member ∧ model.points[index]!.t = t

def restrictedVertical (source : Source) (segment : Segment) : Rat :=
  source.loads.foldl (fun total load =>
    if load.member == segment.member && load.kind == 2 && load.t ≤ segment.left && segment.right ≤ load.ending
    then total + load.fy else total) 0

def SegmentValid (model : Compiled) (segment : Segment) : Prop :=
  segment.member < model.source.members.size ∧
  LocationValid model segment.member segment.left segment.a ∧
  LocationValid model segment.member segment.right segment.b ∧
  0 ≤ segment.left ∧ segment.left < segment.right ∧ segment.right ≤ 1 ∧
  segment.length = memberLength model.source segment.member * (segment.right-segment.left) ∧
  0 < segment.length ∧ 0 < segment.EA ∧ 0 < segment.EI ∧
  segment.EA = model.source.members[segment.member]!.EA ∧
  segment.EI = model.source.members[segment.member]!.EI ∧
  segment.cosine = memberCosine model.source segment.member ∧
  segment.sine = memberSine model.source segment.member ∧
  segment.cosine * segment.cosine + segment.sine * segment.sine = 1 ∧
  (segment.cosine = 0 ∨ segment.sine = 0) ∧
  segment.vertical = restrictedVertical model.source segment ∧ segment.a ≠ segment.b

/-- Every member's filtered segment list is a positive chain ending at 1. -/
def chainFrom (start : Rat) : List Segment → Bool
  | [] => start == 1
  | segment :: rest => segment.left == start && decide (segment.left < segment.right) && chainFrom segment.right rest

def memberSegments (model : Compiled) (member : Nat) : List Segment :=
  model.segments.toList.filter (fun segment => segment.member == member)

/-- The postcondition exposes standard support semantics to the real-model
    bridge, in addition to the source validator's executable class gate. -/
def SupportValid (model : Compiled) (support : Support) : Prop :=
  LocationValid model support.member support.t (locationIndex model support.member support.t) ∧
  support.kind ≤ 2 ∧
  (support.kind = 2 → support.angle = 0 ∨ support.angle = 90 ∨ support.angle = 180 ∨ support.angle = 270)

def PartitionValid (model : Compiled) : Prop :=
  0 < model.source.nodes.size ∧ 0 < model.source.members.size ∧
  model.source.nodes.size ≤ model.points.size ∧ model.points.size ≤ 16 ∧ model.segments.size ≤ 16 ∧
  (∀ i : Fin model.source.members.size,
    model.source.members[i.val]!.a < model.source.nodes.size ∧
    model.source.members[i.val]!.b < model.source.nodes.size ∧
    0 < memberLength model.source i.val) ∧
  (∀ i : Fin model.points.size, PointValid model i) ∧
  (∀ i j : Fin model.points.size,
    model.points[i.val]!.owner = model.points[j.val]!.owner →
    model.points[i.val]!.index = model.points[j.val]!.index →
    model.points[i.val]!.t = model.points[j.val]!.t → i = j) ∧
  (∀ i : Fin model.points.size,
    ¬ ∀ segment : Fin model.segments.size,
      model.segments[segment.val]!.a ≠ i.val ∧ model.segments[segment.val]!.b ≠ i.val) ∧
  (∀ i : Fin model.segments.size, SegmentValid model model.segments[i.val]!) ∧
  (∀ i : Fin model.source.members.size, chainFrom 0 (memberSegments model i.val) = true) ∧
  (∀ i : Fin model.source.supports.size,
    SupportValid model model.source.supports[i.val]!) ∧
  (∀ i : Fin model.source.loads.size,
    let load := model.source.loads[i.val]!
    LocationValid model load.member load.t (locationIndex model load.member load.t) ∧
    (load.kind = 2 → LocationValid model load.member load.ending (locationIndex model load.member load.ending)))

instance (model : Compiled) (i : Fin model.points.size) : Decidable (PointValid model i) := by
  unfold PointValid
  dsimp only
  cases model.points[i.val]!.owner <;> infer_instance
instance (model : Compiled) (member : Nat) (t : Rat) (index : Nat) : Decidable (LocationValid model member t index) := by
  unfold LocationValid
  infer_instance
instance (model : Compiled) (segment : Segment) : Decidable (SegmentValid model segment) := by
  unfold SegmentValid
  infer_instance
instance (model : Compiled) (support : Support) : Decidable (SupportValid model support) := by
  unfold SupportValid
  infer_instance
instance (model : Compiled) : Decidable (PartitionValid model) := by
  unfold PartitionValid
  infer_instance

end RationalFrame
