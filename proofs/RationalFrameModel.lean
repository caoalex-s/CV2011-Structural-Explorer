import Batteries.Data.Rat.Basic

/-! Executable source-derived model for the bounded rigid axis-aligned class.
    No stiffness, force, constraint, cut, or geometry table is a caller input.
    The real-model interpretation belongs in a separate soundness module.
    Original nodes and member-owned interior cuts have distinct point identities. -/
namespace RationalFrame

structure Node where
  id : String
  x : Rat
  y : Rat
  joint : Nat
  reference : Option Nat
  rotationStiffness : Rat
  deriving Inhabited, Repr, DecidableEq

structure Member where
  id : String
  a : Nat
  b : Nat
  EA : Rat
  EI : Rat
  rigidEnds : Bool
  deriving Inhabited, Repr, DecidableEq

structure Support where
  id : String
  member : Nat
  t : Rat
  /-- 0 pin, 1 fixed, 2 roller. -/
  kind : Nat
  angle : Rat
  deriving Inhabited, Repr, DecidableEq

structure Load where
  id : String
  member : Nat
  /-- 0 global point force, 1 point couple, 2 vertical uniform intensity. -/
  kind : Nat
  t : Rat
  ending : Rat
  fx : Rat
  fy : Rat
  mz : Rat
  qEnd : Rat
  deriving Inhabited, Repr, DecidableEq

structure Source where
  nodes : Array Node
  members : Array Member
  supports : Array Support
  loads : Array Load
  deriving Inhabited, Repr, DecidableEq

structure Query where
  member : Nat
  t : Rat
  /-- false selects the left limit; true selects the right limit. -/
  right : Bool
  /-- Version 1 fixes N,V,M,rotation,ux,uy, units and documented signs. -/
  convention : Nat
  deriving Inhabited, Repr

structure Point where
  /-- none is an original node; some m is an interior point owned by m. -/
  owner : Option Nat
  index : Nat
  t : Rat
  x : Rat
  y : Rat
  deriving Inhabited, Repr, DecidableEq

structure Segment where
  member : Nat
  a : Nat
  b : Nat
  left : Rat
  right : Rat
  length : Rat
  cosine : Rat
  sine : Rat
  EA : Rat
  EI : Rat
  vertical : Rat
  deriving Inhabited, Repr

structure Compiled where
  source : Source
  points : Array Point
  segments : Array Segment
  deriving Inhabited, Repr

def absolute (a : Rat) : Rat := if a < 0 then -a else a
def inUnit (a : Rat) : Bool := decide (0 ≤ a ∧ a ≤ 1)
def uniqueIds (ids : Array String) : Bool :=
  ids.toList.eraseDups.length == ids.size && ids.all (fun id => !id.isEmpty && id.length ≤ 1024)

/-- Source checks use exact equality, never an axis or endpoint tolerance. -/
def sourceValid (source : Source) : Bool := Id.run do
  if source.nodes.size == 0 || source.nodes.size > 16 || source.members.size == 0 ||
      source.members.size > 8 || source.supports.size > 16 || source.loads.size > 16 then return false
  if !(uniqueIds (source.nodes.map (·.id)) && uniqueIds (source.members.map (·.id)) &&
      uniqueIds (source.supports.map (·.id)) && uniqueIds (source.loads.map (·.id))) then return false
  for i in [:source.nodes.size] do
    let node := source.nodes[i]!
    if node.joint != 0 || !(source.members.any (fun m => m.a == i || m.b == i)) then return false
    if let some reference := node.reference then
      if reference ≥ source.members.size then return false
      let member := source.members[reference]!
      if member.a != i && member.b != i then return false
  for member in source.members do
    if member.a ≥ source.nodes.size || member.b ≥ source.nodes.size || member.a == member.b ||
        member.EA ≤ 0 || member.EI ≤ 0 || !member.rigidEnds then return false
    let a := source.nodes[member.a]!
    let b := source.nodes[member.b]!
    if (a.x == b.x && a.y == b.y) || (a.x != b.x && a.y != b.y) then return false
  for support in source.supports do
    if support.member ≥ source.members.size || !inUnit support.t || support.kind > 2 then return false
    if support.kind == 2 && !(support.angle == 0 || support.angle == 90 || support.angle == 180 || support.angle == 270) then return false
  for load in source.loads do
    if load.member ≥ source.members.size || !inUnit load.t || !inUnit load.ending || load.kind > 2 then return false
    if load.kind == 2 && (load.t ≥ load.ending || load.fy != load.qEnd) then return false
  return true

/-- Complete sorted unique source boundaries for one original member. -/
def memberCuts (source : Source) (member : Nat) : List Rat :=
  let supports := (source.supports.toList.filter (fun s => s.member == member)).map (·.t)
  let loads := (source.loads.toList.filter (fun l => l.member == member)).flatMap
    (fun l => if l.kind == 2 then [l.t, l.ending] else [l.t])
  (([0, 1] ++ supports ++ loads).mergeSort (fun a b => decide (a ≤ b))).eraseDups

/-- Point identity depends on incidence and ownership, not equal coordinates. -/
def locationIndex (model : Compiled) (member : Nat) (t : Rat) : Nat :=
  if t = 0 then model.source.members[member]!.a
  else if t = 1 then model.source.members[member]!.b
  else ((List.range model.points.size).find? (fun i =>
    model.points[i]!.owner == some member && model.points[i]!.t == t)).getD model.points.size

/-- The checker derives its own subdivision and load restriction from source. -/
def compileModel (source : Source) : Option Compiled := Id.run do
  if !sourceValid source then return none
  let mut points := source.nodes.mapIdx fun i node =>
    ({ owner := none, index := i, t := 0, x := node.x, y := node.y } : Point)
  let mut segments : Array Segment := #[]
  for m in [:source.members.size] do
    let member := source.members[m]!
    let a := source.nodes[member.a]!
    let b := source.nodes[member.b]!
    let dx := b.x - a.x
    let dy := b.y - a.y
    let length := absolute dx + absolute dy
    let cosine := dx / length
    let sine := dy / length
    let cuts := (memberCuts source m).toArray
    let mut indices : Array Nat := #[]
    for t in cuts do
      if t = 0 then indices := indices.push member.a
      else if t = 1 then indices := indices.push member.b
      else
        if points.size ≥ 16 then return none
        indices := indices.push points.size
        points := points.push {
          owner := some m, index := m, t := t,
          x := a.x + t * dx, y := a.y + t * dy }
    for i in [:cuts.size - 1] do
      if segments.size ≥ 16 then return none
      let left := cuts[i]!
      let right := cuts[i + 1]!
      let vertical := source.loads.foldl (fun total load =>
        if load.member == m && load.kind == 2 && load.t ≤ left && right ≤ load.ending
        then total + load.fy else total) 0
      segments := segments.push {
        member := m, a := indices[i]!, b := indices[i + 1]!,
        left := left, right := right, length := length * (right - left), cosine := cosine, sine := sine,
        EA := member.EA, EI := member.EI, vertical := vertical }
  return some { source := source, points := points, segments := segments }

def Compiled.dofs (model : Compiled) : Nat := 3 * model.points.size
def sumFin (n : Nat) (f : Fin n → Rat) : Rat := ((List.finRange n).map f).foldr (· + ·) 0
def sumSegments (model : Compiled) (f : Segment → Rat) : Rat :=
  sumFin model.segments.size (fun i => f model.segments[i.val]!)

/-- Exact local stiffness, with no cached input matrix. -/
def localStiffness (s : Segment) (i j : Fin 6) : Rat :=
  let L := s.length
  let a := s.EA / L
  let b := 12 * s.EI / (L * L * L)
  let c := 6 * s.EI / (L * L)
  let d := 4 * s.EI / L
  let e := 2 * s.EI / L
  -- Axial block, transverse block, bending/rotation couplings, rotations.
  -- Pattern matching avoids constructing a 6×6 array for each scalar entry.
  match i.val, j.val with
  | 0, 0 | 3, 3 => a
  | 0, 3 | 3, 0 => -a
  | 1, 1 | 4, 4 => b
  | 1, 4 | 4, 1 => -b
  | 1, 2 | 2, 1 | 1, 5 | 5, 1 => c
  | 2, 4 | 4, 2 | 4, 5 | 5, 4 => -c
  | 2, 2 | 5, 5 => d
  | 2, 5 | 5, 2 => e
  | _, _ => 0

def localForce (s : Segment) (i : Fin 6) : Rat :=
  let axial := s.sine * s.vertical * s.length / 2
  let transverse := s.cosine * s.vertical * s.length / 2
  let moment := s.cosine * s.vertical * (s.length * s.length) / 12
  match i.val with
  | 0 | 3 => axial
  | 1 | 4 => transverse
  | 2 => moment
  | 5 => -moment
  | _ => 0

/-- For the supported axes each local coordinate is one signed global coordinate. -/
def globalIndex (s : Segment) (i : Fin 6) : Nat :=
  let point := if i.val < 3 then s.a else s.b
  let direction := i.val % 3
  3 * point + if direction = 2 then 2 else if s.cosine ≠ 0 then direction else 1 - direction

def coordinateSign (s : Segment) (i : Fin 6) : Rat :=
  if i.val % 3 = 2 then 1
  else if s.cosine ≠ 0 then s.cosine
  else if i.val % 3 = 0 then s.sine else -s.sine

def mapping (s : Segment) (i : Fin 6) (j : Nat) : Rat :=
  if globalIndex s i = j then coordinateSign s i else 0

/-- Invert the signed axis permutation for one global coordinate. Validated
    segments have distinct ends, so at most one local coordinate contributes. -/
def localAt (segment : Segment) (coordinate : Nat) : Option (Fin 6) :=
  let globalDirection := coordinate % 3
  let localDirection := if globalDirection = 2 then 2
    else if segment.cosine ≠ 0 then globalDirection else 1 - globalDirection
  have directionBound : localDirection < 3 := by
    dsimp only [localDirection]
    split
    · decide
    · split
      · exact Nat.mod_lt coordinate (by decide)
      · omega
  if coordinate / 3 = segment.a then some ⟨localDirection, by omega⟩
  else if coordinate / 3 = segment.b then some ⟨localDirection + 3, by omega⟩
  else none

def segmentStiffnessEntry (segment : Segment) (row column : Nat) : Rat :=
  match localAt segment row, localAt segment column with
  | some i, some j => coordinateSign segment i * localStiffness segment i j * coordinateSign segment j
  | _, _ => 0

def stiffnessEntry (model : Compiled) (row column : Nat) : Rat :=
  sumSegments model (fun segment => segmentStiffnessEntry segment row column)

/-- Functional assembly exposes each exact entry to the proof. Coefficients
    are only evaluated for incident segment ends; no caller matrix is used. -/
def stiffnessMatrix (model : Compiled) : Array (Array Rat) :=
  ((List.range model.dofs).map fun row =>
    ((List.range model.dofs).map fun column => stiffnessEntry model row column).toArray).toArray

def segmentForceEntry (segment : Segment) (row : Nat) : Rat :=
  match localAt segment row with
  | some i => coordinateSign segment i * localForce segment i
  | none => 0

def pointForceEntry (model : Compiled) (load : Load) (row : Nat) : Rat :=
  if row / 3 = locationIndex model load.member load.t then
    if load.kind = 0 then if row % 3 = 0 then load.fx else if row % 3 = 1 then load.fy else 0
    else if load.kind = 1 && row % 3 = 2 then load.mz else 0
  else 0

def forceEntry (model : Compiled) (row : Nat) : Rat :=
  sumSegments model (fun segment => segmentForceEntry segment row) +
    sumFin model.source.loads.size (fun i => pointForceEntry model model.source.loads[i.val]! row)

def forceVector (model : Compiled) : Array Rat :=
  ((List.range model.dofs).map fun row => forceEntry model row).toArray

def blocksDirection (support : Support) (direction : Nat) : Bool :=
  support.kind == 1 || (support.kind == 0 && direction < 2) ||
    (support.kind == 2 && direction == if support.angle == 0 || support.angle == 180 then 0 else 1)

def blocked (model : Compiled) (i : Nat) : Bool :=
  model.source.supports.any fun support =>
    let point := locationIndex model support.member support.t
    i / 3 == point && blocksDirection support (i % 3)

def freeIndices (model : Compiled) : Array Nat :=
  ((List.range model.dofs).filter (fun i => !blocked model i)).toArray

def SideContains (segment : Segment) (query : Query) : Prop :=
  segment.member = query.member ∧
    if query.right then segment.left ≤ query.t ∧ query.t < segment.right
    else segment.left < query.t ∧ query.t ≤ segment.right

instance (segment : Segment) (query : Query) : Decidable (SideContains segment query) := by
  unfold SideContains
  infer_instance

/-- Strictness on the outward endpoint selects the requested one-sided
    field directly, independently of the storage order of other members. -/
def selectedIndex (model : Compiled) (query : Query) : Option (Fin model.segments.size) :=
  (List.finRange model.segments.size).find? fun i => decide (SideContains model.segments[i.val]! query)

def selectedSegment (model : Compiled) (query : Query) : Option Segment :=
  (selectedIndex model query).map (fun i => model.segments[i.val]!)

def queryValid (model : Compiled) (query : Query) : Bool :=
  query.member < model.source.members.size && inUnit query.t && query.convention == 1 &&
    (query.t != 0 || query.right) && (query.t != 1 || !query.right) &&
    (match selectedIndex model query with
      | none => false
      | some i => decide (SideContains model.segments[i.val]! query))

def localMotion (s : Segment) (motion : Array Rat) (i : Fin 6) : Rat :=
  coordinateSign s i * motion[globalIndex s i]!

def endAction (s : Segment) (motion : Array Rat) (i : Fin 6) : Rat :=
  sumFin 6 (fun j => localStiffness s i j * localMotion s motion j) - localForce s i

/-- Loaded field values, ordered N,V,M,rotation,ux,uy with original member axes. -/
def recoverSegment (s : Segment) (parameter : Rat) (motion : Array Rat) : Array Rat :=
  let d := localMotion s motion
  let action := endAction s motion
  let x := s.length * (parameter - s.left) / (s.right - s.left)
  let p := s.sine * s.vertical
  let q := s.cosine * s.vertical
  let x2 := x*x
  let x3 := x2*x
  let x4 := x2*x2
  let normal := -action 0 - p*x
  let shear := action 1 + q*x
  let moment := -action 2 + action 1*x + q*x2/2
  let axial := d 0 + (-action 0*x - p*x2/2)/s.EA
  let transverse := d 1 + d 2*x + (-action 2*x2/2 + action 1*x3/6 + q*x4/24)/s.EI
  let rotation := d 2 + (-action 2*x + action 1*x2/2 + q*x3/6)/s.EI
  #[normal, shear, moment, rotation,
    s.cosine*axial - s.sine*transverse, s.sine*axial + s.cosine*transverse]

def recover (model : Compiled) (query : Query) (motion : Array Rat) : Array Rat :=
  match selectedSegment model query with
  | none => #[]
  | some segment => recoverSegment segment query.t motion

end RationalFrame
