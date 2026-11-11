import Batteries.Data.Rat.Basic

/-! Executable source-derived model for the bounded rigid axis-aligned class.
    No stiffness, force, constraint, cut, or geometry table is a caller input.
    The real-model interpretation is proved separately in RationalFrameSoundness.
    Original nodes and member-owned interior cuts have distinct point identities. -/
namespace RationalFrame

structure Node where
  id : String
  x : Rat
  y : Rat
  joint : Nat
  reference : Option Nat
  rotationStiffness : Rat
  deriving Inhabited, Repr

structure Member where
  id : String
  a : Nat
  b : Nat
  EA : Rat
  EI : Rat
  rigidEnds : Bool
  deriving Inhabited, Repr

structure Support where
  id : String
  member : Nat
  t : Rat
  /-- 0 pin, 1 fixed, 2 roller. -/
  kind : Nat
  angle : Rat
  deriving Inhabited, Repr

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
  deriving Inhabited, Repr

structure Source where
  nodes : Array Node
  members : Array Member
  supports : Array Support
  loads : Array Load
  deriving Inhabited, Repr

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
  deriving Inhabited, Repr

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
  ids.toList.eraseDups.length == ids.size && ids.all (fun id => !id.isEmpty && id.length ≤ 256)

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
        points := points.push { owner := some m, index := m, t,
          x := a.x + t * dx, y := a.y + t * dy }
    for i in [:cuts.size - 1] do
      if segments.size ≥ 16 then return none
      let left := cuts[i]!
      let right := cuts[i + 1]!
      let vertical := source.loads.foldl (fun total load =>
        if load.member == m && load.kind == 2 && load.t ≤ left && right ≤ load.ending
        then total + load.fy else total) 0
      segments := segments.push { member := m, a := indices[i]!, b := indices[i + 1]!,
        left, right, length := length * (right - left), cosine, sine,
        EA := member.EA, EI := member.EI, vertical }
  return some { source, points, segments }

def dofs (model : Compiled) : Nat := 3 * model.points.size
def sumFin (n : Nat) (f : Fin n → Rat) : Rat := ((List.finRange n).map f).foldr (· + ·) 0
def sumSegments (model : Compiled) (f : Segment → Rat) : Rat :=
  (model.segments.toList.map f).foldr (· + ·) 0

/-- Exact local stiffness, with no cached input matrix. -/
def localStiffness (s : Segment) (i j : Fin 6) : Rat :=
  let L := s.length
  let a := s.EA / L
  let b := 12 * s.EI / L^3
  let c := 6 * s.EI / L^2
  let d := 4 * s.EI / L
  let e := 2 * s.EI / L
  let rows : Array (Array Rat) :=
    #[#[a,0,0,-a,0,0], #[0,b,c,0,-b,c], #[0,c,d,0,-c,e],
      #[-a,0,0,a,0,0], #[0,-b,-c,0,b,-c], #[0,c,e,0,-c,d]]
  rows[i.val]![j.val]!

def localForce (s : Segment) (i : Fin 6) : Rat :=
  let axial := s.sine * s.vertical * s.length / 2
  let transverse := s.cosine * s.vertical * s.length / 2
  let moment := s.cosine * s.vertical * s.length^2 / 12
  (#[axial, transverse, moment, axial, transverse, -moment] : Array Rat)[i.val]!

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

/-- The scattered matrix is constructed once per request before witness checks. -/
def stiffnessMatrix (model : Compiled) : Array (Array Rat) := Id.run do
  let mut matrix := Array.replicate model.dofs (Array.replicate model.dofs (0 : Rat))
  for segment in model.segments do
    for i in List.finRange 6 do
      let row := globalIndex segment i
      for j in List.finRange 6 do
        let column := globalIndex segment j
        let value := coordinateSign segment i * localStiffness segment i j * coordinateSign segment j
        matrix := matrix.set! row ((matrix[row]!).set! column (matrix[row]![column]! + value))
  return matrix

def forceVector (model : Compiled) : Array Rat := Id.run do
  let mut force := Array.replicate model.dofs (0 : Rat)
  for segment in model.segments do
    for i in List.finRange 6 do
      let row := globalIndex segment i
      force := force.set! row (force[row]! + coordinateSign segment i * localForce segment i)
  for load in model.source.loads do
    if load.kind < 2 then
      let point := locationIndex model load.member load.t
      let action : Array Rat := if load.kind == 0 then #[load.fx, load.fy, 0] else #[0, 0, load.mz]
      for d in [:3] do
        let row := 3 * point + d
        force := force.set! row (force[row]! + action[d]!)
  return force

def blocked (model : Compiled) (i : Nat) : Bool :=
  model.source.supports.any fun support =>
    let point := locationIndex model support.member support.t
    let d := i % 3
    i / 3 == point && (support.kind == 1 || (support.kind == 0 && d < 2) ||
      (support.kind == 2 && d == if support.angle == 0 || support.angle == 180 then 0 else 1))

def freeIndices (model : Compiled) : Array Nat :=
  ((List.range model.dofs).filter (fun i => !blocked model i)).toArray

def selectedSegment (model : Compiled) (query : Query) : Option Segment :=
  let matching := model.segments.toList.filter fun segment =>
    segment.member == query.member && segment.left ≤ query.t && query.t ≤ segment.right
  if query.right then matching.getLast? else matching.head?

def queryValid (model : Compiled) (query : Query) : Bool :=
  query.member < model.source.members.size && inUnit query.t && query.convention == 1 &&
    (selectedSegment model query).isSome

/-- Loaded field values, ordered N,V,M,rotation,ux,uy with original member axes. -/
def recover (model : Compiled) (query : Query) (motion : Array Rat) : Array Rat := Id.run do
  let some s := selectedSegment model query | return #[]
  let d := fun i : Fin 6 => coordinateSign s i * motion[globalIndex s i]!
  let action := fun i : Fin 6 => sumFin 6 (fun j => localStiffness s i j * d j) - localForce s i
  let x := s.length * (query.t - s.left) / (s.right - s.left)
  let p := s.sine * s.vertical
  let q := s.cosine * s.vertical
  let normal := -action 0 - p*x
  let shear := action 1 + q*x
  let moment := -action 2 + action 1*x + q*x^2/2
  let axial := d 0 + (-action 0*x - p*x^2/2)/s.EA
  let transverse := d 1 + d 2*x + (-action 2*x^2/2 + action 1*x^3/6 + q*x^4/24)/s.EI
  let rotation := d 2 + (-action 2*x + action 1*x^2/2 + q*x^3/6)/s.EI
  return #[normal, shear, moment, rotation,
    s.cosine*axial - s.sine*transverse, s.sine*axial + s.cosine*transverse]

end RationalFrame
