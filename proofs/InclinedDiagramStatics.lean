import FrameSpring

/-! Exact statics constrains uncertain end-action enclosures. Each coordinate
is a global end force, an end couple, a spring torque, a member length, or
the constant one. Only end forces and torques are eliminated. -/
namespace InclinedDiagram.Statics
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly FrameIntervalOps

abbrev Row := Array Rat

structure System where
  unknowns : Nat
  width : Nat
  pivots : Array (Nat × Row)

def subtractMultiple (target pivot : Row) (factor : Rat) : Row :=
  if factor = 0 then target else Array.ofFn fun i : Fin target.size => target[i.val]! - factor*pivot[i.val]!

def applyPivots : List (Nat × Row) → Row → Row
  | [], row => row
  | (index,pivot) :: tail, row => applyPivots tail (subtractMultiple row pivot row[index]!)

def reduce (system : System) (row : Row) : Row := applyPivots system.pivots.toList row

/-- Echelon rows may be kept in insertion order. Each later pivot row
has zero coefficient at every preceding pivot. -/
def insert (system : System) (equation : Row) : System := Id.run do
  let remainder := reduce system equation
  let some pivot := (List.range system.unknowns).find? (fun i => remainder[i]! != 0) | return system
  let normalized := remainder.map (· / remainder[pivot]!)
  return {system with pivots := system.pivots.push (pivot,normalized)}

def coefficient (slot : Nat) : List (Nat × Rat) → Rat
  | [] => 0
  | (i,a) :: rest => (if slot = i then a else 0) + coefficient slot rest

def equation (width : Nat) (terms : List (Nat × Rat)) : Row :=
  Array.ofFn fun i : Fin width => coefficient i.val terms

def loadComponent (load : RationalFrame.Load) (d : Nat) : Rat :=
  if load.kind = 0 then if d = 0 then load.fx else if d = 1 then load.fy else 0
  else if load.kind = 1 && d = 2 then load.mz else 0

def endPoint (segment : Piece) (component : Fin 6) :=
  if component.val < 3 then segment.a else segment.b

def globalSlot (component : Fin 6) : Fin 3 := ⟨component.val%3,Nat.mod_lt _ (by decide)⟩

def width (data : Partition) (torques : Nat) :=
  6*data.pieces.size+torques+data.source.members.size+1

def elementTerms (data : Partition) (torques : Nat) (i : Fin data.pieces.size) :
    List (List (Nat × Rat)) :=
  let segment := data.pieces[i.val]!
  let member := data.source.members[segment.member]!
  let a := data.source.nodes[member.a]!
  let b := data.source.nodes[member.b]!
  let fraction := segment.right-segment.left
  let dx := fraction*(b.x-a.x)
  let dy := fraction*(b.y-a.y)
  let len := 6*data.pieces.size+torques+segment.member
  let k := 6*i.val
  [[(k,1),(k+3,1)],[(k+1,1),(k+4,1),(len,fraction*(segment.vertical+segment.verticalEnd)/2)],
    [(k+2,1),(k+5,1),(k+4,dx),(k+3,-dy),(len,fraction*dx*(segment.vertical+2*segment.verticalEnd)/6)]]

/-- Only point directions with exact amplitudes can seed a rational
equilibrium equation. Other columns remain available independently. -/
def columnTerms {data : Partition} {basis : GlobalBasis} (cert : Certificate data basis)
    (torques : Array (Fin basis.columns.size → Rat)) (col : Fin basis.columns.size) :
    Option (List (Nat × Rat)) :=
  let amp := fun p d => pointColumnAt cert p col d
  if ∀ point : Fin data.points.size, ∀ d : Fin 3,
      (amp point.val d).lower = (amp point.val d).upper then
    let ends := (List.finRange data.pieces.size).flatMap fun i =>
      (List.finRange 6).map fun d => (6*i.val+d.val,(amp (endPoint data.pieces[i.val]! d) (globalSlot d)).lower)
    let springs := (List.finRange torques.size).map fun i => (6*data.pieces.size+i.val,torques[i.val]! col)
    let external := FrameSpring.sumRational fun i : Fin data.source.loads.size =>
      let load := data.source.loads[i.val]!
      FrameSpring.sumRational fun d : Fin 3 =>
        (amp (locate data load.member load.t) d).lower * loadComponent load d.val
    some (ends ++ springs ++ [(width data torques.size-1,-external)])
  else none

def seedTerms {data : Partition} {basis : GlobalBasis} (cert : Certificate data basis)
    (torques : Array (Fin basis.columns.size → Rat)) :=
  (List.finRange data.pieces.size).flatMap (elementTerms data torques.size) ++
    (List.finRange basis.columns.size).filterMap (columnTerms cert torques)

def insertRows (width : Nat) : List (List (Nat × Rat)) → System → System
  | [], system => system
  | terms :: tail, system => insertRows width tail (insert system (equation width terms))

def assemble {data : Partition} {basis : GlobalBasis} (cert : Certificate data basis)
    (torques : Array (Fin basis.columns.size → Rat)) : System :=
  let n := width data torques.size
  insertRows n (seedTerms cert torques) ⟨6*data.pieces.size+torques.size,n,#[]⟩

end InclinedDiagram.Statics