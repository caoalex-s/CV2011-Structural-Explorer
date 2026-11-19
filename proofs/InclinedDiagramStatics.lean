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
  if factor = 0 then target else target.mapIdx fun i a => a - factor*pivot[i]!

def reduce (system : System) (row : Row) : Row :=
  system.pivots.foldl (fun r entry => subtractMultiple r entry.2 r[entry.1]!) row

/-- Echelon rows may be kept in insertion order. Each later pivot row
has zero coefficient at every preceding pivot. -/
def insert (system : System) (equation : Row) : System := Id.run do
  let remainder := reduce system equation
  let some pivot := (List.range system.unknowns).find? (fun i => remainder[i]! != 0) | return system
  let normalized := remainder.map (· / remainder[pivot]!)
  return {system with pivots := system.pivots.push (pivot,normalized)}

def equation (width : Nat) (terms : List (Nat × Rat)) : Row :=
  terms.foldl (fun row term => row.modify term.1 (· + term.2)) (Array.replicate width 0)

def loadComponent (load : RationalFrame.Load) (d : Nat) : Rat :=
  if load.kind = 0 then if d = 0 then load.fx else if d = 1 then load.fy else 0
  else if load.kind = 1 && d = 2 then load.mz else 0

/-- An uncertain roller tangent cannot seed a rational equilibrium equation.
All other columns of the same assembly remain usable. -/
def columnEquation {data : Partition} {basis : GlobalBasis} (cert : Certificate data basis)
    (torques : Array (Fin basis.columns.size → Rat)) (col : Fin basis.columns.size)
    (width : Nat) : Option Row := do
  let mut row := Array.replicate width (0 : Rat)
  for i in [:data.pieces.size] do
    let segment := data.pieces[i]!
    for component in [:6] do
      let point := if component < 3 then segment.a else segment.b
      let v := pointColumnAt cert point col ⟨component%3,Nat.mod_lt _ (by decide)⟩
      guard (v.lower = v.upper)
      row := row.set! (6*i+component) v.lower
  for i in [:torques.size] do
    row := row.set! (6*data.pieces.size+i) (torques[i]! col)
  let mut applied : Rat := 0
  for load in data.source.loads do
    for component in List.finRange 3 do
      let v := pointColumnAt cert (locate data load.member load.t) col component
      guard (v.lower = v.upper)
      applied := applied + v.lower*loadComponent load component.val
  return row.set! (width-1) (-applied)

def assemble {data : Partition} {basis : GlobalBasis} (cert : Certificate data basis)
    (torques : Array (Fin basis.columns.size → Rat)) : System := Id.run do
  let unknowns := 6*data.pieces.size + torques.size
  let width := unknowns + data.source.members.size + 1
  let mut system : System := ⟨unknowns,width,#[]⟩
  for i in [:data.pieces.size] do
    let segment := data.pieces[i]!
    let a := data.points[segment.a]!
    let b := data.points[segment.b]!
    let fraction := segment.right-segment.left
    let len := unknowns + segment.member
    let k := 6*i
    -- Global force and moment balance about the first end. The affine
    -- load has resultant ell*(f0+f1)/2 and first moment ell*dx*(f0+2*f1)/6.
    system := insert system (equation width [(k,1),(k+3,1)])
    system := insert system (equation width [(k+1,1),(k+4,1),(len,fraction*(segment.vertical+segment.verticalEnd)/2)])
    system := insert system (equation width [(k+2,1),(k+5,1),(k+4,b.x-a.x),(k+3,a.y-b.y),
      (len,fraction*(b.x-a.x)*(segment.vertical+2*segment.verticalEnd)/6)])
  for col in List.finRange basis.columns.size do
    if let some row := columnEquation cert torques col width then system := insert system row
  return system

end InclinedDiagram.Statics
