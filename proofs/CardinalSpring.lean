import FrameSpringWire
import HingeFrameChecker

/-! Exact cardinal equilibrium with shared translations and side-owned rotations.
The LDL factors and motion computed below are proposals. The checker verifies
the factorization and every free equilibrium equation against the original
drawing before any section field uses that motion. -/
namespace CardinalSpring
open RationalFrame

structure System where
  beam : HingeFrame.Assembly
  stiffnesses : Array Rat

def referenceRow (s : System) (side : Nat) :=
  3 * InclinedRelease.endpoint s.beam.mesh.source.members[side/2]! side + 2

def ConnectedRows (s : System) : Prop :=
  ∀ side ∈ s.beam.sides, let q := HingeFrame.faceQuery side
    let source := s.beam.mesh.source
    let node := InclinedRelease.endpoint source.members[q.member]! side
    let ref := HingeFrame.reference source node
    let refT : Rat := if source.members[ref]!.a = node then 0 else 1
    ref < source.members.size ∧ (source.members[ref]!.a = node ∨ source.members[ref]!.b = node) ∧
    HingeFrame.pointIndex s.beam q.member q.t 2 = s.beam.mesh.dofs + s.beam.sides.idxOf side ∧
    HingeFrame.pointIndex s.beam ref refT 2 = referenceRow s side

instance (s : System) : Decidable (ConnectedRows s) := by unfold ConnectedRows; infer_instance

def compile (p : FrameSpring.Wire.Packet) : Option System := do
  let (layout, ks) ← FrameSpring.resolve p.source p.rules
  let mesh ← compileModel p.source
  if valid : PartitionValid mesh then
    let a : HingeFrame.Assembly := ⟨mesh, layout.sides.toList, valid⟩
    let s : System := ⟨a,ks⟩
    if a.size ≤ 48 ∧ ConnectedRows s then some s else none
  else none

def gapColumn (s : System) (side row : Nat) : Rat :=
  let own := s.beam.mesh.dofs + s.beam.sides.idxOf side
  (if row == own then 1 else 0) - (if row == referenceRow s side then 1 else 0)

def matrix (s : System) : Array (Array Rat) :=
  HingeFrame.tabulate s.beam.size fun i => HingeFrame.tabulate s.beam.size fun j =>
    HingeFrame.stiffness s.beam i j + (s.beam.sides.map fun side =>
      s.stiffnesses[side]! * gapColumn s side i * gapColumn s side j).sum

def freeRows (s : System) := ((List.range s.beam.size).filter fun i => !HingeFrame.restrained s.beam i).toArray
def loads (s : System) := HingeFrame.tabulate s.beam.size (HingeFrame.force s.beam)

def gap (s : System) (u : Array Rat) (side : Nat) :=
  u[s.beam.mesh.dofs + s.beam.sides.idxOf side]! - u[referenceRow s side]!

/-- Local section convention gives -M at a first end and +M at a last end.
The beam end action plus the spring restoring action balances the external
couple and any rotational support reaction acting on that same face. -/
def faceLaw (s : System) (w : Certificate) (side : Nat) : Prop :=
  let q := HingeFrame.faceQuery side
  let moment := (HingeFrame.sectionValues s.beam q w.motion)[2]!
  let row := HingeFrame.pointIndex s.beam q.member q.t 2
  (if q.right then -moment else moment) + s.stiffnesses[side]! * gap s w.motion side =
    HingeFrame.faceCouple s.beam q + (if HingeFrame.restrained s.beam row then w.reactions[row]! else 0)

instance (s : System) (w : Certificate) (side : Nat) : Decidable (faceLaw s w side) := by
  unfold faceLaw; infer_instance

def Equilibrium (s : System) (k : Array (Array Rat)) (w : Certificate) : Prop :=
  FactorValid k (freeRows s) w ∧ w.motion.size = s.beam.size ∧
  w.reactions = residual k (loads s) w.motion ∧
  (∀ i : Fin s.beam.size, if HingeFrame.restrained s.beam i then w.motion[i.val]! = 0 else w.reactions[i.val]! = 0) ∧
  (∀ i : Fin s.beam.sides.length, faceLaw s w (s.beam.sides.get i)) ∧
  (∀ i : Fin (freeRows s).size,
    sumFin (freeRows s).size (fun j => k[(freeRows s)[i.val]!]![(freeRows s)[j.val]!]! * w.motion[(freeRows s)[j.val]!]!) =
      (loads s)[(freeRows s)[i.val]!]!)

instance (s : System) (k : Array (Array Rat)) (w : Certificate) : Decidable (Equilibrium s k w) := by
  unfold Equilibrium; infer_instance

/-- Limit intermediate rational growth during the untrusted factor proposal. -/
def small (r : Rat) := r.num.natAbs.log2 ≤ 4096 && r.den.log2 ≤ 4096

def solve (s : System) (k : Array (Array Rat)) : Option Certificate := do
  let free := freeRows s
  let n := free.size
  let forces := loads s
  let mut lower : Array (Array Rat) := Array.replicate n (Array.replicate n 0)
  let mut diagonal : Array Rat := Array.replicate n 0
  let mut y : Array Rat := Array.replicate n 0
  for i in [:n] do
    for j in [:i+1] do
      let mut entry := k[free[i]!]![free[j]!]!
      for t in [:j] do
        entry := entry - lower[i]![t]! * diagonal[t]! * lower[j]![t]!
      if i == j then
        guard (entry > 0 && small entry)
        diagonal := diagonal.set! i entry
        lower := lower.set! i (lower[i]!.set! j 1)
      else
        let quotient := entry / diagonal[j]!
        guard (small quotient)
        lower := lower.set! i (lower[i]!.set! j quotient)
    let mut value := forces[free[i]!]!
    for j in [:i] do value := value - lower[i]![j]! * y[j]!
    guard (small value)
    y := y.set! i value
  let mut u : Array Rat := Array.replicate s.beam.size 0
  for reverse in [:n] do
    let i := n - 1 - reverse
    let mut value := y[i]! / diagonal[i]!
    for j in [i+1:n] do value := value - lower[j]![i]! * u[free[j]!]!
    guard (small value)
    u := u.set! free[i]! value
  return { (default : Certificate) with motion := u, lower, diagonal, reactions := residual k forces u }

end CardinalSpring
