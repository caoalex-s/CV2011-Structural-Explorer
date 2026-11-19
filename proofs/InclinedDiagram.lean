import MemberDiagram
import FrameIntervalExpression
import InclinedDiagramStatics

/-! Inclined member fields in fractional piece distance t. Multiplying the
direction cosine by the piece length gives its signed horizontal projection,
so both variable shear coefficients remain rational for irrational lengths. -/
namespace InclinedDiagram
open FrameIntervalOps

structure Piece where
  left : Rat
  right : Rat
  memberLength : Bounds
  shearStart : Bounds
  momentStart : Bounds
  linear : Rat
  quadratic : Rat
  -- Reduced forms for L*V₀ and M₀ on the same global equilibrium system.
  scaledShear : Statics.Row := #[]
  initialMoment : Statics.Row := #[]
  lengthColumn : Nat := 0
  deriving Inhabited

def singleton (r : Rat) : Bounds := ⟨r,r⟩

/-- Enclosures contain exact algebraic values. Each square-root endpoint is
proposed with integer bisection and its square is checked before use. -/
def rootBox (b : Bounds) : Option Bounds := do
  let lower ← MemberDiagram.sqrtBox b.lower
  let upper ← MemberDiagram.sqrtBox b.upper
  return ⟨lower.lo,upper.hi⟩

def scale (k : Rat) (b : Bounds) : Bounds :=
  if 0 ≤ k then ⟨k*b.lower,k*b.upper⟩ else ⟨k*b.upper,k*b.lower⟩

def shift (a : Rat) (b : Bounds) : Bounds := ⟨a+b.lower,a+b.upper⟩

inductive Station where
  | fixed (value : Rat)
  | linearRoot
  | quadraticRoot (plus : Bool)
  deriving Inhabited, DecidableEq

def discriminant (p : Piece) := shift (p.linear*p.linear) (scale (-4*p.quadratic) p.shearStart)

def stationBox (p : Piece) : Station → Option Bounds
  | .fixed r => some (singleton r)
  | .linearRoot => some (scale (-1/p.linear) p.shearStart)
  | .quadraticRoot plus => do
    let d ← rootBox (discriminant p)
    let denominator := 2*p.quadratic
    return shift (-p.linear/denominator) (scale ((if plus then 1 else -1)/denominator) d)

/-- A successful list accounts for each real derivative zero. A discriminant
whose sign cannot be established makes the diagram inconclusive. -/
def stationary (p : Piece) (moment : Bool) : Option (List Station) :=
  if moment then
    if p.quadratic = 0 then
      if p.linear = 0 then
        if p.shearStart.upper < 0 ∨ 0 < p.shearStart.lower ∨ p.shearStart = singleton 0 then some [] else none
      else some [.linearRoot]
    else
      let d := discriminant p
      if d.upper < 0 then some []
      else if d = singleton 0 then some [.fixed (-p.linear/(2*p.quadratic))]
      else if 0 < d.lower then some [.quadraticRoot false,.quadraticRoot true]
      else none
  else if p.quadratic = 0 then some []
  else some [.fixed (-p.linear/(2*p.quadratic))]

def flat (p : Piece) (moment : Bool) : Bool :=
  p.linear == 0 && p.quadratic == 0 && (!moment || p.shearStart == singleton 0)

/-- Inputs are V0, M0, member length and t. The affine load coefficients
come directly from the drawing and every interval has its own physical span. -/
def quantity (p : Piece) (moment : Bool) : FrameIntervalExpression.Expression 4 :=
  let v := FrameIntervalExpression.Expression.input 0
  let m := FrameIntervalExpression.Expression.input 1
  let L := FrameIntervalExpression.Expression.input 2
  let t := FrameIntervalExpression.Expression.input 3
  let lit := @FrameIntervalExpression.Expression.constant 4
  if moment then m+L*lit (p.right-p.left)*t*(v+t*(lit (p.linear/2)+t*lit (p.quadratic/3)))
  else v+t*(lit p.linear+t*lit p.quadratic)

def values (p : Piece) (t : Bounds) (i : Fin 4) : Bounds :=
  match i.val with
  | 0 => p.shearStart
  | 1 => p.momentStart
  | 2 => p.memberLength
  | _ => t

def evaluate (bits : Nat) (p : Piece) (moment : Bool) (t : Bounds) :=
  FrameIntervalExpression.enclose bits (values p t) (quantity p moment)

def narrow (b : Bounds) := valid b && (b.upper-b.lower ≤ (1:Rat)/100000000)

structure Candidate where
  piece : Nat
  side : String
  station : Station
  t : Bounds
  x : Bounds
  y : Bounds
  /-- For rational stations, V(t)−V(0) is rational. It proves exact
  equality/order on the same piece without comparing two uncertain baselines. -/
  shearOffset : Option Rat
  signature : Statics.Row
  deriving Inhabited

/-- Quantities in the same shear group all use the same positive multiplier
L. Moments are compared directly. At rational stations their forms are
linear in end actions, spring torques and source lengths. -/
def fieldSignature (p : Piece) (moment : Bool) (t : Rat) : Statics.Row := Id.run do
  if p.scaledShear.isEmpty then return #[]
  if moment then
    let span := (p.right-p.left)*t
    let linear := p.initialMoment.mapIdx fun i a => a + span*p.scaledShear[i]!
    return linear.modify p.lengthColumn (· + span*t*(p.linear/2+t*p.quadratic/3))
  return p.scaledShear.modify p.lengthColumn (· + t*(p.linear+t*p.quadratic))

def row (bits piece : Nat) (p : Piece) (moment : Bool) (side : String) (station : Station) : Option Candidate := do
  let t ← stationBox p station
  let memberFraction := shift p.left (scale (p.right-p.left) t)
  let x ← multiply bits p.memberLength memberFraction
  let y ← evaluate bits p moment t
  guard (narrow t && narrow x && narrow y)
  let offset := match station with
    | .fixed v => if moment then none else some (v*(p.linear+v*p.quadratic))
    | _ => none
  let signature := match station with
    | .fixed value => fieldSignature p moment value
    | _ => #[]
  return ⟨piece,side,station,t,x,y,offset,signature⟩

def interior (bits piece : Nat) (p : Piece) (moment : Bool) (station : Station) : Option (Option Candidate) := do
  let t ← stationBox p station
  if t.upper ≤ 0 ∨ 1 ≤ t.lower then pure none
  else if 0 < t.lower ∧ t.upper < 1 then
    (row bits piece p moment "interior" station).bind (fun v => some (some v))
  else none

def rows (bits piece : Nat) (p : Piece) (moment : Bool) : Option (List Candidate) := do
  let a ← row bits piece p moment "start" (.fixed 0)
  let b ← row bits piece p moment "end" (.fixed 1)
  if flat p moment then
    let plateau := {a with side := "flat", t := ⟨0,1⟩, x := ⟨a.x.lower,b.x.upper⟩}
    pure [a,plateau,b]
  else
    let stations ← stationary p moment
    let inner ← stations.mapM (interior bits piece p moment)
    pure (a :: inner.reduceOption ++ [b])

inductive OrderEvidence where | less | equal | greater | unresolved
  deriving BEq, DecidableEq, Inhabited

def compareValues (a b : Candidate) : OrderEvidence :=
  if a.piece == b.piece && a.station == b.station then .equal
  else if a.piece = b.piece ∧ a.shearOffset.isSome ∧ b.shearOffset.isSome then
    let x := a.shearOffset.getD 0
    let y := b.shearOffset.getD 0
    if x < y then .less else if x = y then .equal else .greater
  else if !a.signature.isEmpty && a.signature == b.signature then .equal
  else if a.y.upper < b.y.lower then .less
  else if b.y.upper < a.y.lower then .greater
  else if a.y.lower = a.y.upper ∧ b.y.lower = b.y.upper ∧ a.y.lower = b.y.lower then .equal
  else .unresolved

/-- A nonextremal candidate only needs a strictly better witness. Overlap
between two nonextremal candidates does not obscure the extrema flags. -/
def isExtreme (maximum : Bool) (a : Candidate) (all : List Candidate) : Option Bool :=
  let bad := if maximum then OrderEvidence.less else OrderEvidence.greater
  let comparisons := all.map (compareValues a)
  if comparisons.contains bad then some false
  else if comparisons.contains .unresolved then none
  else some true

end InclinedDiagram
