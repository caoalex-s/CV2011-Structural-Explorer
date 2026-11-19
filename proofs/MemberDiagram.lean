import RationalFrameWire

/-! Whole-member fields for the stable exact cardinal-frame checker. Distances
are metres along the drawn member. Each piece uses its own origin. -/
namespace MemberDiagram
open RationalFrame

structure Cubic where
  f0 : Rat
  f1 : Rat
  f2 : Rat
  f3 : Rat
  deriving Inhabited

def polynomial (s : Segment) (motion : Array Rat) (moment : Bool) : Cubic :=
  let shear := endAction s motion 1
  let q := s.cosine * s.vertical
  let dq := s.cosine * (s.verticalEnd - s.vertical) / s.length
  if moment then ⟨-endAction s motion 2, shear, q/2, dq/6⟩ else ⟨shear, q, dq/2, 0⟩

/-- The exact real number a + b sqrt(d). Roots of the derivative and the
corresponding polynomial values lie in the same quadratic extension. -/
structure Radical where
  a : Rat
  b : Rat
  d : Rat
  deriving Inhabited

def rational (x : Rat) : Radical := ⟨x, 0, 0⟩

def hornerStep (x y : Radical) (constant : Rat) : Radical :=
  ⟨constant + x.a*y.a + x.b*y.b*x.d, x.a*y.b + x.b*y.a, x.d⟩

def evaluate (f : Cubic) (x : Radical) : Radical :=
  hornerStep x (hornerStep x (hornerStep x ⟨f.f3, 0, x.d⟩ f.f2) f.f1) f.f0

def flat (f : Cubic) := f.f1 == 0 && f.f2 == 0 && f.f3 == 0

def stationary (f : Cubic) : List Radical :=
  let a := 3*f.f3
  let b := 2*f.f2
  let c := f.f1
  let d := b*b - 4*a*c
  if a == 0 then
    if b == 0 then [] else [rational (-c/b)]
  else if d < 0 then []
  else if d == 0 then [rational (-b/(2*a))]
  else [⟨-b/(2*a), -1/(2*a), d⟩, ⟨-b/(2*a), 1/(2*a), d⟩]

structure Box where
  lo : Rat
  hi : Rat
  deriving Inhabited

def bisectNat (n : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if hi ≤ lo+1 then lo else
      let mid := (lo+hi)/2
      if mid*mid ≤ n then bisectNat n fuel mid hi else bisectNat n fuel lo mid

/-- Each bound is checked by squaring, so correctness does not depend on the
integer square-root proposal. A perfect rational square has zero width. -/
def sqrtBox (d : Rat) : Option Box := do
  guard (0 ≤ d)
  let scale := (2:Nat)^80
  let n := d.num.natAbs * d.den * scale * scale
  let root := bisectNat n (n.log2+3) 0 (n+1)
  let lo := mkRat (Int.ofNat root) (d.den*scale)
  let hi := if lo*lo == d then lo else mkRat (Int.ofNat (root+1)) (d.den*scale)
  guard (0 ≤ lo && lo*lo ≤ d && 0 ≤ hi && d ≤ hi*hi)
  return ⟨lo, hi⟩

def enclosure (r : Radical) : Option Box := do
  let s ← sqrtBox r.d
  let near := r.a + r.b*s.lo
  let far := r.a + r.b*s.hi
  let box : Box := if r.b < 0 then ⟨far, near⟩ else ⟨near, far⟩
  guard (box.hi-box.lo ≤ (1:Rat)/100000000)
  return box

def sameValue (x y : Radical) : Bool :=
  x.a == y.a && x.b*x.b*x.d == y.b*y.b*y.d && (x.b < 0) == (y.b < 0)

structure Candidate where
  piece : Nat
  side : String
  x : Box
  y : Box
  exactY : Radical
  deriving Inhabited

def candidate (f : Cubic) (piece : Nat) (side : String) (origin : Rat) (x : Radical) : Option Candidate := do
  let pos ← enclosure {x with a := x.a + origin}
  let y := evaluate f x
  let value ← enclosure y
  return ⟨piece, side, pos, value, y⟩

def candidates (f : Cubic) (piece : Nat) (origin len : Rat) : Option (List Candidate) := do
  guard (len > 0)
  if flat f then
    let value ← candidate f piece "flat" origin (rational 0)
    return [{value with x := ⟨origin, origin+len⟩}]
  let left ← candidate f piece "start" origin (rational 0)
  let right ← candidate f piece "end" origin (rational len)
  let middle ← (stationary f).mapM fun root => do
    let box ← enclosure root
    if box.hi ≤ 0 || len ≤ box.lo then return none
    guard (0 < box.lo && box.hi < len)
    return some (← candidate f piece "interior" origin root)
  return left :: middle.filterMap id ++ [right]

/-- Comparisons use disjoint certified enclosures or equality of the exact
radicals. An unresolved ordering causes the entire diagram to be inconclusive. -/
def lessEqual (x y : Candidate) : Bool :=
  x.y.hi ≤ y.y.lo || sameValue x.exactY y.exactY

def number (r : Rat) := toString r.num ++ "/" ++ toString r.den

def extremaRows (kind : String) (rows : List Candidate) : Option (List String) := do
  guard (!rows.isEmpty && rows.all fun r => rows.all fun s => lessEqual r s || lessEqual s r)
  return rows.map fun r =>
    String.intercalate " " [kind, toString r.piece, r.side, number r.x.lo, number r.x.hi,
      number r.y.lo, number r.y.hi, if rows.all (lessEqual r) then "1" else "0",
      if rows.all (fun s => lessEqual s r) then "1" else "0"]

def coefficients (f : Cubic) := [number f.f0, number f.f1, number f.f2, number f.f3]

def diagram (data : Compiled) (member : Nat) (motion : Array Rat) : Option String := do
  let mut pieces := #[]
  let mut v := []
  let mut m := []
  let length := memberLength data.source member
  for s in data.segments do
    if s.member == member then
      let origin := length * s.left
      let shear := polynomial s motion false
      let moment := polynomial s motion true
      v := v ++ (← candidates shear pieces.size origin s.length)
      m := m ++ (← candidates moment pieces.size origin s.length)
      pieces := pieces.push (String.intercalate " " (["P", number origin, number (origin+s.length)] ++
        coefficients shear ++ coefficients moment))
  let vRows ← extremaRows "V" v
  let mRows ← extremaRows "M" m
  return String.intercalate "\n" (["CV2011_DIAGRAM_1", data.source.members[member]!.id] ++ pieces.toList ++ vRows ++ mRows)

@[export member_diagram_report]
def checkReport (input : String) : Option String := do
  let p ← RationalFrame.Wire.decode input
  guard (!p.certificate.mechanism && accepts p.source p.query p.certificate)
  let data ← compileModel p.source
  let out ← diagram data p.query.member p.certificate.motion
  guard (out.utf8ByteSize ≤ 262144)
  return out

end MemberDiagram
