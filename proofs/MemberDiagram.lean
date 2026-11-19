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

def roots (a b c : Rat) : List Radical :=
  let d := b*b - 4*a*c
  if a == 0 then
    if b == 0 then [] else [rational (-c/b)]
  else if d < 0 then []
  else if d == 0 then [rational (-b/(2*a))]
  else [⟨-b/(2*a), -1/(2*a), d⟩, ⟨-b/(2*a), 1/(2*a), d⟩]

def stationary (f : Cubic) := roots (3*f.f3) (2*f.f2) f.f1

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
def proposedSqrt (d : Rat) : Box :=
  let scale := (2:Nat)^80
  let n := d.num.natAbs * d.den * scale * scale
  let root := bisectNat n (n.log2+3) 0 (n+1)
  let lo := mkRat (Int.ofNat root) (d.den*scale)
  let hi := if lo*lo == d then lo else mkRat (Int.ofNat (root+1)) (d.den*scale)
  ⟨lo, hi⟩

def sqrtBox (d : Rat) : Option Box :=
  let box := proposedSqrt d
  if 0 ≤ box.lo ∧ box.lo*box.lo ≤ d ∧ 0 ≤ box.hi ∧ d ≤ box.hi*box.hi then some box else none

def scaledBox (r : Radical) (s : Box) : Box :=
  let near := r.a + r.b*s.lo
  let far := r.a + r.b*s.hi
  if r.b < 0 then ⟨far, near⟩ else ⟨near, far⟩

def enclosure (r : Radical) : Option Box := do
  let s ← sqrtBox r.d
  let box := scaledBox r s
  if box.hi-box.lo ≤ (1:Rat)/100000000 then some box else none

def sameValue (x y : Radical) : Bool :=
  decide (x.a = y.a ∧ x.b*x.b*x.d = y.b*y.b*y.d ∧ (0 ≤ x.b ∧ 0 ≤ y.b ∨ x.b ≤ 0 ∧ y.b ≤ 0))

structure Candidate where
  piece : Nat
  side : String
  x : Box
  y : Box
  exactX : Radical
  exactY : Radical
  deriving Inhabited

def candidate (f : Cubic) (piece : Nat) (side : String) (origin : Rat) (x : Radical) : Option Candidate := do
  let pos ← enclosure {x with a := x.a + origin}
  let y := evaluate f x
  let value ← enclosure y
  return ⟨piece, side, pos, value, x, y⟩

def rootCandidate (f : Cubic) (piece : Nat) (origin len : Rat) (root : Radical) : Option (Option Candidate) := do
  let box ← enclosure root
  if box.hi ≤ 0 ∨ len ≤ box.lo then pure none
  else if 0 < box.lo ∧ box.hi < len then
    (candidate f piece "interior" origin root).bind (fun row => some (some row))
  else none

/-- Keep a result for each stationary root in order; outside roots return none. -/
def collectRoots (entry : Radical → Option (Option Candidate)) : List Radical → Option (List Candidate)
  | [] => some []
  | root :: tail => do
    let value ← entry root
    let rest ← collectRoots entry tail
    return value.toList ++ rest

def candidates (f : Cubic) (piece : Nat) (origin len : Rat) : Option (List Candidate) :=
  if 0 < len then do
    let left ← candidate f piece "start" origin (rational 0)
    let right ← candidate f piece "end" origin (rational len)
    if flat f then
      pure [left, {left with side := "flat", x := ⟨origin, origin+len⟩}, right]
    else
      let middle ← collectRoots (rootCandidate f piece origin len) (stationary f)
      pure (left :: (middle ++ [right]))
  else none

/-- Comparisons use disjoint certified enclosures or equality of the exact
radicals. An unresolved ordering causes the entire diagram to be inconclusive. -/
def lessEqual (x y : Candidate) : Bool :=
  x.y.hi < y.y.lo || (x.y.lo == x.y.hi && y.y.lo == y.y.hi && x.y.lo == y.y.lo) || sameValue x.exactY y.exactY

def number (r : Rat) := toString r.num ++ "/" ++ toString r.den

def ranked (rows : List Candidate) : Bool :=
  !rows.isEmpty && rows.all fun r => rows.all fun s => lessEqual r s || lessEqual s r

def extremaRows (kind : String) (rows : List Candidate) : List String :=
  rows.map fun r =>
    String.intercalate " " [kind, toString r.piece, r.side, number r.x.lo, number r.x.hi,
      number r.y.lo, number r.y.hi, if rows.all (lessEqual r) then "1" else "0",
      if rows.all (fun s => lessEqual s r) then "1" else "0"]

def coefficients (f : Cubic) := [number f.f0, number f.f1, number f.f2, number f.f3]

def selected (data : Compiled) (member : Nat) :=
  (List.finRange data.segments.size).filter fun i => data.segments[i.val]!.member == member

abbrev Index (data : Compiled) (member : Nat) := Fin (selected data member).length

def segmentAt (data : Compiled) (m : Nat) (i : Index data m) : Segment :=
  data.segments[((selected data m).get i).val]!

def originAt (data : Compiled) (m : Nat) (i : Index data m) :=
  memberLength data.source m * (segmentAt data m i).left

def pieceRows (data : Compiled) (m : Nat) (motion : Segment → Array Rat) (moment : Bool) (i : Index data m) :=
  let s := segmentAt data m i
  candidates (polynomial s (motion s) moment) i.val (originAt data m i) s.length

structure Evaluated {α : Type} (computation : Option α) where
  value : α
  computed : computation = some value

def evaluateOption {α : Type} (op : Option α) : Option (Evaluated op) :=
  match op with
  | none => none
  | some value => some ⟨value, rfl⟩

def gather : (n : Nat) → (V : Fin n → Type) → ((i : Fin n) → Option (V i)) → Option ((i : Fin n) → V i)
  | 0, _, _ => some (fun i => Fin.elim0 i)
  | n+1, V, entry => do
    let head ← entry 0
    let tail ← gather n (fun i => V i.succ) (fun i => entry i.succ)
    return Fin.cases head tail

structure Sheet (data : Compiled) (m : Nat) (motion : Segment → Array Rat) where
  rows : (moment : Bool) → (i : Index data m) → Evaluated (pieceRows data m motion moment i)

def allRows {data m motion} (sheet : Sheet data m motion) (moment : Bool) :=
  (List.finRange (selected data m).length).flatMap fun i => (sheet.rows moment i).value

def buildSheet (data : Compiled) (m : Nat) (motion : Segment → Array Rat) : Option (Sheet data m motion) := do
  let table := fun flag => gather (selected data m).length _ fun i => evaluateOption (pieceRows data m motion flag i)
  let shear ← table false
  let moment ← table true
  return ⟨fun flag => match flag with | false => shear | true => moment⟩

def encode {data m motion} (sheet : Sheet data m motion) : String :=
  let pieces := (List.finRange (selected data m).length).map fun i =>
    let s := segmentAt data m i
    let origin := originAt data m i
    String.intercalate " " (["P", number origin, number (origin+s.length)] ++
      coefficients (polynomial s (motion s) false) ++ coefficients (polynomial s (motion s) true))
  String.intercalate "\n" (["CV2011_DIAGRAM_1", data.source.members[m]!.id] ++ pieces ++
    extremaRows "V" (allRows sheet false) ++ extremaRows "M" (allRows sheet true))

@[export member_diagram_report]
def checkReport (input : String) : Option String := do
  let p ← RationalFrame.Wire.decode input
  if !p.certificate.mechanism && accepts p.source p.query p.certificate then
    let data ← compileModel p.source
    let sheet ← buildSheet data p.query.member (fun _ => p.certificate.motion)
    if ranked (allRows sheet false) && ranked (allRows sheet true) && (encode sheet).utf8ByteSize ≤ 262144 then
      return encode sheet
    else none
  else none

end MemberDiagram
