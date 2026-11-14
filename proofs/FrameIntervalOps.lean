import Batteries.Data.Rat.Basic

/-! Executable rational enclosure operations. Rounding proposes endpoints and
    then checks the defining rational inequalities. Soundness therefore does
    not trust the floor implementation. No real arithmetic enters this module. -/
namespace FrameIntervalOps

structure Bounds where
  lower : Rat
  upper : Rat
  deriving Inhabited, Repr, DecidableEq

def bounded (x : Rat) : Bool :=
  (toString x.num.natAbs).length ≤ 128 && (toString x.den).length ≤ 128

def valid (a : Bounds) : Bool := a.lower ≤ a.upper && bounded a.lower && bounded a.upper

def precisionValid (bits : Nat) : Bool := bits == 32 || bits == 64 || bits == 96 || bits == 128

/-- The postcheck explicitly establishes the inequality used by every caller. -/
def outward (bits : Nat) (lower upper : Rat) : Option Bounds := do
  if !precisionValid bits || lower > upper then none else
    let scale : Rat := 2^bits
    let out : Bounds := ⟨(Rat.floor (lower*scale) : Rat)/scale,
      (Rat.ceil (upper*scale) : Rat)/scale⟩
    if valid out && out.lower ≤ lower && upper ≤ out.upper then some out else none

def point (bits : Nat) (x : Rat) : Option Bounds := outward bits x x

def add (bits : Nat) (a b : Bounds) : Option Bounds :=
  if valid a && valid b then outward bits (a.lower+b.lower) (a.upper+b.upper) else none

def negate (bits : Nat) (a : Bounds) : Option Bounds :=
  if valid a then outward bits (-a.upper) (-a.lower) else none

def subtract (bits : Nat) (a b : Bounds) : Option Bounds :=
  if valid a && valid b then outward bits (a.lower-b.upper) (a.upper-b.lower) else none

def multiply (bits : Nat) (a b : Bounds) : Option Bounds :=
  if valid a && valid b then
    let ll := a.lower*b.lower
    let lu := a.lower*b.upper
    let ul := a.upper*b.lower
    let uu := a.upper*b.upper
    outward bits (min (min ll lu) (min ul uu)) (max (max ll lu) (max ul uu))
  else none

def reciprocal (bits : Nat) (a : Bounds) : Option Bounds :=
  if valid a && (0 < a.lower || a.upper < 0) then
    outward bits (1/a.upper) (1/a.lower)
  else none

def divide (bits : Nat) (a b : Bounds) : Option Bounds := do
  let inverse ← reciprocal bits b
  multiply bits a inverse

/-- Root endpoints are witnesses; their squared inequalities are checked exactly. -/
def squareRoot (a witness : Bounds) : Option Bounds :=
  if valid a && valid witness && 0 ≤ a.lower && 0 ≤ witness.lower &&
      witness.lower*witness.lower ≤ a.lower && a.upper ≤ witness.upper*witness.upper then
    some witness
  else none

end FrameIntervalOps
