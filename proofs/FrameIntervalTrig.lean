import FrameIntervalOps

/-! Bounded rational trigonometric reconstruction. Both doubled coordinates use
    the preceding pair; updating one coordinate early would change the formula. -/
namespace FrameIntervalTrig
open FrameIntervalOps

structure Axes where
  sine : Bounds
  cosine : Bounds
  deriving Inhabited, Repr, DecidableEq

def smallAngle (bits : Nat) (angle : Bounds) : Option Axes := do
  let magnitude := max (-angle.lower) angle.upper
  if !valid angle || magnitude > 1 then none else
    let squared ← multiply bits angle angle
    let cubed ← multiply bits squared angle
    let six ← point bits 6
    let two ← point bits 2
    let one ← point bits 1
    let error := 5*magnitude^4/96
    let remainder ← outward bits (-error) error
    let cubicTerm ← divide bits cubed six
    let sinePolynomial ← subtract bits angle cubicTerm
    let sine ← add bits sinePolynomial remainder
    let squareTerm ← divide bits squared two
    let cosinePolynomial ← subtract bits one squareTerm
    let cosine ← add bits cosinePolynomial remainder
    some ⟨sine, cosine⟩

def doubleAngle (bits : Nat) (axes : Axes) : Option Axes := do
  let two ← point bits 2
  let product ← multiply bits axes.sine axes.cosine
  let sine ← multiply bits two product
  let cosineSquared ← multiply bits axes.cosine axes.cosine
  let sineSquared ← multiply bits axes.sine axes.sine
  let cosine ← subtract bits cosineSquared sineSquared
  some ⟨sine, cosine⟩

/-- The caller limits the halving count to the protocol's maximum of 32. -/
def doubleAngles (bits : Nat) : Nat → Axes → Option Axes
  | 0, axes => some axes
  | count+1, axes => do
    let doubled ← doubleAngle bits axes
    doubleAngles bits count doubled

/-- Source reduction is checked as an exact rational equality. The integer turn
    count is a witness, not an approximation to an angle modulo 360 degrees.
    Exact cardinal shortcuts are handled separately by the source compiler. -/
def degreeAxesGeneral (bits : Nat) (source reduced : Rat) (turns : Int) : Option Axes := do
  if !precisionValid bits || reduced < -180 || 180 < reduced ||
      source != reduced + 360 * (turns : Rat) then none else
    let halvings := bits / 4
    let pi ← outward bits (314159265358979323846 / 100000000000000000000)
      (314159265358979323847 / 100000000000000000000)
    let degrees ← point bits (reduced/180)
    let radians ← multiply bits degrees pi
    let scale ← point bits (2^halvings)
    let small ← divide bits radians scale
    let axes ← smallAngle bits small
    doubleAngles bits halvings axes

end FrameIntervalTrig
