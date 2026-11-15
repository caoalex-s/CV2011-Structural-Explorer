import FrameIntervalOps

/-! Affine consistent nodal actions in local u/v/rotation endpoint order.
    Each action is evaluated with outward interval operations; cancellation
    in a resultant never removes the associated endpoint moments. -/
namespace FrameIntervalLoad
open FrameIntervalOps

def scaledPair (bits : Nat) (scale left right : Bounds)
    (leftWeight rightWeight denominator : Rat) : Option Bounds := do
  let a ← point bits leftWeight
  let b ← point bits rightWeight
  let divisor ← point bits denominator
  let weightedLeft ← multiply bits a left
  let weightedRight ← multiply bits b right
  let combined ← add bits weightedLeft weightedRight
  let numerator ← multiply bits scale combined
  divide bits numerator divisor

/-- Inputs are local axial and transverse intensities at both physical ends. -/
def consistentLoad (bits : Nat) (length axialLeft axialRight transverseLeft transverseRight : Bounds) :
    Option (Fin 6 → Bounds) := do
  let squared ← multiply bits length length
  let axialStart ← scaledPair bits length axialLeft axialRight 2 1 6
  let shearStart ← scaledPair bits length transverseLeft transverseRight 7 3 20
  let momentStart ← scaledPair bits squared transverseLeft transverseRight 3 2 60
  let axialEnd ← scaledPair bits length axialLeft axialRight 1 2 6
  let shearEnd ← scaledPair bits length transverseLeft transverseRight 3 7 20
  let momentEnd ← scaledPair bits squared transverseLeft transverseRight (-2) (-3) 60
  some (fun component => match component.val with
    | 0 => axialStart | 1 => shearStart | 2 => momentStart
    | 3 => axialEnd | 4 => shearEnd | _ => momentEnd)

end FrameIntervalLoad
