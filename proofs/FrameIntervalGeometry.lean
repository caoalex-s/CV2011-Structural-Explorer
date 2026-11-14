import FrameIntervalOps

/-! Executable enclosures of original rational endpoint geometry. The proposed
    root is only a witness: squareRoot checks both squared endpoint inequalities.
    This module does not execute floating-point square roots or directions. -/
namespace FrameIntervalGeometry
open FrameIntervalOps

structure MemberBounds where
  length : Bounds
  cosine : Bounds
  sine : Bounds
  deriving Inhabited, Repr, DecidableEq

def member (bits : Nat) (dx dy : Rat) (rootWitness : Bounds) : Option MemberBounds := do
  let squared := dx*dx + dy*dy
  if squared ≤ 0 then none else
    let squaredBounds ← point bits squared
    let length ← squareRoot squaredBounds rootWitness
    if length.lower ≤ 0 then none else
      let horizontal ← point bits dx
      let vertical ← point bits dy
      let cosine ← divide bits horizontal length
      let sine ← divide bits vertical length
      some ⟨length, cosine, sine⟩

end FrameIntervalGeometry
