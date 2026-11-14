import FrameIntervalOps

/-! Executable local Euler–Bernoulli stiffness coefficients. The supplied length
    enclosure must first be established from the original member endpoints. -/
namespace FrameIntervalElement
open FrameIntervalOps

structure Coefficients where
  axial : Bounds
  bending : Bounds
  coupling : Bounds
  rotation : Bounds
  crossRotation : Bounds
  deriving Inhabited, Repr, DecidableEq

def coefficients (bits : Nat) (length : Bounds) (EA EI : Rat) : Option Coefficients := do
  let axialRigidity ← point bits EA
  let bendingRigidity ← point bits EI
  let twelve ← point bits 12
  let six ← point bits 6
  let four ← point bits 4
  let two ← point bits 2
  let squared ← multiply bits length length
  let cubed ← multiply bits squared length
  let bendingNumerator ← multiply bits twelve bendingRigidity
  let couplingNumerator ← multiply bits six bendingRigidity
  let rotationNumerator ← multiply bits four bendingRigidity
  let axial ← divide bits axialRigidity length
  let bending ← divide bits bendingNumerator cubed
  let coupling ← divide bits couplingNumerator squared
  let rotation ← divide bits rotationNumerator length
  let crossRotation ← divide bits rotation two
  some ⟨axial, bending, coupling, rotation, crossRotation⟩

def zero : Bounds := ⟨0, 0⟩
def negative (a : Bounds) : Bounds := ⟨-a.upper, -a.lower⟩

/-- Local order is u, v, rotation at the first end, followed by the second end. -/
def entry (values : Coefficients) (i j : Fin 6) : Bounds :=
  match i.val, j.val with
  | 0, 0 | 3, 3 => values.axial
  | 0, 3 | 3, 0 => negative values.axial
  | 1, 1 | 4, 4 => values.bending
  | 1, 4 | 4, 1 => negative values.bending
  | 1, 2 | 2, 1 | 1, 5 | 5, 1 => values.coupling
  | 2, 4 | 4, 2 | 4, 5 | 5, 4 => negative values.coupling
  | 2, 2 | 5, 5 => values.rotation
  | 2, 5 | 5, 2 => values.crossRotation
  | _, _ => zero

end FrameIntervalElement
