import FrameIntervalOps

/-! Arithmetic expressions authored by the checker, never decoded from a packet.
    This keeps field formulas readable while using one containment proof for
    every outward-rounded operation. Inputs are separately source-bound. -/
namespace FrameIntervalExpression
open FrameIntervalOps

inductive Expression (inputs : Nat) where
  | input : Fin inputs → Expression inputs
  | constant : Rat → Expression inputs
  | add : Expression inputs → Expression inputs → Expression inputs
  | subtract : Expression inputs → Expression inputs → Expression inputs
  | multiply : Expression inputs → Expression inputs → Expression inputs
  | divide : Expression inputs → Expression inputs → Expression inputs
  deriving Repr

instance {inputs : Nat} : Add (Expression inputs) := ⟨Expression.add⟩
instance {inputs : Nat} : Sub (Expression inputs) := ⟨Expression.subtract⟩
instance {inputs : Nat} : Mul (Expression inputs) := ⟨Expression.multiply⟩
instance {inputs : Nat} : Div (Expression inputs) := ⟨Expression.divide⟩
instance {inputs : Nat} : Neg (Expression inputs) := ⟨fun value => Expression.subtract (.constant 0) value⟩
instance {inputs value : Nat} : OfNat (Expression inputs) value := ⟨.constant value⟩

def enclose {inputs : Nat} (bits : Nat) (values : Fin inputs → Bounds) : Expression inputs → Option Bounds
  | .input index => some (values index)
  | .constant value => point bits value
  | .add left right => do
    let a ← enclose bits values left
    let b ← enclose bits values right
    FrameIntervalOps.add bits a b
  | .subtract left right => do
    let a ← enclose bits values left
    let b ← enclose bits values right
    FrameIntervalOps.subtract bits a b
  | .multiply left right => do
    let a ← enclose bits values left
    let b ← enclose bits values right
    FrameIntervalOps.multiply bits a b
  | .divide left right => do
    let a ← enclose bits values left
    let b ← enclose bits values right
    FrameIntervalOps.divide bits a b

end FrameIntervalExpression
