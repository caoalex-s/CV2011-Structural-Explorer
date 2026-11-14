import FrameIntervalOps

/-! Finite vector operations for the enclosed reduced system. The entry decoder
    must enforce n ≤ 48 before constructing these vectors. -/
namespace FrameIntervalVector
open FrameIntervalOps

def dot (bits : Nat) : {n : Nat} → (Fin n → Bounds) → (Fin n → Bounds) → Option Bounds
  | 0, _, _ => point bits 0
  | n+1, left, right => do
    let head ← multiply bits (left 0) (right 0)
    let tail ← dot bits (fun i : Fin n => left i.succ) (fun i : Fin n => right i.succ)
    add bits head tail

def magnitude (bounds : Bounds) : Rat := upperOf (-bounds.lower) bounds.upper

def magnitudeSum : {n : Nat} → (Fin n → Bounds) → Rat
  | 0, _ => 0
  | n+1, values => magnitude (values 0) + magnitudeSum (fun i : Fin n => values i.succ)

end FrameIntervalVector
