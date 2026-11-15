import FrameIntervalVector

/-! Interval assembly of source-owned element contributions. The source compiler
    supplies the physical local stiffness/load and projected basis enclosures.
    These operations do not accept a producer's assembled matrix as evidence. -/
namespace FrameIntervalAssembly
open FrameIntervalOps FrameIntervalVector

/-- Evaluate and accumulate each term, propagating every arithmetic failure. -/
def sumTerms (bits : Nat) : {size : Nat} → (Fin size → Option Bounds) → Option Bounds
  | 0, _ => point bits 0
  | size+1, terms => do
    let head ← terms 0
    let tail ← sumTerms bits (fun index : Fin size => terms index.succ)
    add bits head tail

/-- One entry of Pᵀ Tᵀ k T P; the two projected columns share the same source
    element and orientation. Local order is u/v/rotation at each endpoint. -/
def elementEntry (bits : Nat) (stiffness : Fin 6 → Fin 6 → Bounds)
    (rowProjection columnProjection : Fin 6 → Bounds) : Option Bounds :=
  sumTerms bits fun row => do
    let action ← dot bits (stiffness row) columnProjection
    multiply bits (rowProjection row) action

def matrixEntry {pieces coordinates : Nat} (bits : Nat)
    (stiffness : Fin pieces → Fin 6 → Fin 6 → Bounds)
    (projection : Fin pieces → Fin 6 → Fin coordinates → Bounds)
    (row column : Fin coordinates) : Option Bounds :=
  sumTerms bits fun piece => elementEntry bits (stiffness piece)
    (fun localRow => projection piece localRow row) (fun localRow => projection piece localRow column)

/-- Distributed-load virtual work is accumulated over every physical piece. -/
def distributedEntry {pieces coordinates : Nat} (bits : Nat)
    (load : Fin pieces → Fin 6 → Bounds)
    (projection : Fin pieces → Fin 6 → Fin coordinates → Bounds)
    (row : Fin coordinates) : Option Bounds :=
  sumTerms bits fun piece => dot bits (fun localRow => projection piece localRow row) (load piece)

/-- Source point actions are evaluated individually at their owned cut. The
    caller supplies all original load indices; affine entries contribute zero. -/
def pointActionEntry {loads coordinates : Nat} (bits : Nat)
    (actions : Fin loads → Fin 3 → Bounds)
    (projection : Fin loads → Fin 3 → Fin coordinates → Bounds)
    (row : Fin coordinates) : Option Bounds :=
  sumTerms bits fun load => dot bits (fun component => projection load component row) (actions load)

def forceEntry {pieces loads coordinates : Nat} (bits : Nat)
    (distributed : Fin pieces → Fin 6 → Bounds)
    (pieceProjection : Fin pieces → Fin 6 → Fin coordinates → Bounds)
    (actions : Fin loads → Fin 3 → Bounds)
    (actionProjection : Fin loads → Fin 3 → Fin coordinates → Bounds)
    (row : Fin coordinates) : Option Bounds := do
  let pieceWork ← distributedEntry bits distributed pieceProjection row
  let pointWork ← pointActionEntry bits actions actionProjection row
  add bits pieceWork pointWork

end FrameIntervalAssembly
