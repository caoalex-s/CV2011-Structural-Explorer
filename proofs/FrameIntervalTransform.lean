import FrameIntervalOps
import Mathlib.Data.Fin.VecNotation

/-! Apply one source member orientation to both endpoint displacement triples.
    The minus sign is attached to sine in transverse local displacement. -/
namespace FrameIntervalTransform
open FrameIntervalOps

def localPoint (bits : Nat) (cosine sine : Bounds) (global : Fin 3 → Bounds) :
    Option (Fin 3 → Bounds) := do
  let cx ← multiply bits cosine (global 0)
  let sy ← multiply bits sine (global 1)
  let sx ← multiply bits sine (global 0)
  let cy ← multiply bits cosine (global 1)
  let axial ← add bits cx sy
  let transverse ← subtract bits cy sx
  some ![axial, transverse, global 2]

def localPiece (bits : Nat) (cosine sine : Bounds) (start finish : Fin 3 → Bounds) :
    Option (Fin 6 → Bounds) := do
  let first ← localPoint bits cosine sine start
  let second ← localPoint bits cosine sine finish
  some ![first 0, first 1, first 2, second 0, second 1, second 2]

end FrameIntervalTransform
