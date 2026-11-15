import FrameIntervalOps

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
  some (fun component => match component.val with
    | 0 => axial | 1 => transverse | _ => global 2)

def localPiece (bits : Nat) (cosine sine : Bounds) (start finish : Fin 3 → Bounds) :
    Option (Fin 6 → Bounds) := do
  let first ← localPoint bits cosine sine start
  let second ← localPoint bits cosine sine finish
  some (fun component => match component.val with
    | 0 => first 0 | 1 => first 1 | 2 => first 2
    | 3 => second 0 | 4 => second 1 | _ => second 2)

end FrameIntervalTransform
