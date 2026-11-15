import InclinedFrameIntervalGeometry
import FrameIntervalLoad

/-! Source-derived loads for inclined interval assembly. Partition intensities
    are the exact restrictions of original affine loads; point actions retain
    their original index, both global force components and applied couple. -/
namespace InclinedFrameIntervalLoad
open InclinedFrameSource FrameIntervalOps InclinedFrameIntervalGeometry

def pieceLoad (bits : Nat) (segment : Piece) (geometry : PieceBounds) :
    Option (Fin 6 → Bounds) := do
  let left ← point bits segment.vertical
  let right ← point bits segment.verticalEnd
  let axialLeft ← multiply bits geometry.sine left
  let axialRight ← multiply bits geometry.sine right
  let transverseLeft ← multiply bits geometry.cosine left
  let transverseRight ← multiply bits geometry.cosine right
  FrameIntervalLoad.consistentLoad bits geometry.length axialLeft axialRight transverseLeft transverseRight

/-- Affine source records contribute through pieces, hence zero point action. -/
def pointAction (bits : Nat) (data : Partition) (index : Fin data.source.loads.size)
    (component : Fin 3) : Option Bounds :=
  let action := data.source.loads[index.val]!
  let value := if action.kind = 0 then
      if component = 0 then action.fx else if component = 1 then action.fy else 0
    else if action.kind = 1 then if component = 2 then action.mz else 0
    else 0
  point bits value

end InclinedFrameIntervalLoad
