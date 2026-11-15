import InclinedFrameSource
import FrameIntervalGeometry
import FrameIntervalElement

/-! Source-owned geometry and local stiffness evaluation. Only square-root
    brackets are proposed; endpoints, segment spans and rigidities are read
    from the checked source partition. Arithmetic failure is inconclusive. -/
namespace InclinedFrameIntervalGeometry
open InclinedFrameSource FrameIntervalOps

def member (bits : Nat) (data : Partition) (index : Nat) (root : Bounds) :
    Option FrameIntervalGeometry.MemberBounds :=
  let original := data.source.members[index]!
  let start := data.source.nodes[original.a]!
  let finish := data.source.nodes[original.b]!
  FrameIntervalGeometry.member bits (finish.x-start.x) (finish.y-start.y) root

structure PieceBounds where
  length : Bounds
  cosine : Bounds
  sine : Bounds
  stiffness : FrameIntervalElement.Coefficients
  deriving Inhabited, Repr, DecidableEq

/-- A cut changes the physical length, while retaining the original orientation.
    The partition validity gate separately establishes ordered, owned cuts. -/
def piece (bits : Nat) (data : Partition) (segment : Piece) (root : Bounds) :
    Option PieceBounds := do
  let original := data.source.members[segment.member]!
  let geometry ← member bits data segment.member root
  let span ← point bits (segment.right-segment.left)
  let length ← multiply bits geometry.length span
  let stiffness ← FrameIntervalElement.coefficients bits length original.EA original.EI
  some ⟨length, geometry.cosine, geometry.sine, stiffness⟩

end InclinedFrameIntervalGeometry
