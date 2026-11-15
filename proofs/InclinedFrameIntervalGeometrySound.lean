import InclinedFrameIntervalGeometry
import FrameIntervalGeometrySound
import FrameIntervalElementSound
import InclinedFrameReal

/-! Containment of the source geometry and physical element stiffness.
    This is one input bridge for assembly, not full checker acceptance. -/
namespace InclinedFrameIntervalGeometrySound
open InclinedFrameSource InclinedFrameIntervalGeometry InclinedFrameReal FrameEnclosure
noncomputable section

theorem member_contains {bits : Nat} {data : Partition} {index : Nat}
    {root : FrameIntervalOps.Bounds} {out : FrameIntervalGeometry.MemberBounds}
    (h : member bits data index root = some out) :
    Contains out.length (memberLength data index) ∧
    Contains out.cosine (memberDirection data index).cosine ∧
    Contains out.sine (memberDirection data index).sine := by
  unfold member at h
  simpa only [memberLength, memberDirection, endpoints] using
    FrameIntervalGeometrySound.original_endpoints h

theorem piece_contains {bits : Nat} {data : Partition} {segment : Piece}
    {root : FrameIntervalOps.Bounds} {out : PieceBounds}
    (h : piece bits data segment root = some out) :
    Contains out.length (pieceLength data segment) ∧
    Contains out.cosine (memberDirection data segment.member).cosine ∧
    Contains out.sine (memberDirection data segment.member).sine ∧
    (∀ i j : Fin 6, Contains (FrameIntervalElement.entry out.stiffness i j)
      (LocalFrameFields.stiffness (pieceLength data segment)
        data.source.members[segment.member]!.EA data.source.members[segment.member]!.EI i j)) := by
  simp only [piece, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
  obtain ⟨geometry, hgeometry, span, hspan, length, hlength, stiffness, hstiffness, hout⟩ := h
  subst out
  obtain ⟨hmemberLength, hcosine, hsine⟩ := member_contains hgeometry
  have hspanContains : Contains span ((segment.right : ℝ) - segment.left) := by
    simpa only [Rat.cast_sub] using executable_point_contains hspan
  have hpieceLength : Contains length (pieceLength data segment) :=
    executable_multiply_contains hlength hmemberLength hspanContains
  have hcoefficients := FrameIntervalElementSound.coefficients_contains hstiffness hpieceLength
  exact ⟨hpieceLength, hcosine, hsine, fun i j =>
    FrameIntervalElementSound.entry_contains hcoefficients i j⟩

end
end InclinedFrameIntervalGeometrySound
