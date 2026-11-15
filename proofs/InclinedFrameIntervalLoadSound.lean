import InclinedFrameIntervalLoad
import InclinedFrameIntervalGeometrySound
import FrameIntervalLoadSound
import InclinedFrameAssemblySound

/-! Original-source load containment for each physical piece and point action.
    Source ownership and affine restriction are checked by PartitionValid. -/
namespace InclinedFrameIntervalLoadSound
open InclinedFrameSource InclinedFrameIntervalGeometry FrameEnclosure
noncomputable section

theorem pieceLoad_contains {bits : Nat} {data : Partition} {segment : Piece}
    {root : FrameIntervalOps.Bounds} {geometry : PieceBounds}
    {out : Fin 6 → FrameIntervalOps.Bounds}
    (hgeometry : piece bits data segment root = some geometry)
    (hload : InclinedFrameIntervalLoad.pieceLoad bits segment geometry = some out) :
    ∀ i, Contains (out i) (InclinedFrameReal.pieceLoad data segment i) := by
  obtain ⟨hL, hc, hs, _⟩ := InclinedFrameIntervalGeometrySound.piece_contains hgeometry
  simp only [InclinedFrameIntervalLoad.pieceLoad, Option.bind_eq_bind, Option.bind_eq_some] at hload
  obtain ⟨left, hl, right, hr, axialLeft, hal, axialRight, har,
    transverseLeft, htl, transverseRight, htr, hout⟩ := hload
  have hleft := executable_point_contains hl
  have hright := executable_point_contains hr
  exact FrameIntervalLoadSound.consistentLoad_contains hout hL
    (executable_multiply_contains hal hs hleft)
    (executable_multiply_contains har hs hright)
    (executable_multiply_contains htl hc hleft)
    (executable_multiply_contains htr hc hright)

theorem pointAction_contains {bits : Nat} {data : Partition}
    {index : Fin data.source.loads.size} {component : Fin 3} {out : FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalLoad.pointAction bits data index component = some out) :
    Contains out (InclinedFrameAssemblySound.sourceAction data index component) := by
  unfold InclinedFrameIntervalLoad.pointAction at h
  have hpoint := executable_point_contains h
  unfold InclinedFrameAssemblySound.sourceAction
  split_ifs <;> fin_cases component <;> simpa [*] using hpoint

end
end InclinedFrameIntervalLoadSound
