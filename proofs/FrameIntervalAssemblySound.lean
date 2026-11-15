import FrameIntervalAssembly
import FrameIntervalVectorSound

/-! Finite assembly containment. Original-source projection, geometry and load
    correspondence are additional obligations of the source checker bridge. -/
namespace FrameIntervalAssemblySound
open FrameIntervalAssembly FrameEnclosure
noncomputable section

theorem sumTerms_contains {bits size : Nat} {terms : Fin size → Option FrameIntervalOps.Bounds}
    {values : Fin size → ℝ} {out : FrameIntervalOps.Bounds}
    (h : sumTerms bits terms = some out)
    (hterms : ∀ index bounds, terms index = some bounds → Contains bounds (values index)) :
    Contains out (∑ index, values index) := by
  induction size generalizing out with
  | zero => simpa using executable_point_contains h
  | succ size ih =>
    obtain ⟨head, hhead, tail, htail, hadd⟩ := by
      simpa only [sumTerms, Option.bind_eq_bind, Option.bind_eq_some] using h
    have htailContains := ih htail (fun index => hterms index.succ)
    have hsum := executable_add_contains hadd (hterms 0 head hhead) htailContains
    simpa [Fin.sum_univ_succ] using hsum

theorem elementEntry_contains {bits : Nat}
    {stiffness : Fin 6 → Fin 6 → FrameIntervalOps.Bounds}
    {rowProjection columnProjection : Fin 6 → FrameIntervalOps.Bounds}
    {actual : Fin 6 → Fin 6 → ℝ} {actualRow actualColumn : Fin 6 → ℝ}
    {out : FrameIntervalOps.Bounds}
    (h : elementEntry bits stiffness rowProjection columnProjection = some out)
    (hstiffness : ∀ i j, Contains (stiffness i j) (actual i j))
    (hrow : ∀ i, Contains (rowProjection i) (actualRow i))
    (hcolumn : ∀ i, Contains (columnProjection i) (actualColumn i)) :
    Contains out (∑ i, actualRow i * (∑ j, actual i j * actualColumn j)) := by
  apply sumTerms_contains h
  intro row bounds hterm
  obtain ⟨action, haction, hmultiply⟩ := Option.bind_eq_some.mp hterm
  have hactionContains := FrameIntervalVectorSound.dot_contains haction (hstiffness row) hcolumn
  exact executable_multiply_contains hmultiply (hrow row) hactionContains

theorem matrixEntry_contains {bits pieces coordinates : Nat}
    {stiffness : Fin pieces → Fin 6 → Fin 6 → FrameIntervalOps.Bounds}
    {projection : Fin pieces → Fin 6 → Fin coordinates → FrameIntervalOps.Bounds}
    {actual : Fin pieces → Fin 6 → Fin 6 → ℝ}
    {actualProjection : Fin pieces → Fin 6 → Fin coordinates → ℝ}
    {row column : Fin coordinates} {out : FrameIntervalOps.Bounds}
    (h : matrixEntry bits stiffness projection row column = some out)
    (hstiffness : ∀ piece i j, Contains (stiffness piece i j) (actual piece i j))
    (hprojection : ∀ piece i coordinate, Contains (projection piece i coordinate)
      (actualProjection piece i coordinate)) :
    Contains out (∑ piece, ∑ i,
      actualProjection piece i row * (∑ j, actual piece i j * actualProjection piece j column)) := by
  apply sumTerms_contains h
  intro piece bounds hterm
  exact elementEntry_contains hterm (hstiffness piece)
    (fun i => hprojection piece i row) (fun i => hprojection piece i column)

theorem forceEntry_contains {bits pieces loads coordinates : Nat}
    {distributed : Fin pieces → Fin 6 → FrameIntervalOps.Bounds}
    {pieceProjection : Fin pieces → Fin 6 → Fin coordinates → FrameIntervalOps.Bounds}
    {actions : Fin loads → Fin 3 → FrameIntervalOps.Bounds}
    {actionProjection : Fin loads → Fin 3 → Fin coordinates → FrameIntervalOps.Bounds}
    {actualDistributed : Fin pieces → Fin 6 → ℝ}
    {actualPieceProjection : Fin pieces → Fin 6 → Fin coordinates → ℝ}
    {actualActions : Fin loads → Fin 3 → ℝ}
    {actualActionProjection : Fin loads → Fin 3 → Fin coordinates → ℝ}
    {row : Fin coordinates} {out : FrameIntervalOps.Bounds}
    (h : forceEntry bits distributed pieceProjection actions actionProjection row = some out)
    (hdistributed : ∀ piece i, Contains (distributed piece i) (actualDistributed piece i))
    (hpiece : ∀ piece i coordinate, Contains (pieceProjection piece i coordinate)
      (actualPieceProjection piece i coordinate))
    (hactions : ∀ load i, Contains (actions load i) (actualActions load i))
    (haction : ∀ load i coordinate, Contains (actionProjection load i coordinate)
      (actualActionProjection load i coordinate)) :
    Contains out ((∑ piece, ∑ i, actualPieceProjection piece i row * actualDistributed piece i) +
      ∑ load, ∑ i, actualActionProjection load i row * actualActions load i) := by
  simp only [forceEntry, Option.bind_eq_bind, Option.bind_eq_some] at h
  obtain ⟨pieceWork, hpieceWork, pointWork, hpointWork, hadd⟩ := h
  apply executable_add_contains hadd
  · apply sumTerms_contains hpieceWork
    intro piece bounds hterm
    exact FrameIntervalVectorSound.dot_contains hterm (fun i => hpiece piece i row) (hdistributed piece)
  · apply sumTerms_contains hpointWork
    intro load bounds hterm
    exact FrameIntervalVectorSound.dot_contains hterm (fun i => haction load i row) (hactions load)

end
end FrameIntervalAssemblySound
