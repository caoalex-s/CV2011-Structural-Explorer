import FrameIntervalSolve
import FrameIntervalVectorSound

/-! A successful executable residual check encloses the solution of the same
    real matrix and load contained by its inputs. Source assembly correspondence
    is supplied by the physical checker bridge, not by a certificate assertion. -/
namespace FrameIntervalSolveSound
open FrameIntervalSolve FrameEnclosure
noncomputable section

theorem singleton_contains (value : Rat) : Contains (singletonBounds value) (value : ℝ) :=
  ⟨le_rfl, le_rfl⟩

theorem defect_contains {size bits : Nat}
    {matrix : Fin size → Fin size → FrameIntervalOps.Bounds}
    {actual : Fin size → Fin size → ℝ} {inverse : Fin size → Fin size → Rat}
    {row column : Fin size} {out : FrameIntervalOps.Bounds}
    (h : defectEntry bits matrix inverse row column = some out)
    (hcontains : ∀ i j, Contains (matrix i j) (actual i j)) :
    Contains out (FrameMatrixResidual.defect actual (fun i j => (inverse i j : ℝ)) row column) := by
  simp only [defectEntry, Option.bind_eq_bind, Option.bind_eq_some] at h
  obtain ⟨product, hproduct, hsubtract⟩ := h
  have hproductContains := FrameIntervalVectorSound.dot_contains hproduct
    (fun index => singleton_contains (inverse row index)) (fun index => hcontains index column)
  have hidentity : Contains (singletonBounds (if row = column then 1 else 0))
      (if row = column then (1 : ℝ) else 0) := by
    by_cases hequal : row = column
    · simpa [hequal] using singleton_contains (1 : Rat)
    · simpa [hequal] using singleton_contains (0 : Rat)
  exact executable_subtract_contains hsubtract hidentity hproductContains

theorem residual_contains {size bits : Nat}
    {matrix : Fin size → Fin size → FrameIntervalOps.Bounds} {force : Fin size → FrameIntervalOps.Bounds}
    {actual : Fin size → Fin size → ℝ} {actualForce : Fin size → ℝ} {estimate : Fin size → Rat}
    {row : Fin size} {out : FrameIntervalOps.Bounds}
    (h : residualEntry bits matrix force estimate row = some out)
    (hmatrix : ∀ i j, Contains (matrix i j) (actual i j))
    (hforce : ∀ i, Contains (force i) (actualForce i)) :
    Contains out (actualForce row - FrameMatrixResidual.action actual (fun i => (estimate i : ℝ)) row) := by
  simp only [residualEntry, Option.bind_eq_bind, Option.bind_eq_some] at h
  obtain ⟨product, hproduct, hsubtract⟩ := h
  have hproductContains := FrameIntervalVectorSound.dot_contains hproduct (hmatrix row)
    (fun index => singleton_contains (estimate index))
  exact executable_subtract_contains hsubtract (hforce row) hproductContains

theorem transformed_contains {size bits : Nat} {inverse : Fin size → Fin size → Rat}
    {residual : Fin size → FrameIntervalOps.Bounds} {actualResidual : Fin size → ℝ}
    {row : Fin size} {out : FrameIntervalOps.Bounds}
    (h : transformedEntry bits inverse residual row = some out)
    (hresidual : ∀ i, Contains (residual i) (actualResidual i)) :
    Contains out (FrameMatrixResidual.action (fun i j => (inverse i j : ℝ)) actualResidual row) :=
  FrameIntervalVectorSound.dot_contains h (fun index => singleton_contains (inverse row index)) hresidual

/-- The unique solution is enclosed even for an empty reduced coordinate set.
    This is a solve theorem; physical stability requires the separate PSD bridge. -/
theorem check_sound {size bits : Nat}
    {matrix : Fin size → Fin size → FrameIntervalOps.Bounds} {force : Fin size → FrameIntervalOps.Bounds}
    {actual : Fin size → Fin size → ℝ} {actualForce : Fin size → ℝ}
    {certificate : Certificate size} (hcheck : check bits matrix force certificate = true)
    (hmatrix : ∀ i j, Contains (matrix i j) (actual i j))
    (hforce : ∀ i, Contains (force i) (actualForce i)) :
    ∃ solution, FrameMatrixResidual.action actual solution = actualForce ∧
      (∀ i, Contains (certificate.solution i) (solution i)) ∧
      ∀ other, FrameMatrixResidual.action actual other = actualForce → other = solution := by
  have hchecks : Checks bits matrix force certificate := of_decide_eq_true hcheck
  rcases hchecks with ⟨hscalar, _, harithmetic, hnorm, houtput⟩
  have hdefect : ∀ i j, Contains (certificate.defect i j)
      (FrameMatrixResidual.defect actual (fun row column => (certificate.inverse row column : ℝ)) i j) :=
    fun i j => defect_contains (harithmetic.1 i j) hmatrix
  have hresidual : ∀ i, Contains (certificate.residual i)
      (actualForce i - FrameMatrixResidual.action actual (fun j => (certificate.estimate j : ℝ)) i) :=
    fun i => residual_contains (harithmetic.2.1 i) hmatrix hforce
  have htransformed : ∀ i, Contains (certificate.transformedResidual i)
      (FrameMatrixResidual.action (fun row column => (certificate.inverse row column : ℝ))
        (actualForce - FrameMatrixResidual.action actual (fun j => (certificate.estimate j : ℝ))) i) :=
    fun i => transformed_contains (harithmetic.2.2 i) hresidual
  have hrows := FrameIntervalVectorSound.checked_defect_rows hdefect hnorm.1
  have hresidualBound : ∀ i,
      |FrameMatrixResidual.action (fun row column => (certificate.inverse row column : ℝ))
        (actualForce - FrameMatrixResidual.action actual (fun j => (certificate.estimate j : ℝ))) i| ≤
          (certificate.residualBound : ℝ) := by
    intro i
    exact le_trans (FrameIntervalVectorSound.magnitude_bound (htransformed i))
      (by exact_mod_cast hnorm.2 i)
  have hqzero : (0 : ℝ) ≤ certificate.contraction := by exact_mod_cast hscalar.2.2.1
  have hqone : (certificate.contraction : ℝ) < 1 := by exact_mod_cast hscalar.2.2.2.1
  have hetazero : (0 : ℝ) ≤ certificate.residualBound := by exact_mod_cast hscalar.2.2.2.2.1
  obtain ⟨solution, hsolution, _⟩ := FrameMatrixResidual.enclosed_solution actual
    (fun row column => (certificate.inverse row column : ℝ)) actualForce
    (fun i => (certificate.estimate i : ℝ)) certificate.contraction certificate.residualBound
    hqzero hqone hetazero hrows hresidualBound
  refine ⟨solution, hsolution.1, ?_, ?_⟩
  · intro i
    have hlower : ((certificate.solution i).lower : ℝ) ≤
        (certificate.estimate i : ℝ) - certificate.residualBound/(1-(certificate.contraction : ℝ)) := by
      exact_mod_cast (houtput i).2.1
    have hupper : (certificate.estimate i : ℝ) +
        certificate.residualBound/(1-(certificate.contraction : ℝ)) ≤
          ((certificate.solution i).upper : ℝ) := by exact_mod_cast (houtput i).2.2
    exact ⟨le_trans hlower (hsolution.2 i).1, le_trans (hsolution.2 i).2 hupper⟩
  · intro other hother
    have hinjective := FrameResidualBound.injective_of_defect (FrameMatrixResidual.action actual)
      (FrameMatrixResidual.action (fun row column => (certificate.inverse row column : ℝ)))
      (certificate.contraction : ℝ) hqone
      (FrameMatrixResidual.defect_norm_bound actual _ _ hqzero hrows)
    exact hinjective (hother.trans hsolution.1.symm)

end
end FrameIntervalSolveSound
