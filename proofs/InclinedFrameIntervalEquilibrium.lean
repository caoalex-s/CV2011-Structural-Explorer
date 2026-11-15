import InclinedFrameIntervalAssemblySound

/-! Reindex the checked flat solution through the source column bijection.
    Neither an omitted coordinate nor a producer permutation enters this map.
    Physical uniqueness quantifies over all original-support admissible motions. -/
namespace InclinedFrameIntervalEquilibrium
open InclinedFrameSource InclinedFrameBasis InclinedFrameGlobalBasis
open InclinedFrameIntervalAssembly FrameEnclosure
noncomputable section

def liftCoordinates {data : Partition} {basis : GlobalBasis} (h : GlobalBasisValid data basis)
    (values : Fin basis.columns.size → ℝ) : Coordinates data basis :=
  fun index => values ((columnEquivalence h).symm index)

theorem lift_at_column {data : Partition} {basis : GlobalBasis} (h : GlobalBasisValid data basis)
    (values : Fin basis.columns.size → ℝ) (column : Fin basis.columns.size) :
    liftCoordinates h values (columnIndex h column) = values column :=
  congrArg values ((columnEquivalence h).symm_apply_apply column)

theorem lift_flatten {data : Partition} {basis : GlobalBasis} (h : GlobalBasisValid data basis)
    (values : Coordinates data basis) :
    liftCoordinates h (fun column => values (columnIndex h column)) = values := by
  funext index
  exact congrArg values ((columnEquivalence h).apply_symm_apply index)

theorem action_flatten {data : Partition} {basis : GlobalBasis} (h : GlobalBasisValid data basis)
    (values : Coordinates data basis) (row : Fin basis.columns.size) :
    FrameMatrixResidual.action
      (fun i j => InclinedFrameReduced.matrix data basis (columnIndex h i) (columnIndex h j))
      (fun column => values (columnIndex h column)) row =
      FrameMatrixResidual.action (InclinedFrameReduced.matrix data basis) values (columnIndex h row) :=
  (columnEquivalence h).sum_comp
    (fun index => InclinedFrameReduced.matrix data basis (columnIndex h row) index * values index)

theorem flat_equilibrium {data : Partition} {basis : GlobalBasis} (hpartition : PartitionValid data)
    (h : GlobalBasisValid data basis) (values : Fin basis.columns.size → ℝ) :
    FrameMatrixResidual.action
      (fun i j => InclinedFrameReduced.matrix data basis (columnIndex h i) (columnIndex h j)) values =
      (fun row => InclinedFrameReduced.force data basis (columnIndex h row)) ↔
      InclinedFrameReduced.Equilibrium data (embed data basis (liftCoordinates h values)) := by
  rw [← InclinedFrameReduced.reduced_equilibrium data basis hpartition h]
  constructor
  · intro hflat
    funext index
    obtain ⟨row, rfl⟩ := columnIndex_surjective h index
    have hrow := action_flatten h (liftCoordinates h values) row
    simpa only [lift_at_column, hflat] using hrow.symm
  · intro hsource
    funext row
    have hrow := action_flatten h (liftCoordinates h values) row
    simpa only [lift_at_column, hsource] using hrow

theorem check_physical_equilibrium {bits : Nat} {data : Partition} {basis : GlobalBasis}
    {certificate : Certificate data basis} (hcheck : check bits certificate = true) :
    ∃ h : GlobalBasisValid data basis, ∃ values : Fin basis.columns.size → ℝ,
      InclinedFrameReduced.Equilibrium data (embed data basis (liftCoordinates h values)) ∧
      (∀ other, InclinedFrameReduced.Equilibrium data other →
        other = embed data basis (liftCoordinates h values)) ∧
      ∀ column, Contains (certificate.solve.solution column)
        (liftCoordinates h values (columnIndex h column)) := by
  have hchecks : Checks bits certificate := of_decide_eq_true hcheck
  have hpartition := hchecks.1
  obtain ⟨hbasis, values, hsolution, hbounds, hunique⟩ :=
    InclinedFrameIntervalAssemblySound.check_reduced_solution hcheck
  refine ⟨hbasis, values, (flat_equilibrium hpartition hbasis values).mp hsolution, ?_, ?_⟩
  · intro other hequilibrium
    obtain ⟨coordinates, hcoordinates⟩ :=
      (range_equals_source_kernel hpartition hbasis other).mp hequilibrium.1
    have hother : InclinedFrameReduced.Equilibrium data
        (embed data basis (liftCoordinates hbasis (fun column => coordinates (columnIndex hbasis column)))) := by
      simpa only [lift_flatten, hcoordinates] using hequilibrium
    have hflat := hunique (fun column => coordinates (columnIndex hbasis column))
      ((flat_equilibrium hpartition hbasis _).mpr hother)
    rw [← hcoordinates, ← lift_flatten hbasis coordinates, hflat]
  · intro column
    simpa only [lift_at_column] using hbounds column

/-- Stability uses the original source's symmetric PSD stiffness, in addition
    to checked uniqueness. No stability conclusion follows from an inverse
    proposal or an unconstrained algebraic matrix alone. -/
theorem check_positive_stiffness {bits : Nat} {data : Partition} {basis : GlobalBasis}
    {certificate : Certificate data basis} (hcheck : check bits certificate = true)
    (motion : InclinedFrameReal.Motion data) (hadmissible : SourceAllows data motion)
    (hnonzero : motion ≠ 0) : 0 < InclinedFrameReal.stiffnessWork data motion motion := by
  have hchecks : Checks bits certificate := of_decide_eq_true hcheck
  have hpartition := hchecks.1
  obtain ⟨hbasis, flatValues, hequilibrium, hunique, _⟩ := check_physical_equilibrium hcheck
  let solution := liftCoordinates hbasis flatValues
  have hnondegenerate : ∀ coordinates : Coordinates data basis,
      (∀ variation, InclinedFrameReduced.form data basis coordinates variation = 0) → coordinates = 0 := by
    intro coordinates hnull
    have hperturbed : InclinedFrameReduced.Equilibrium data (embed data basis (solution+coordinates)) := by
      constructor
      · exact (range_equals_source_kernel hpartition hbasis _).mpr ⟨solution+coordinates, rfl⟩
      · intro variation hallowed
        obtain ⟨virtualCoordinates, rfl⟩ :=
          (range_equals_source_kernel hpartition hbasis variation).mp hallowed
        have hallowedVirtual : SourceAllows data (embed data basis virtualCoordinates) :=
          (range_equals_source_kernel hpartition hbasis _).mpr ⟨virtualCoordinates, rfl⟩
        have hwork := hequilibrium.2 _ hallowedVirtual
        change InclinedFrameReduced.form data basis solution virtualCoordinates =
          InclinedFrameReduced.load data basis virtualCoordinates at hwork
        change InclinedFrameReduced.form data basis (solution+coordinates) virtualCoordinates =
          InclinedFrameReduced.load data basis virtualCoordinates
        rw [map_add, LinearMap.add_apply, hnull, add_zero]
        exact hwork
    have hequal := embed_injective data basis (hunique _ hperturbed)
    exact add_left_cancel (show solution+coordinates = solution+0 by simpa only [add_zero] using hequal)
  have hpositive := FrameReducedStability.positive_of_psd_nondegenerate
    (InclinedFrameReduced.form data basis) (InclinedFrameReduced.form_symmetric data basis)
    (InclinedFrameReduced.form_nonnegative data basis hpartition) hnondegenerate
  obtain ⟨coordinates, hcoordinates⟩ :=
    (range_equals_source_kernel hpartition hbasis motion).mp hadmissible
  have hcoordinatesNonzero : coordinates ≠ 0 := by
    intro hzero
    apply hnonzero
    rw [← hcoordinates, hzero]
    exact (embedding data basis).map_zero
  have hresult := hpositive coordinates hcoordinatesNonzero
  change 0 < InclinedFrameReal.stiffnessWork data
    (embed data basis coordinates) (embed data basis coordinates) at hresult
  simpa only [hcoordinates] using hresult

end
end InclinedFrameIntervalEquilibrium
