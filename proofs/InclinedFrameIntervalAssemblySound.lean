import InclinedFrameIntervalAssembly
import InclinedFrameIntervalBasisSound
import InclinedFrameIntervalLoadSound
import FrameIntervalTransformSound
import FrameIntervalSolveSound

/-! Source correspondence for every input to the checked reduced solve. The
    output is a solution of the original reduced entries, in checked column
    order. Physical equilibrium follows after the explicit index bijection. -/
namespace InclinedFrameIntervalAssemblySound
open InclinedFrameSource InclinedFrameBasis InclinedFrameGlobalBasis
open InclinedFrameIntervalAssembly InclinedFrameAssemblySound FrameEnclosure
noncomputable section

theorem pointColumnAt_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hbasis : GlobalBasisValid data basis) {certificate : Certificate data basis}
    (hprojection : ProjectionChecks bits certificate) (point : Nat) (column : Fin basis.columns.size) :
    ∀ i, Contains (pointColumnAt certificate point column i)
      (InclinedFrameReal.pointMotion data
        (embed data basis (InclinedFrameReduced.unit data basis (columnIndex hbasis column))) point i) := by
  unfold pointColumnAt InclinedFrameReal.pointMotion
  split
  next hin => exact InclinedFrameIntervalBasisSound.pointColumn_contains hbasis (hprojection.1 ⟨point, hin⟩ column)
  next hout => intro i; simp [Contains]

theorem localColumns_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hbasis : GlobalBasisValid data basis) {certificate : Certificate data basis}
    (hgeometry : GeometryChecks bits certificate) (hprojection : ProjectionChecks bits certificate)
    (piece : Fin data.pieces.size) (column : Fin basis.columns.size) :
    ∀ i, Contains (certificate.localColumns piece column i) (sourceProjection data basis hbasis piece i column) := by
  obtain ⟨_, hc, hs, _⟩ := InclinedFrameIntervalGeometrySound.piece_contains (hgeometry piece)
  exact FrameIntervalTransformSound.localPiece_contains (hprojection.2 piece column) hc hs
    (pointColumnAt_contains hbasis hprojection _ column)
    (pointColumnAt_contains hbasis hprojection _ column)

theorem matrix_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hbasis : GlobalBasisValid data basis) {certificate : Certificate data basis}
    (hgeometry : GeometryChecks bits certificate) (hprojection : ProjectionChecks bits certificate)
    (hassembly : AssemblyChecks bits certificate) :
    ∀ row column, Contains (certificate.matrix row column)
      (InclinedFrameReduced.matrix data basis (columnIndex hbasis row) (columnIndex hbasis column)) := by
  intro row column
  apply checked_matrix_entry hbasis (hassembly.1 row column)
  · intro piece i j
    exact (InclinedFrameIntervalGeometrySound.piece_contains (hgeometry piece)).2.2.2 i j
  · intro piece component coordinate
    exact localColumns_contains hbasis hgeometry hprojection piece coordinate component

theorem force_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hbasis : GlobalBasisValid data basis) {certificate : Certificate data basis}
    (hgeometry : GeometryChecks bits certificate) (hprojection : ProjectionChecks bits certificate)
    (hload : LoadChecks bits certificate) (hassembly : AssemblyChecks bits certificate) :
    ∀ row, Contains (certificate.force row) (InclinedFrameReduced.force data basis (columnIndex hbasis row)) := by
  intro row
  apply checked_force_entry hbasis (hassembly.2 row)
  · intro piece component
    exact InclinedFrameIntervalLoadSound.pieceLoad_contains (hgeometry piece) (hload.1 piece) component
  · intro piece component coordinate
    exact localColumns_contains hbasis hgeometry hprojection piece coordinate component
  · intro index component
    exact InclinedFrameIntervalLoadSound.pointAction_contains (hload.2 index component)
  · intro index component coordinate
    exact pointColumnAt_contains hbasis hprojection _ coordinate component

/-- Uniqueness applies to every reduced solution, not just candidates inside
    the displayed interval. This distinction is needed for physical uniqueness. -/
theorem check_reduced_solution {bits : Nat} {data : Partition} {basis : GlobalBasis}
    {certificate : Certificate data basis} (hcheck : check bits certificate = true) :
    ∃ hbasis : GlobalBasisValid data basis, ∃ solution : Fin basis.columns.size → ℝ,
      FrameMatrixResidual.action
        (fun row column => InclinedFrameReduced.matrix data basis (columnIndex hbasis row) (columnIndex hbasis column))
        solution = (fun row => InclinedFrameReduced.force data basis (columnIndex hbasis row)) ∧
      (∀ i, Contains (certificate.solve.solution i) (solution i)) ∧
      ∀ other, FrameMatrixResidual.action
        (fun row column => InclinedFrameReduced.matrix data basis (columnIndex hbasis row) (columnIndex hbasis column))
        other = (fun row => InclinedFrameReduced.force data basis (columnIndex hbasis row)) → other = solution := by
  have h : Checks bits certificate := of_decide_eq_true hcheck
  obtain ⟨_, hbasis, hgeometry, hprojection, hload, hassembly, hsolve⟩ := h
  exact ⟨hbasis, FrameIntervalSolveSound.check_sound hsolve
    (matrix_contains hbasis hgeometry hprojection hassembly)
    (force_contains hbasis hgeometry hprojection hload hassembly)⟩

end
end InclinedFrameIntervalAssemblySound
