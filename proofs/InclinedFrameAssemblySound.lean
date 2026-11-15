import FrameIntervalAssemblySound
import InclinedFrameReduced

/-! Bind interval assembly sums to the original physical reduced entries.
    The source evaluator must establish the local stiffness, load and projection
    enclosures supplied here; arbitrary producer tables are not accepted. -/
namespace InclinedFrameAssemblySound
open InclinedFrameSource InclinedFrameBasis InclinedFrameGlobalBasis InclinedFrameReal FrameEnclosure
noncomputable section

def sourceStiffness (data : Partition) (piece : Fin data.pieces.size) : Fin 6 → Fin 6 → ℝ :=
  let segment := data.pieces[piece.val]!
  let member := data.source.members[segment.member]!
  LocalFrameFields.stiffness (pieceLength data segment) member.EA member.EI

def sourceProjection (data : Partition) (basis : GlobalBasis) (h : GlobalBasisValid data basis)
    (piece : Fin data.pieces.size) (component : Fin 6) (column : Fin basis.columns.size) : ℝ :=
  pieceMotion data data.pieces[piece.val]!
    (embed data basis (InclinedFrameReduced.unit data basis (columnIndex h column))) component

def sourceAction (data : Partition) (index : Fin data.source.loads.size) : FrameTransform.Triple :=
  let action := data.source.loads[index.val]!
  if action.kind = 0 then ![(action.fx : ℝ), (action.fy : ℝ), 0]
  else if action.kind = 1 then ![0, 0, (action.mz : ℝ)] else 0

def sourceActionProjection (data : Partition) (basis : GlobalBasis) (h : GlobalBasisValid data basis)
    (index : Fin data.source.loads.size) (component : Fin 3) (column : Fin basis.columns.size) : ℝ :=
  let action := data.source.loads[index.val]!
  pointMotion data (embed data basis (InclinedFrameReduced.unit data basis (columnIndex h column)))
    (locate data action.member action.t) component

theorem source_matrix_assembly (data : Partition) (basis : GlobalBasis) (h : GlobalBasisValid data basis)
    (row column : Fin basis.columns.size) :
    InclinedFrameReduced.matrix data basis (columnIndex h row) (columnIndex h column) =
      ∑ piece, ∑ i, sourceProjection data basis h piece i row *
        (∑ j, sourceStiffness data piece i j * sourceProjection data basis h piece j column) := by
  change (∑ piece : Fin data.pieces.size, ∑ i : Fin 6, ∑ j : Fin 6,
    sourceProjection data basis h piece i row * sourceStiffness data piece i j *
      sourceProjection data basis h piece j column) = _
  simp only [Finset.mul_sum, mul_assoc]

theorem source_point_work (data : Partition) (basis : GlobalBasis) (h : GlobalBasisValid data basis)
    (index : Fin data.source.loads.size) (row : Fin basis.columns.size) :
    pointLoadWork data index (embed data basis (InclinedFrameReduced.unit data basis (columnIndex h row))) =
      ∑ component, sourceActionProjection data basis h index component row * sourceAction data index component := by
  unfold pointLoadWork sourceActionProjection sourceAction
  split_ifs <;> simp_all [Fin.sum_univ_succ] <;> ring

theorem source_force_assembly (data : Partition) (basis : GlobalBasis) (h : GlobalBasisValid data basis)
    (row : Fin basis.columns.size) :
    InclinedFrameReduced.force data basis (columnIndex h row) =
      (∑ piece : Fin data.pieces.size, ∑ component,
        sourceProjection data basis h piece component row * pieceLoad data data.pieces[piece.val]! component) +
      ∑ index, ∑ component,
        sourceActionProjection data basis h index component row * sourceAction data index component := by
  change externalWork data (embed data basis (InclinedFrameReduced.unit data basis (columnIndex h row))) = _
  unfold externalWork
  simp only [source_point_work]
  congr 1
  apply Finset.sum_congr rfl
  intro piece _
  apply Finset.sum_congr rfl
  intro component _
  exact mul_comm _ _

theorem checked_matrix_entry {data : Partition} {basis : GlobalBasis} (h : GlobalBasisValid data basis)
    {bits : Nat} {stiffness : Fin data.pieces.size → Fin 6 → Fin 6 → FrameIntervalOps.Bounds}
    {projection : Fin data.pieces.size → Fin 6 → Fin basis.columns.size → FrameIntervalOps.Bounds}
    {row column : Fin basis.columns.size} {out : FrameIntervalOps.Bounds}
    (hentry : FrameIntervalAssembly.matrixEntry bits stiffness projection row column = some out)
    (hstiffness : ∀ piece i j, Contains (stiffness piece i j) (sourceStiffness data piece i j))
    (hprojection : ∀ piece component coordinate, Contains (projection piece component coordinate)
      (sourceProjection data basis h piece component coordinate)) :
    Contains out (InclinedFrameReduced.matrix data basis (columnIndex h row) (columnIndex h column)) := by
  rw [source_matrix_assembly]
  exact FrameIntervalAssemblySound.matrixEntry_contains hentry hstiffness hprojection

theorem checked_force_entry {data : Partition} {basis : GlobalBasis} (h : GlobalBasisValid data basis)
    {bits : Nat} {distributed : Fin data.pieces.size → Fin 6 → FrameIntervalOps.Bounds}
    {pieceProjection : Fin data.pieces.size → Fin 6 → Fin basis.columns.size → FrameIntervalOps.Bounds}
    {actions : Fin data.source.loads.size → Fin 3 → FrameIntervalOps.Bounds}
    {actionProjection : Fin data.source.loads.size → Fin 3 → Fin basis.columns.size → FrameIntervalOps.Bounds}
    {row : Fin basis.columns.size} {out : FrameIntervalOps.Bounds}
    (hentry : FrameIntervalAssembly.forceEntry bits distributed pieceProjection actions actionProjection row = some out)
    (hdistributed : ∀ piece component, Contains (distributed piece component)
      (pieceLoad data data.pieces[piece.val]! component))
    (hpiece : ∀ piece component coordinate, Contains (pieceProjection piece component coordinate)
      (sourceProjection data basis h piece component coordinate))
    (hactions : ∀ index component, Contains (actions index component) (sourceAction data index component))
    (haction : ∀ index component coordinate, Contains (actionProjection index component coordinate)
      (sourceActionProjection data basis h index component coordinate)) :
    Contains out (InclinedFrameReduced.force data basis (columnIndex h row)) := by
  rw [source_force_assembly]
  exact FrameIntervalAssemblySound.forceEntry_contains hentry hdistributed hpiece hactions haction

end
end InclinedFrameAssemblySound
