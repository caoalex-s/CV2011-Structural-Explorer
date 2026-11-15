import InclinedFrameIntervalOutputs

/-! Reconstruct certificate tables in checker arithmetic order. The wire decoder
    supplies only bounded source data, root witnesses and solver proposals.
    Construction grants no status: the final result must pass `accepts`.
    The outer worker also enforces a deadline for the bounded computation. -/
namespace InclinedFrameIntervalBuild
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly FrameIntervalOps

/-- Evaluate each finite entry once, stopping at the first failed operation. -/
def tabulate {Value : Type} : (size : Nat) → (Fin size → Option Value) → Option (Fin size → Value)
  | 0, _ => some (fun index => Fin.elim0 index)
  | size+1, entry => do
    let first ← entry 0
    let rest ← tabulate size (fun index => entry index.succ)
    return Fin.cases first rest

def maximum : {size : Nat} → (Fin size → Rat) → Rat
  | 0, _ => 0
  | size+1, values => upperOf (values 0) (maximum (fun index : Fin size => values index.succ))

structure Proposal (data : Partition) (basis : GlobalBasis) where
  roots : Fin data.source.members.size → Bounds
  inverse : Fin basis.columns.size → Fin basis.columns.size → Rat
  estimate : Fin basis.columns.size → Rat

/-- Conservative work admission score, including reconstruction and the final
    recomputation checks. Terms cover trigonometric columns, element assembly,
    dense residuals, all reactions, all field expression trees and source loads.
    This is a resource gate, not a mathematical accuracy or stability test. -/
def workScore (data : Partition) (basis : GlobalBasis) : Nat :=
  let points := data.points.size
  let pieces := data.pieces.size
  let coordinates := basis.columns.size
  2 * (300*points*coordinates + 120*pieces*coordinates*coordinates +
    4*coordinates*coordinates*coordinates +
    3*points*pieces*(16*coordinates+200) + 6*(16*coordinates+500) +
    500*pieces + 100*data.source.loads.size*coordinates)

/-- Source and basis dimensions are checked before allocating any dense table.
    Wire rational-digit limits must additionally precede parsing these inputs. -/
def build {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (proposal : Proposal data basis) : Option (Certificate data basis) := do
  if !precisionValid bits || !decide (PartitionValid data ∧ GlobalBasisValid data basis) ||
      workScore data basis > 2000000 ||
      !decide (∀ member, valid (proposal.roots member) = true) ||
      !decide (∀ row column, bounded (proposal.inverse row column) = true) ||
      !decide (∀ row, bounded (proposal.estimate row) = true) then none else
    -- 1. Source geometry, admissible columns and original load contributions.
    let rootAt := fun member =>
      if h : member < data.source.members.size then proposal.roots ⟨member, h⟩ else ⟨0, 0⟩
    let geometry ← tabulate data.pieces.size fun index =>
      InclinedFrameIntervalGeometry.piece bits data data.pieces[index.val]!
        (rootAt data.pieces[index.val]!.member)
    let pointColumns ← tabulate data.points.size fun point =>
      tabulate basis.columns.size fun column =>
        InclinedFrameIntervalBasis.pointColumn bits data basis column point.val
    let pointAt := fun point column =>
      if h : point < data.points.size then pointColumns ⟨point, h⟩ column else fun _ => ⟨0, 0⟩
    let localColumns ← tabulate data.pieces.size fun index =>
      tabulate basis.columns.size fun column =>
        FrameIntervalTransform.localPiece bits (geometry index).cosine (geometry index).sine
          (pointAt data.pieces[index.val]!.a column) (pointAt data.pieces[index.val]!.b column)
    let distributed ← tabulate data.pieces.size fun index =>
      InclinedFrameIntervalLoad.pieceLoad bits data.pieces[index.val]! (geometry index)
    let actions ← tabulate data.source.loads.size fun index =>
      tabulate 3 fun component => InclinedFrameIntervalLoad.pointAction bits data index component

    -- 2. Reuse exactly the matrix and load arithmetic checked by assembly.
    let projection := fun piece component column => localColumns piece column component
    let stiffness := fun piece => FrameIntervalElement.entry (geometry piece).stiffness
    let actionProjection := fun (index : Fin data.source.loads.size) (component : Fin 3)
        (column : Fin basis.columns.size) =>
      let action := data.source.loads[index.val]!
      pointAt (locate data action.member action.t) column component
    let matrix ← tabulate basis.columns.size fun row =>
      tabulate basis.columns.size fun column =>
        FrameIntervalAssembly.matrixEntry bits stiffness projection row column
    let force ← tabulate basis.columns.size fun row =>
      FrameIntervalAssembly.forceEntry bits distributed projection actions actionProjection row

    -- 3. Derive conservative contraction/residual bounds from the proposal.
    let defect ← tabulate basis.columns.size fun row =>
      tabulate basis.columns.size fun column =>
        FrameIntervalSolve.defectEntry bits matrix proposal.inverse row column
    let residual ← tabulate basis.columns.size fun row =>
      FrameIntervalSolve.residualEntry bits matrix force proposal.estimate row
    let transformedResidual ← tabulate basis.columns.size fun row =>
      FrameIntervalSolve.transformedEntry bits proposal.inverse residual row
    let contraction := maximum fun row => FrameIntervalVector.magnitudeSum (defect row)
    let residualBound := maximum fun row => FrameIntervalVector.magnitude (transformedResidual row)
    if contraction < 0 || 1 ≤ contraction || residualBound < 0 then none else
      let radius := residualBound / (1-contraction)
      let solution ← tabulate basis.columns.size fun row =>
        outward bits (proposal.estimate row-radius) (proposal.estimate row+radius)
      return {
        roots := proposal.roots, geometry := geometry, pointColumns := pointColumns,
        localColumns := localColumns, distributed := distributed, actions := actions,
        matrix := matrix, force := force,
        solve := {
          inverse := proposal.inverse, estimate := proposal.estimate, defect := defect,
          residual := residual, transformedResidual := transformedResidual,
          contraction := contraction, residualBound := residualBound, solution := solution } }

/-- Return all six fields and every grouped reaction only after the existing
    source, solve and accuracy checks accept this same reconstructed certificate. -/
def checked {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (proposal : Proposal data basis) (query : RationalFrame.Query) :
    Option (InclinedFrameIntervalOutputs.Outputs data) := do
  let certificate ← build bits proposal
  let fields ← tabulate 6 fun component =>
    InclinedFrameIntervalRecovery.field bits certificate query component
  let reactions ← tabulate data.points.size fun point =>
    tabulate 3 fun direction => InclinedFrameIntervalReactions.reaction bits certificate point direction
  let outputs : InclinedFrameIntervalOutputs.Outputs data := ⟨fields, reactions⟩
  if InclinedFrameIntervalOutputs.accepts bits certificate query outputs then some outputs else none

end InclinedFrameIntervalBuild
