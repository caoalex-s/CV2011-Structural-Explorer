import HingeFrameChecker
import InclinedFrameIntervalReport

/-! Each independently rotating end is represented by a coincident point.
    Its x and y columns are those of the original joint. Only its absolute
    rotation has a separate column. Supports and couples keep the source
    member and parameter, so their rotation follows the selected end. -/
namespace InclinedRelease
open RationalFrame InclinedFrameSource InclinedFrameBasis FrameIntervalOps
open InclinedFrameIntervalAssembly (Certificate)
open InclinedFrameIntervalBuild (Proposal tabulate maximum workScore)

structure Layout where
  original : Partition
  expanded : Partition
  sides : Array Nat
  parent : Array Nat
  basis : GlobalBasis

def endpoint (m : Member) (side : Nat) : Nat := if side % 2 == 0 then m.a else m.b

def layout (source : Source) (rules : HingeFrame.Connections) : Option Layout := do
  let original ← checkedPartition source
  guard (rules.joints.size == source.nodes.size && rules.ends.size == 2*source.members.size)
  guard (rules.joints.all (· ≤ 2) && rules.ends.all (· ≤ 2))
  let sides := (HingeFrame.releases source rules).toArray
  guard (!sides.isEmpty && original.points.size + sides.size ≤ 16)
  let mut members := source.members
  let mut nodes := source.nodes.map fun node => {node with reference := none}
  let mut parent := (List.range nodes.size).toArray
  for side in sides do
    let m := members[side/2]!
    let joint := endpoint source.members[side/2]! side
    let node := source.nodes[joint]!
    let index := nodes.size
    nodes := nodes.push {node with id := "~" ++ toString side, reference := none}
    members := members.set! (side/2) (if side % 2 == 0 then {m with a := index} else {m with b := index})
    parent := parent.push joint
  let expanded ← checkedPartition {source with nodes, members}
  let points := Array.ofFn fun i : Fin expanded.points.size =>
    let p := expanded.points[i.val]!
    let sourcePoint := if p.owner.isSome then locate original p.index p.t else parent[i.val]!
    let shared := rawBasis original sourcePoint
    let own := rawBasis expanded i.val
    let independent := p.owner.isNone && i.val ≥ source.nodes.size
    {shared with translation := if independent then 2 else shared.translation, rotationFree := own.rotationFree}
  let basis : GlobalBasis := ⟨points, allocatedColumns points⟩
  guard (basis.columns.size ≤ 48 && workScore expanded basis ≤ 2000000)
  return ⟨original, expanded, sides, Array.ofFn (fun i : Fin expanded.points.size => parent[i.val]?.getD i.val), basis⟩

/-- Use the same unit translation at all incident ends while preserving the
    separate rotational restraint at each end. -/
def pointColumn (l : Layout) (bits : Nat) (column : Fin l.basis.columns.size) (p : Nat) :
    Option (Fin 3 → Bounds) := do
  let shared ← InclinedFrameIntervalBasis.pointColumn bits l.expanded l.basis column l.parent[p]!
  let own ← InclinedFrameIntervalBasis.pointColumn bits l.expanded l.basis column p
  return fun d => if d.val == 2 then own d else shared d

def build (l : Layout) (bits : Nat)
    (proposal : Proposal l.expanded l.basis) : Option (Certificate l.expanded l.basis) := do
  let data := l.expanded
  let basis := l.basis
  if !precisionValid bits ||
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
        pointColumn l bits column point.val
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

end InclinedRelease
