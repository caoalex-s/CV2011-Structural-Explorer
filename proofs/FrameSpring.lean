import InclinedReleaseWire

namespace FrameSpring
open InclinedRelease InclinedFrameSource InclinedFrameBasis FrameIntervalOps RationalFrame
open InclinedFrameIntervalAssembly
open InclinedFrameIntervalBuild (Proposal tabulate maximum workScore)

/-- Joint presets and explicit member-end overrides are preserved separately in
the packet. Each reference is recovered from the original member incidence. -/
structure Rules where
  joints : Array Nat
  ends : Array Nat
  stiffnesses : Array Rat

def resolve (source : Source) (rules : Rules) : Option (Layout × Array Rat) := do
  let n := 2 * source.members.size
  guard (rules.joints.size == source.nodes.size && rules.ends.size == n && rules.stiffnesses.size == n)
  let mut ends := #[]
  let mut stiffnesses := #[]
  for side in [:n] do
    let member := side / 2
    let node := endpoint source.members[member]! side
    let joint := rules.joints[node]!
    let tag := rules.ends[side]!
    let explicitK := rules.stiffnesses[side]!
    let presetK := source.nodes[node]!.rotationStiffness
    guard (joint ≤ 3 && tag ≤ 3 && (if tag == 3 then explicitK > 0 else explicitK == 0))
    guard (joint != 3 || presetK > 0)
    let reference := HingeFrame.reference source node
    let rule := if member == reference then 1 else if tag != 0 then tag
      else if joint == 3 then 3 else if joint == 1 then 2 else 1
    let k := if rule != 3 then 0 else if tag == 3 then explicitK else presetK
    ends := ends.push (if rule ≥ 2 then 2 else 1)
    stiffnesses := stiffnesses.push k
  guard (stiffnesses.any (· > 0))
  let l ← layout source ⟨Array.replicate source.nodes.size 0, ends⟩
  return (l, stiffnesses)

/-- Relative rotation of the spring-attached face for one reduced unit column. -/
def relativeColumn (l : Layout) (side : Nat) (col : Fin l.basis.columns.size) : Rat :=
  let rotation := fun point => InclinedFrameIntervalBasis.pointAmplitude l.expanded l.basis col point 2
  rotation (Wire.facePoint l side) - rotation (Wire.faceNode l side)

/-- The Hessian of the physical rotational spring energy contributes k bᵀb.
Fixed rotations have zero amplitude. No penalty stiffness is introduced. -/
def coupling (l : Layout) (ks : Array Rat) (r c : Fin l.basis.columns.size) : Rat :=
  ∑ i : Fin l.sides.size,
    let side := l.sides[i.val]!
    ks[side]! * relativeColumn l side r * relativeColumn l side c

def stiffenedEntry (bits : Nat) (k : Rat) (beam : Option Bounds) : Option Bounds := do
  let value ← beam
  add bits value ⟨k, k⟩

def build (l : Layout) (stiffnesses : Array Rat) (bits : Nat)
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
        stiffenedEntry bits (coupling l stiffnesses row column)
          (FrameIntervalAssembly.matrixEntry bits stiffness projection row column)
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


def Assembly (l : Layout) (ks : Array Rat) (bits : Nat) (c : Wire.Cert l) : Prop :=
  (∀ row col, stiffenedEntry bits (coupling l ks row col)
    (FrameIntervalAssembly.matrixEntry bits (localStiffness c)
       (fun piece component coordinate => c.localColumns piece coordinate component) row col) = some (c.matrix row col)) ∧
  (∀ row, FrameIntervalAssembly.forceEntry bits c.distributed
    (fun piece component coordinate => c.localColumns piece coordinate component)
    c.actions (actionProjection c) row = some (c.force row))

instance (l : Layout) (ks : Array Rat) (bits : Nat) (c : Wire.Cert l) : Decidable (Assembly l ks bits c) := by
  unfold Assembly
  infer_instance

def verified (l : Layout) (ks : Array Rat) (bits : Nat) (c : Wire.Cert l) : Bool :=
  decide (GeometryChecks bits c ∧ Projections l bits c ∧ LoadChecks bits c ∧ Assembly l ks bits c) &&
    FrameIntervalSolve.check bits c.matrix c.force c.solve

end FrameSpring
