import InclinedFrameIntervalRecovery

/-! Grouped nodal reactions are assembled residuals against global unit
    motions. Duplicate supports share one point reaction; no arbitrary split
    into individual restraint forces is introduced. -/
namespace InclinedFrameIntervalReactions
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly FrameIntervalOps

def virtualPoint {data : Partition} (point : Fin data.points.size) (direction : Fin 3)
    (endpoint : Nat) : Fin 3 → Bounds := fun component =>
  let value : Rat := if endpoint = point.val ∧ component = direction then 1 else 0
  ⟨value, value⟩

def pieceWork {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (point : Fin data.points.size) (direction : Fin 3) (index : Fin data.pieces.size) : Option Bounds := do
  let segment := data.pieces[index.val]!
  let geometry := certificate.geometry index
  let motion ← InclinedFrameIntervalRecovery.localMotion bits certificate index
  let axialStart ← InclinedFrameIntervalRecovery.endAction bits certificate index motion 0
  let shearStart ← InclinedFrameIntervalRecovery.endAction bits certificate index motion 1
  let momentStart ← InclinedFrameIntervalRecovery.endAction bits certificate index motion 2
  let axialEnd ← InclinedFrameIntervalRecovery.endAction bits certificate index motion 3
  let shearEnd ← InclinedFrameIntervalRecovery.endAction bits certificate index motion 4
  let momentEnd ← InclinedFrameIntervalRecovery.endAction bits certificate index motion 5
  let variation ← FrameIntervalTransform.localPiece bits geometry.cosine geometry.sine
    (virtualPoint point direction segment.a) (virtualPoint point direction segment.b)
  FrameIntervalVector.dot bits variation ![axialStart, shearStart, momentStart, axialEnd, shearEnd, momentEnd]

def appliedAction {data : Partition} {basis : GlobalBasis} (certificate : Certificate data basis)
    (point : Fin data.points.size) (direction : Fin 3) (index : Fin data.source.loads.size) : Bounds :=
  let action := data.source.loads[index.val]!
  if locate data action.member action.t = point.val then certificate.actions index direction else ⟨0, 0⟩

def reaction {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (point : Fin data.points.size) (direction : Fin 3) : Option Bounds := do
  let elementWork ← FrameIntervalAssembly.sumTerms bits (pieceWork bits certificate point direction)
  let externalWork ← FrameIntervalAssembly.sumTerms bits
    (fun index => some (appliedAction certificate point direction index))
  subtract bits elementWork externalWork

end InclinedFrameIntervalReactions
