import InclinedFrameBasis
import FrameIntervalTrig

/-! Enclose source-owned admissible unit columns. Rational amplitudes are
    Kronecker coordinates; only a roller tangent requires real trigonometry. -/
namespace InclinedFrameIntervalBasis
open InclinedFrameSource InclinedFrameBasis FrameIntervalOps

def pointAmplitude (data : Partition) (basis : GlobalBasis)
    (column : Fin basis.columns.size) (point : Nat) (slot : Fin 3) : Rat :=
  if point < data.points.size ∧ point = basis.columns[column.val]!.point ∧
      slot = columnSlot basis.columns[column.val]! ∧ Active basis.points[point]! slot then 1 else 0

/-- Slot amplitudes follow the same x/y-or-tangent/rotation convention as the
    real synthesis map. Canonical roller normals lie in [0,180), so no turn
    witness from the producer is needed here. -/
def synthesize (bits : Nat) (basis : PointBasis) (amplitudes : Fin 3 → Rat) :
    Option (Fin 3 → Bounds) := do
  let first ← point bits (amplitudes 0)
  let second ← point bits (amplitudes 1)
  let rotation ← point bits (amplitudes 2)
  if basis.translation = 0 then some (fun component => match component.val with
    | 0 => first | 1 => second | _ => rotation)
  else if basis.translation = 1 then
    let axes ← FrameIntervalTrig.degreeAxesGeneral bits basis.normal basis.normal 0
    let zero ← point bits 0
    let negativeSine ← subtract bits zero axes.sine
    let horizontal ← multiply bits negativeSine first
    let vertical ← multiply bits axes.cosine first
    some (fun component => match component.val with
      | 0 => horizontal | 1 => vertical | _ => rotation)
  else
    let zero ← point bits 0
    some (fun component => match component.val with
      | 0 => zero | 1 => zero | _ => rotation)

def pointColumn (bits : Nat) (data : Partition) (basis : GlobalBasis)
    (column : Fin basis.columns.size) (point : Nat) : Option (Fin 3 → Bounds) :=
  synthesize bits basis.points[point]! (pointAmplitude data basis column point)

end InclinedFrameIntervalBasis
