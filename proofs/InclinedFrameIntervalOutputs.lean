import InclinedFrameIntervalReactions
import FrameIntervalAccuracy

/-! Final field/reaction gates after checked source assembly and solution.
    Every returned component passes the fixed unit-aware accuracy policy.
    Packet decoding and original-source binding are separate outer boundaries. -/
namespace InclinedFrameIntervalOutputs
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly

structure Outputs (data : Partition) where
  fields : Fin 6 → FrameIntervalOps.Bounds
  reactions : Fin data.points.size → Fin 3 → FrameIntervalOps.Bounds

def fieldQuantity (component : Fin 6) : Fin 9 :=
  ⟨component.val, Nat.lt_of_lt_of_le component.isLt (by decide : 6 ≤ 9)⟩

def reactionQuantity (direction : Fin 3) : Fin 9 :=
  ⟨direction.val+6, Nat.add_lt_add_right direction.isLt 6⟩

def OutputChecks {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (certificate : Certificate data basis) (query : RationalFrame.Query) (outputs : Outputs data) : Prop :=
  (∀ component, InclinedFrameIntervalRecovery.field bits certificate query component = some (outputs.fields component) ∧
    FrameIntervalAccuracy.check (fieldQuantity component) (outputs.fields component) = true) ∧
  (∀ point direction, InclinedFrameIntervalReactions.reaction bits certificate point direction =
      some (outputs.reactions point direction) ∧
    FrameIntervalAccuracy.check (reactionQuantity direction) (outputs.reactions point direction) = true)

instance {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis)
    (query : RationalFrame.Query) (outputs : Outputs data) : Decidable (OutputChecks bits certificate query outputs) := by
  unfold OutputChecks
  infer_instance

/-- Rejection is inconclusive; only the successful source/solve/output path
    can grant checked status. No failed numerical certificate means mechanism. -/
def accepts {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (certificate : Certificate data basis) (query : RationalFrame.Query) (outputs : Outputs data) : Bool :=
  check bits certificate && decide (OutputChecks bits certificate query outputs)

end InclinedFrameIntervalOutputs
