import InclinedFrameIntervalBasis
import InclinedFrameIntervalLoad
import FrameIntervalTransform
import FrameIntervalAssembly
import FrameIntervalSolve

/-! Source assembly certificate checker. Stored intermediate tables are checked
    against source evaluation; they are not trusted geometry, stiffness or load
    inputs. The source decoder must enforce limits before allocating tables. -/
namespace InclinedFrameIntervalAssembly
open InclinedFrameSource InclinedFrameBasis FrameIntervalOps

/-- Compare every component of a finite vector. This constructive decision is
    used when recomputed vectors are compared with certificate tables. -/
private def finiteVectorEquality {size : Nat} {Value : Type} [DecidableEq Value]
    (left right : Fin size → Value) : Decidable (left = right) :=
  if equalComponents : ∀ index, left index = right index then
    isTrue (funext equalComponents)
  else
    isFalse (fun equality => equalComponents (fun index => congrFun equality index))

local instance {size : Nat} {Value : Type} [DecidableEq Value] :
    DecidableEq (Fin size → Value) := finiteVectorEquality

structure Certificate (data : Partition) (basis : GlobalBasis) where
  roots : Fin data.source.members.size → Bounds
  geometry : Fin data.pieces.size → InclinedFrameIntervalGeometry.PieceBounds
  pointColumns : Fin data.points.size → Fin basis.columns.size → Fin 3 → Bounds
  localColumns : Fin data.pieces.size → Fin basis.columns.size → Fin 6 → Bounds
  distributed : Fin data.pieces.size → Fin 6 → Bounds
  actions : Fin data.source.loads.size → Fin 3 → Bounds
  matrix : Fin basis.columns.size → Fin basis.columns.size → Bounds
  force : Fin basis.columns.size → Bounds
  solve : FrameIntervalSolve.Certificate basis.columns.size

/-- Total accessors agree with the physical model's zero extension. The checked
    partition separately ensures that every referenced endpoint is in range. -/
def rootAt {data : Partition} {basis : GlobalBasis} (certificate : Certificate data basis)
    (member : Nat) : Bounds :=
  if h : member < data.source.members.size then certificate.roots ⟨member, h⟩ else ⟨0, 0⟩

def pointColumnAt {data : Partition} {basis : GlobalBasis} (certificate : Certificate data basis)
    (point : Nat) (column : Fin basis.columns.size) : Fin 3 → Bounds :=
  if h : point < data.points.size then certificate.pointColumns ⟨point, h⟩ column else fun _ => ⟨0, 0⟩

def localStiffness {data : Partition} {basis : GlobalBasis} (certificate : Certificate data basis)
    (piece : Fin data.pieces.size) : Fin 6 → Fin 6 → Bounds :=
  FrameIntervalElement.entry (certificate.geometry piece).stiffness

def actionProjection {data : Partition} {basis : GlobalBasis} (certificate : Certificate data basis)
    (index : Fin data.source.loads.size) (component : Fin 3) (column : Fin basis.columns.size) : Bounds :=
  let action := data.source.loads[index.val]!
  pointColumnAt certificate (locate data action.member action.t) column component

def GeometryChecks {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (certificate : Certificate data basis) : Prop :=
  ∀ piece : Fin data.pieces.size,
    InclinedFrameIntervalGeometry.piece bits data data.pieces[piece.val]!
      (rootAt certificate data.pieces[piece.val]!.member) = some (certificate.geometry piece)

def ProjectionChecks {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (certificate : Certificate data basis) : Prop :=
  (∀ (point : Fin data.points.size) (column : Fin basis.columns.size),
      InclinedFrameIntervalBasis.pointColumn bits data basis column point.val =
      some (certificate.pointColumns point column)) ∧
  (∀ (piece : Fin data.pieces.size) (column : Fin basis.columns.size), FrameIntervalTransform.localPiece bits
      (certificate.geometry piece).cosine (certificate.geometry piece).sine
      (pointColumnAt certificate data.pieces[piece.val]!.a column)
      (pointColumnAt certificate data.pieces[piece.val]!.b column) = some (certificate.localColumns piece column))

def LoadChecks {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (certificate : Certificate data basis) : Prop :=
  (∀ piece : Fin data.pieces.size, InclinedFrameIntervalLoad.pieceLoad bits data.pieces[piece.val]! (certificate.geometry piece) =
      some (certificate.distributed piece)) ∧
  (∀ index component, InclinedFrameIntervalLoad.pointAction bits data index component =
      some (certificate.actions index component))

def AssemblyChecks {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (certificate : Certificate data basis) : Prop :=
  (∀ row column, FrameIntervalAssembly.matrixEntry bits (localStiffness certificate)
      (fun piece component coordinate => certificate.localColumns piece coordinate component)
      row column = some (certificate.matrix row column)) ∧
  (∀ row, FrameIntervalAssembly.forceEntry bits certificate.distributed
      (fun piece component coordinate => certificate.localColumns piece coordinate component)
      certificate.actions (actionProjection certificate) row = some (certificate.force row))

instance {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis) :
    Decidable (GeometryChecks bits certificate) := by unfold GeometryChecks; infer_instance
instance {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis) :
    Decidable (ProjectionChecks bits certificate) := by unfold ProjectionChecks; infer_instance
instance {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis) :
    Decidable (LoadChecks bits certificate) := by unfold LoadChecks; infer_instance
instance {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis) :
    Decidable (AssemblyChecks bits certificate) := by unfold AssemblyChecks; infer_instance

def Checks {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis) : Prop :=
  PartitionValid data ∧ GlobalBasisValid data basis ∧ GeometryChecks bits certificate ∧
  ProjectionChecks bits certificate ∧ LoadChecks bits certificate ∧ AssemblyChecks bits certificate ∧
  FrameIntervalSolve.check bits certificate.matrix certificate.force certificate.solve = true

instance {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis) :
    Decidable (Checks bits certificate) := by unfold Checks; infer_instance

def check {data : Partition} {basis : GlobalBasis} (bits : Nat) (certificate : Certificate data basis) : Bool :=
  decide (Checks bits certificate)

end InclinedFrameIntervalAssembly
