import InclinedFrameSource

/-! Source-derived point basis classification with executable postconditions.
    Every support remains in the source-indexed predicates. No floating rank
    decision, angular tolerance or replacement support mask is accepted. -/
namespace InclinedFrameBasis
open RationalFrame InclinedFrameSource

structure AngleClass where
  angle : Rat
  turns : Int
  deriving Inhabited, Repr, DecidableEq

def canonical (angle : Rat) : AngleClass :=
  let turns := Rat.floor (angle/180)
  ⟨angle - 180*(turns : Rat), turns⟩

def ClassValid (source : Rat) (value : AngleClass) : Prop :=
  0 ≤ value.angle ∧ value.angle < 180 ∧ source = value.angle + 180*(value.turns : Rat)

instance (source : Rat) (value : AngleClass) : Decidable (ClassValid source value) := by
  unfold ClassValid
  infer_instance

structure PointBasis where
  /-- 0: independent x/y translations; 1: one tangent; 2: no translation. -/
  translation : Nat
  normal : Rat
  rotationFree : Bool
  deriving Inhabited, Repr, DecidableEq

def owned (data : Partition) (point : Nat) (support : Fin data.source.supports.size) : Prop :=
  let source := data.source.supports[support.val]!
  locate data source.member source.t = point

instance (data : Partition) (point : Nat) (support : Fin data.source.supports.size) :
    Decidable (owned data point support) := by unfold owned; infer_instance

/-- Original source indices, including all duplicate restraints at this point. -/
def supportsAt (data : Partition) (point : Nat) : List (Fin data.source.supports.size) :=
  (List.finRange data.source.supports.size).filter (fun i => decide (owned data point i))

def rawBasis (data : Partition) (point : Nat) : PointBasis :=
  let supports := supportsAt data point
  let fixed := supports.any (fun i => data.source.supports[i.val]!.kind == 1)
  let pinOrFixed := supports.any (fun i => data.source.supports[i.val]!.kind ≤ 1)
  let classes := ((supports.filter (fun i => data.source.supports[i.val]!.kind == 2)).map
    (fun i => (canonical data.source.supports[i.val]!.angle).angle)).eraseDups
  let translation := if pinOrFixed || classes.length ≥ 2 then 2 else if classes.isEmpty then 0 else 1
  { translation := translation, normal := classes.headD 0, rotationFree := !fixed }

/-- These finite checks certify the full support classification independently
    of the filtering/deduplication algorithm used to propose it. -/
def BasisValid (data : Partition) (point : Nat) (basis : PointBasis) : Prop :=
  point < data.points.size ∧
  (∀ i : Fin data.source.supports.size, owned data point i →
    data.source.supports[i.val]!.kind ≤ 2 ∧
    ClassValid data.source.supports[i.val]!.angle (canonical data.source.supports[i.val]!.angle)) ∧
  (basis.rotationFree = true ↔ ∀ i : Fin data.source.supports.size,
    owned data point i → data.source.supports[i.val]!.kind ≠ 1) ∧
  (match basis.translation with
  | 0 => ∀ i : Fin data.source.supports.size, ¬owned data point i
  | 1 => 0 ≤ basis.normal ∧ basis.normal < 180 ∧
      (∃ i : Fin data.source.supports.size, owned data point i) ∧
      (∀ i : Fin data.source.supports.size, owned data point i →
        data.source.supports[i.val]!.kind = 2 ∧
        (canonical data.source.supports[i.val]!.angle).angle = basis.normal)
  | 2 =>
      (∃ i : Fin data.source.supports.size, owned data point i ∧ data.source.supports[i.val]!.kind ≤ 1) ∨
      (∃ i j : Fin data.source.supports.size, owned data point i ∧ owned data point j ∧
        data.source.supports[i.val]!.kind = 2 ∧ data.source.supports[j.val]!.kind = 2 ∧
        (canonical data.source.supports[i.val]!.angle).angle ≠
          (canonical data.source.supports[j.val]!.angle).angle)
  | _ => False)

instance (data : Partition) (point : Nat) (basis : PointBasis) : Decidable (BasisValid data point basis) := by
  unfold BasisValid
  split <;> infer_instance

def checkedBasis (data : Partition) (point : Nat) : Option PointBasis :=
  let basis := rawBasis data point
  if BasisValid data point basis then some basis else none

theorem checkedBasis_valid {data : Partition} {point : Nat} {basis : PointBasis}
    (h : checkedBasis data point = some basis) : BasisValid data point basis := by
  unfold checkedBasis at h
  split at h
  next accepted =>
    have heq : rawBasis data point = basis := Option.some.inj h
    simpa [heq] using accepted
  · simp at h

/-- Column kinds are x translation, y translation, tangent translation and
    rotation, respectively. Point ownership is retained in every column. -/
structure Column where
  point : Nat
  kind : Nat
  deriving Inhabited, Repr, DecidableEq

def columnKinds (basis : PointBasis) : List Nat :=
  let translations := match basis.translation with
    | 0 => [0, 1]
    | 1 => [2]
    | _ => []
  translations ++ if basis.rotationFree then [3] else []

/-- Enumerate points in source-partition order, then their permitted local
    coordinates. No candidate-provided permutation or omitted point is used. -/
def allocatedColumns (points : Array PointBasis) : Array Column :=
  ((List.finRange points.size).flatMap fun point =>
    (columnKinds points[point.val]!).map fun kind => ⟨point.val, kind⟩).toArray

structure GlobalBasis where
  points : Array PointBasis
  columns : Array Column
  deriving Inhabited, Repr, DecidableEq

/-- Local slots 0/1/2 mean first translation, second translation and rotation.
    Slot 0 is tangent amplitude when the translation mode is one. -/
def Active (basis : PointBasis) (slot : Fin 3) : Prop :=
  if slot = 0 then basis.translation ≤ 1
  else if slot = 1 then basis.translation = 0
  else basis.rotationFree = true

instance (basis : PointBasis) (slot : Fin 3) : Decidable (Active basis slot) := by
  unfold Active
  infer_instance

def columnSlot (column : Column) : Fin 3 :=
  if column.kind = 1 then 1 else if column.kind = 3 then 2 else 0

/-- Explicit finite ownership, uniqueness and coverage checks make the array
    ordering a bijection with the independent source-coordinate index. -/
def AllocationValid (data : Partition) (basis : GlobalBasis) : Prop :=
  (∀ index : Fin basis.columns.size,
    basis.columns[index.val]!.point < data.points.size ∧
    Active basis.points[basis.columns[index.val]!.point]! (columnSlot basis.columns[index.val]!)) ∧
  (∀ first second : Fin basis.columns.size,
    basis.columns[first.val]!.point = basis.columns[second.val]!.point →
    columnSlot basis.columns[first.val]! = columnSlot basis.columns[second.val]! → first = second) ∧
  (∀ point : Fin data.points.size, ∀ slot : Fin 3, Active basis.points[point.val]! slot →
    ∃ index : Fin basis.columns.size,
      basis.columns[index.val]!.point = point.val ∧ columnSlot basis.columns[index.val]! = slot)

instance (data : Partition) (basis : GlobalBasis) : Decidable (AllocationValid data basis) := by
  unfold AllocationValid
  infer_instance

def rawGlobalBasis (data : Partition) : GlobalBasis :=
  let points := Array.ofFn fun point : Fin data.points.size => rawBasis data point.val
  ⟨points, allocatedColumns points⟩

/-- Check all source-owned local classifications before accepting their global
    allocation. The 48-coordinate cap matches the bounded reduced solver.
    Real range equality and column independence are separate proof obligations. -/
def GlobalBasisValid (data : Partition) (basis : GlobalBasis) : Prop :=
  basis.points.size = data.points.size ∧
  (∀ point : Fin data.points.size, BasisValid data point.val basis.points[point.val]!) ∧
  basis.columns = allocatedColumns basis.points ∧ basis.columns.size ≤ 48 ∧ AllocationValid data basis

instance (data : Partition) (basis : GlobalBasis) : Decidable (GlobalBasisValid data basis) := by
  unfold GlobalBasisValid
  infer_instance

def checkedGlobalBasis (data : Partition) : Option GlobalBasis :=
  let basis := rawGlobalBasis data
  if GlobalBasisValid data basis then some basis else none

theorem checkedGlobalBasis_valid {data : Partition} {basis : GlobalBasis}
    (h : checkedGlobalBasis data = some basis) : GlobalBasisValid data basis := by
  unfold checkedGlobalBasis at h
  dsimp only at h
  split at h
  next accepted =>
    have outputEquality : rawGlobalBasis data = basis := Option.some.inj h
    simpa only [outputEquality] using accepted
  · cases h

end InclinedFrameBasis
