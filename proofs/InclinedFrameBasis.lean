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

end InclinedFrameBasis
