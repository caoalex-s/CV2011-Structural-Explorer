import InclinedFrameBasisSound
import InclinedFrameReal

/-! Source-owned coordinates for the complete constrained motion space.
    Each coordinate belongs to one partition point. A free point has x/y slots,
    a single roller class has one tangent slot, and blocked translations have
    neither. Rotation is present exactly when no owned fixed restraint exists.
    The checked allocation supplies the finite bijection to executable columns. -/
namespace InclinedFrameGlobalBasis
open InclinedFrameSource InclinedFrameBasis InclinedFrameBasisSound FrameAdmissiblePoint
noncomputable section

abbrev LocalIndex (basis : PointBasis) := {slot : Fin 3 // Active basis slot}
abbrev LocalCoordinates (basis : PointBasis) := LocalIndex basis → ℝ

def amplitude (basis : PointBasis) (values : LocalCoordinates basis) (slot : Fin 3) : ℝ :=
  if h : Active basis slot then values ⟨slot, h⟩ else 0

/-- Embed independent amplitudes into global x/y/rotation components. -/
def synthesize (basis : PointBasis) (values : LocalCoordinates basis) : FrameTransform.Triple :=
  let first := amplitude basis values 0
  let second := amplitude basis values 1
  let rotation := amplitude basis values 2
  let cosine := ExactGeometry.degreeCos (basis.normal : ℝ)
  let sine := ExactGeometry.degreeSin (basis.normal : ℝ)
  ![if basis.translation = 0 then first else if basis.translation = 1 then -sine*first else 0,
    if basis.translation = 0 then second else if basis.translation = 1 then cosine*first else 0,
    rotation]

/-- Recover local amplitudes using the normalized source tangent. -/
def project (basis : PointBasis) (motion : FrameTransform.Triple) : LocalCoordinates basis :=
  fun coordinate =>
    if coordinate.val = 0 then
      if basis.translation = 0 then motion 0 else
        tangentCoordinate (ExactGeometry.degreeCos (basis.normal : ℝ))
          (ExactGeometry.degreeSin (basis.normal : ℝ)) (motion 0) (motion 1)
    else if coordinate.val = 1 then motion 1 else motion 2

private theorem recover_tangent (basis : PointBasis) (value : ℝ) :
    tangentCoordinate (ExactGeometry.degreeCos (basis.normal : ℝ))
      (ExactGeometry.degreeSin (basis.normal : ℝ))
      (-ExactGeometry.degreeSin (basis.normal : ℝ)*value)
      (ExactGeometry.degreeCos (basis.normal : ℝ)*value) = value := by
  unfold tangentCoordinate
  calc
    _ = ((ExactGeometry.degreeCos (basis.normal : ℝ))^2 +
      (ExactGeometry.degreeSin (basis.normal : ℝ))^2)*value := by ring
    _ = value := by rw [ExactGeometry.degree_axis_normalized]; ring

theorem project_synthesize (basis : PointBasis) (values : LocalCoordinates basis) :
    project basis (synthesize basis values) = values := by
  funext coordinate
  rcases coordinate with ⟨slot, active⟩
  fin_cases slot
  · have hmode : basis.translation = 0 ∨ basis.translation = 1 := by
      have hbound : basis.translation ≤ 1 := by simpa [Active] using active
      omega
    rcases hmode with hfree | htangent
    · simp [project, synthesize, amplitude, Active, hfree]
    · simp [project, synthesize, amplitude, Active, htangent, recover_tangent]
  · have hfree : basis.translation = 0 := by simpa [Active] using active
    simp [project, synthesize, amplitude, Active, hfree]
  · have hrotation : basis.rotationFree = true := by simpa [Active] using active
    simp [project, synthesize, amplitude, Active, hrotation]

theorem synthesize_injective (basis : PointBasis) : Function.Injective (synthesize basis) := by
  intro first second equalMotion
  have equalCoordinates := congrArg (project basis) equalMotion
  simpa only [project_synthesize] using equalCoordinates

private theorem valid_modes {data : Partition} {point : Nat} {basis : PointBasis}
    (h : BasisValid data point basis) :
    basis.translation = 0 ∨ basis.translation = 1 ∨ basis.translation = 2 := by
  have classification := h.2.2.2
  split at classification <;> omega

def PointAllows (data : Partition) (point : Nat) (motion : FrameTransform.Triple) : Prop :=
  TranslationAllows data point (motion 0) (motion 1) ∧ RotationAllows data point (motion 2)

theorem synthesize_allows {data : Partition} {point : Nat} {basis : PointBasis}
    (h : BasisValid data point basis) (values : LocalCoordinates basis) :
    PointAllows data point (synthesize basis values) := by
  constructor
  · rcases valid_modes h with hfree | htangent | hblocked
    · exact free_translation h hfree _ _
    · apply (tangent_translation h htangent _ _).mpr
      exact ⟨amplitude basis values 0, by simp [synthesize, htangent]⟩
    · apply (blocked_translation h hblocked _ _).mpr
      simp [synthesize, hblocked]
  · apply (rotation_kernel h _).mpr
    by_cases hrotation : basis.rotationFree = true
    · exact Or.inl hrotation
    · right
      simp [synthesize, amplitude, Active, hrotation]

theorem synthesize_project {data : Partition} {point : Nat} {basis : PointBasis}
    (h : BasisValid data point basis) (motion : FrameTransform.Triple)
    (hallows : PointAllows data point motion) :
    synthesize basis (project basis motion) = motion := by
  have hrotation : amplitude basis (project basis motion) 2 = motion 2 := by
    rcases (rotation_kernel h _).mp hallows.2 with hfree | hzero
    · simp [amplitude, Active, project, hfree]
    · by_cases hfree : basis.rotationFree = true
      · simp [amplitude, Active, project, hfree]
      · simp [amplitude, Active, hfree, hzero]
  rcases valid_modes h with hfree | htangent | hblocked
  · funext slot
    fin_cases slot
    · simp [synthesize, amplitude, Active, project, hfree]
    · simp [synthesize, amplitude, Active, project, hfree]
    · exact hrotation
  · obtain ⟨value, hx, hy⟩ := (tangent_translation h htangent _ _).mp hallows.1
    have ht : tangentCoordinate (ExactGeometry.degreeCos (basis.normal : ℝ))
        (ExactGeometry.degreeSin (basis.normal : ℝ)) (motion 0) (motion 1) = value := by
      rw [hx, hy]
      exact recover_tangent basis value
    have hfirst : amplitude basis (project basis motion) 0 = value := by
      simp [amplitude, Active, project, htangent, ht]
    funext slot
    fin_cases slot
    · simp [synthesize, htangent, hfirst, hx]
    · simp [synthesize, htangent, hfirst, hy]
    · exact hrotation
  · obtain ⟨hx, hy⟩ := (blocked_translation h hblocked _ _).mp hallows.1
    funext slot
    fin_cases slot
    · simp [synthesize, hblocked, hx]
    · simp [synthesize, hblocked, hy]
    · exact hrotation

/-- The global index explicitly pairs every independent local coordinate with
    its source-partition point; sharing of member endpoints was settled there. -/
abbrev Index (data : Partition) (basis : GlobalBasis) :=
  {coordinate : Fin data.points.size × Fin 3 // Active basis.points[coordinate.1.val]! coordinate.2}

abbrev Coordinates (data : Partition) (basis : GlobalBasis) := Index data basis → ℝ

def embed (data : Partition) (basis : GlobalBasis) (values : Coordinates data basis) :
    InclinedFrameReal.Motion data :=
  fun point => synthesize basis.points[point.val]!
    (fun localIndex => values ⟨(point, localIndex.val), localIndex.property⟩)

def extract (data : Partition) (basis : GlobalBasis) (motion : InclinedFrameReal.Motion data) :
    Coordinates data basis :=
  fun coordinate => project basis.points[coordinate.val.1.val]! (motion coordinate.val.1)
    ⟨coordinate.val.2, coordinate.property⟩

def Allows (data : Partition) (motion : InclinedFrameReal.Motion data) : Prop :=
  ∀ point : Fin data.points.size, PointAllows data point.val (motion point)

/-- Original support rows, before grouping by point or reducing degree aliases.
    Every source index occurs, including repeated and nearly parallel rollers. -/
def SourceAllows (data : Partition) (motion : InclinedFrameReal.Motion data) : Prop :=
  ∀ index : Fin data.source.supports.size,
    let support := data.source.supports[index.val]!
    let displacement := InclinedFrameReal.pointMotion data motion (locate data support.member support.t)
    (if support.kind = 2 then sourceNormalWork support.angle (displacement 0) (displacement 1) = 0
      else displacement 0 = 0 ∧ displacement 1 = 0) ∧
    (support.kind = 1 → displacement 2 = 0)

theorem allows_iff_source {data : Partition} (hpartition : PartitionValid data)
    (motion : InclinedFrameReal.Motion data) : Allows data motion ↔ SourceAllows data motion := by
  constructor
  · intro hallows index
    have hlocation := support_location hpartition index
    let support := data.source.supports[index.val]!
    let location := locate data support.member support.t
    have hbound : location < data.points.size := hlocation.1.2.1
    have hpoint := hallows ⟨location, hbound⟩
    have howned : owned data location index := rfl
    have htranslation := hpoint.1 index howned
    have hrotation := hpoint.2 index howned
    constructor
    · simpa [InclinedFrameReal.pointMotion, support, location, hbound] using htranslation
    · simpa [InclinedFrameReal.pointMotion, support, location, hbound] using hrotation
  · intro hsource point
    constructor
    · intro index howned
      have hrow := (hsource index).1
      have hlocation : locate data data.source.supports[index.val]!.member
          data.source.supports[index.val]!.t = point.val := howned
      simpa [InclinedFrameReal.pointMotion, hlocation, point.isLt] using hrow
    · intro index howned hfixed
      have hrow := (hsource index).2 hfixed
      have hlocation : locate data data.source.supports[index.val]!.member
          data.source.supports[index.val]!.t = point.val := howned
      simpa [InclinedFrameReal.pointMotion, hlocation, point.isLt] using hrow

/-- Combine source-row equivalence with represented, unique source locations;
    the latter rules out vacuous ownership from a malformed partition. -/
theorem original_support_location {data : Partition} (hpartition : PartitionValid data)
    (index : Fin data.source.supports.size) :
    let support := data.source.supports[index.val]!
    represented data support.member support.t (locate data support.member support.t) = true ∧
      ∀ other, LocationValid data support.member support.t other →
        other = locate data support.member support.t := by
  have hlocation := support_location hpartition index
  exact ⟨hlocation.2, fun _ hother => location_unique hpartition hother hlocation.1⟩

theorem extract_embed (data : Partition) (basis : GlobalBasis) (values : Coordinates data basis) :
    extract data basis (embed data basis values) = values := by
  funext coordinate
  exact congrFun (project_synthesize basis.points[coordinate.val.1.val]!
    (fun localIndex => values ⟨(coordinate.val.1, localIndex.val), localIndex.property⟩))
      ⟨coordinate.val.2, coordinate.property⟩

theorem embed_injective (data : Partition) (basis : GlobalBasis) :
    Function.Injective (embed data basis) := by
  intro first second equalMotion
  have equalCoordinates := congrArg (extract data basis) equalMotion
  simpa only [extract_embed] using equalCoordinates

theorem range_equals_point_kernel {data : Partition} {basis : GlobalBasis}
    (h : GlobalBasisValid data basis) (motion : InclinedFrameReal.Motion data) :
    Allows data motion ↔ ∃ values, embed data basis values = motion := by
  constructor
  · intro hallows
    refine ⟨extract data basis motion, ?_⟩
    funext point
    exact synthesize_project (h.2.1 point) (motion point) (hallows point)
  · rintro ⟨values, rfl⟩ point
    exact synthesize_allows (h.2.1 point)
      (fun localIndex => values ⟨(point, localIndex.val), localIndex.property⟩)

theorem range_equals_source_kernel {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (hbasis : GlobalBasisValid data basis)
    (motion : InclinedFrameReal.Motion data) :
    SourceAllows data motion ↔ ∃ values, embed data basis values = motion :=
  (allows_iff_source hpartition motion).symm.trans (range_equals_point_kernel hbasis motion)

theorem amplitude_add (basis : PointBasis) (first second : LocalCoordinates basis) (slot : Fin 3) :
    amplitude basis (first+second) slot = amplitude basis first slot + amplitude basis second slot := by
  unfold amplitude
  split <;> simp

theorem amplitude_smul (basis : PointBasis) (scalar : ℝ)
    (values : LocalCoordinates basis) (slot : Fin 3) :
    amplitude basis (scalar • values) slot = scalar * amplitude basis values slot := by
  unfold amplitude
  split <;> simp

theorem synthesize_add (basis : PointBasis) (first second : LocalCoordinates basis) :
    synthesize basis (first+second) = synthesize basis first + synthesize basis second := by
  by_cases hfree : basis.translation = 0 <;> by_cases htangent : basis.translation = 1
  all_goals
    funext slot
    fin_cases slot <;> simp [synthesize, hfree, htangent, amplitude_add, mul_add]

theorem synthesize_smul (basis : PointBasis) (scalar : ℝ) (values : LocalCoordinates basis) :
    synthesize basis (scalar • values) = scalar • synthesize basis values := by
  by_cases hfree : basis.translation = 0 <;> by_cases htangent : basis.translation = 1
  all_goals
    funext slot
    fin_cases slot <;> simp [synthesize, hfree, htangent, amplitude_smul, mul_left_comm, mul_assoc]

/-- This explicit linear map is the admissible-coordinate map used to pull
    back the physical stiffness and load forms. -/
def embedding (data : Partition) (basis : GlobalBasis) :
    Coordinates data basis →ₗ[ℝ] InclinedFrameReal.Motion data where
  toFun := embed data basis
  map_add' first second := by
    funext point
    exact synthesize_add basis.points[point.val]!
      (fun localIndex => first ⟨(point, localIndex.val), localIndex.property⟩)
      (fun localIndex => second ⟨(point, localIndex.val), localIndex.property⟩)
  map_smul' scalar values := by
    funext point
    exact synthesize_smul basis.points[point.val]! scalar
      (fun localIndex => values ⟨(point, localIndex.val), localIndex.property⟩)

/-- Interpret a checked executable column as its source-owned coordinate. -/
def columnIndex {data : Partition} {basis : GlobalBasis} (h : GlobalBasisValid data basis)
    (column : Fin basis.columns.size) : Index data basis :=
  ⟨(⟨basis.columns[column.val]!.point, (h.2.2.2.2.1 column).1⟩,
      columnSlot basis.columns[column.val]!), (h.2.2.2.2.1 column).2⟩

theorem columnIndex_injective {data : Partition} {basis : GlobalBasis}
    (h : GlobalBasisValid data basis) : Function.Injective (columnIndex h) := by
  intro first second hequal
  apply h.2.2.2.2.2.1 first second
  · exact congrArg (fun coordinate : Index data basis => coordinate.val.1.val) hequal
  · exact congrArg (fun coordinate : Index data basis => coordinate.val.2) hequal

theorem columnIndex_surjective {data : Partition} {basis : GlobalBasis}
    (h : GlobalBasisValid data basis) : Function.Surjective (columnIndex h) := by
  intro coordinate
  obtain ⟨column, hpoint, hslot⟩ :=
    h.2.2.2.2.2.2 coordinate.val.1 coordinate.val.2 coordinate.property
  refine ⟨column, ?_⟩
  apply Subtype.ext
  exact Prod.ext (Fin.ext hpoint) hslot

def columnEquivalence {data : Partition} {basis : GlobalBasis} (h : GlobalBasisValid data basis) :
    Fin basis.columns.size ≃ Index data basis :=
  Equiv.ofBijective (columnIndex h) ⟨columnIndex_injective h, columnIndex_surjective h⟩

end
end InclinedFrameGlobalBasis
