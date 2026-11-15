import InclinedFrameSource
import ExactGeometry
import FrameEnergy

/-! Real rigid-frame reference derived from the original exact source. Segment
    geometry uses physical Euclidean length and the original member direction.
    This is the target of interval assembly, not a rounded interval midpoint model. -/
namespace InclinedFrameReal
open InclinedFrameSource FrameInterfaces FrameTransform
noncomputable section

def endpoints (data : Partition) (member : Nat) : ExactGeometry.Point × ExactGeometry.Point :=
  let source := data.source.members[member]!
  let a := data.source.nodes[source.a]!
  let b := data.source.nodes[source.b]!
  (((a.x : ℝ), (a.y : ℝ)), ((b.x : ℝ), (b.y : ℝ)))

def memberLength (data : Partition) (member : Nat) : ℝ :=
  ExactGeometry.distance (endpoints data member).1 (endpoints data member).2

def memberDirection (data : Partition) (member : Nat) : FrameInterfaces.Orientation :=
  ExactGeometry.direction (endpoints data member).1 (endpoints data member).2

def pieceLength (data : Partition) (piece : Piece) : ℝ :=
  memberLength data piece.member * ((piece.right : ℝ) - piece.left)

theorem endpoints_distinct (data : Partition) (h : SourceValid data.source)
    (member : Fin data.source.members.size) :
    (endpoints data member.val).1 ≠ (endpoints data member.val).2 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hmembers, _, _⟩
  have hm := hmembers member
  rcases hm with ⟨_, _, _, _, _, _, hdistinct⟩
  intro heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  dsimp [endpoints] at hx hy
  have hxrat : data.source.nodes[data.source.members[member.val]!.a]!.x =
      data.source.nodes[data.source.members[member.val]!.b]!.x := by exact_mod_cast hx
  have hyrat : data.source.nodes[data.source.members[member.val]!.a]!.y =
      data.source.nodes[data.source.members[member.val]!.b]!.y := by exact_mod_cast hy
  exact hdistinct.elim (fun hn => hn hxrat) (fun hn => hn hyrat)

theorem member_positive (data : Partition) (h : SourceValid data.source)
    (member : Fin data.source.members.size) : 0 < memberLength data member.val :=
  ExactGeometry.distance_positive _ _ (endpoints_distinct data h member)

theorem member_normalized (data : Partition) (h : SourceValid data.source)
    (member : Fin data.source.members.size) :
    (memberDirection data member.val).cosine^2 + (memberDirection data member.val).sine^2 = 1 :=
  ExactGeometry.direction_normalized _ _ (endpoints_distinct data h member)

theorem piece_properties (data : Partition) (h : PartitionValid data)
    (piece : Fin data.pieces.size) :
    0 < pieceLength data data.pieces[piece.val]! ∧
    0 < (data.source.members[data.pieces[piece.val]!.member]!.EA : ℝ) ∧
    0 < (data.source.members[data.pieces[piece.val]!.member]!.EI : ℝ) := by
  rcases h with ⟨hsource, _, _, _, _, _, _, hpieces, _, _, _, _⟩
  have hp := hpieces piece
  have hmemberBound := hp.1.1
  have hlength := member_positive data hsource ⟨_, hmemberBound⟩
  rcases hsource with ⟨_, _, _, _, _, _, _, _, _, _, _, hmembers, _, _⟩
  have hm := hmembers ⟨_, hmemberBound⟩
  refine ⟨?_, ?_, ?_⟩
  · apply mul_pos hlength
    exact_mod_cast sub_pos.mpr hp.2.2.2.1
  · exact_mod_cast hm.2.2.2.1
  · exact_mod_cast hm.2.2.2.2.1

theorem piece_physical_length (data : Partition) (piece : Piece)
    (h : piece.left < piece.right) :
    pieceLength data piece = ExactGeometry.distance
      (ExactGeometry.position (endpoints data piece.member).1 (endpoints data piece.member).2 piece.left)
      (ExactGeometry.position (endpoints data piece.member).1 (endpoints data piece.member).2 piece.right) := by
  rw [ExactGeometry.segment_distance _ _ _ _ (by exact_mod_cast h)]
  unfold pieceLength memberLength
  ring

abbrev Motion (data : Partition) := Fin data.points.size → Triple

def pointMotion (data : Partition) (motion : Motion data) (point : Nat) : Triple :=
  if h : point < data.points.size then motion ⟨point, h⟩ else 0

def pieceMotion (data : Partition) (piece : Piece) (motion : Motion data) : LocalDofs :=
  let a := pointMotion data motion piece.a
  let b := pointMotion data motion piece.b
  let direction := memberDirection data piece.member
  toLocal6 direction.cosine direction.sine ![a 0, a 1, a 2, b 0, b 1, b 2]

theorem pointMotion_add (data : Partition) (x y : Motion data) (point : Nat) :
    pointMotion data (x+y) point = pointMotion data x point + pointMotion data y point := by
  unfold pointMotion
  split <;> simp

theorem pointMotion_smul (data : Partition) (scalar : ℝ) (x : Motion data) (point : Nat) :
    pointMotion data (scalar • x) point = scalar • pointMotion data x point := by
  unfold pointMotion
  split <;> simp

theorem pieceMotion_add (data : Partition) (piece : Piece) (x y : Motion data) :
    pieceMotion data piece (x+y) = pieceMotion data piece x + pieceMotion data piece y := by
  funext i
  fin_cases i <;> simp [pieceMotion, pointMotion_add, toLocal6] <;> ring

theorem pieceMotion_smul (data : Partition) (piece : Piece) (scalar : ℝ) (x : Motion data) :
    pieceMotion data piece (scalar • x) = scalar • pieceMotion data piece x := by
  funext i
  fin_cases i <;> simp [pieceMotion, pointMotion_smul, toLocal6] <;> ring

/-- The physical bilinear form sums the established local beam stiffness after
    transforming both motion and virtual displacement into the source axes. -/
def stiffnessWork (data : Partition) (motion variation : Motion data) : ℝ :=
  ∑ s : Fin data.pieces.size,
    let piece := data.pieces[s.val]!
    let member := data.source.members[piece.member]!
    ∑ i : Fin 6, ∑ j : Fin 6,
      pieceMotion data piece variation i *
      LocalFrameFields.stiffness (pieceLength data piece) member.EA member.EI i j *
      pieceMotion data piece motion j

theorem stiffness_add_left (data : Partition) (x y z : Motion data) :
    stiffnessWork data (x+y) z = stiffnessWork data x z + stiffnessWork data y z := by
  simp [stiffnessWork, pieceMotion_add, mul_add, Finset.sum_add_distrib]

theorem stiffness_add_right (data : Partition) (x y z : Motion data) :
    stiffnessWork data x (y+z) = stiffnessWork data x y + stiffnessWork data x z := by
  simp [stiffnessWork, pieceMotion_add, add_mul, Finset.sum_add_distrib]

theorem stiffness_smul_left (data : Partition) (scalar : ℝ) (x y : Motion data) :
    stiffnessWork data (scalar • x) y = scalar * stiffnessWork data x y := by
  simp [stiffnessWork, pieceMotion_smul, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem stiffness_smul_right (data : Partition) (scalar : ℝ) (x y : Motion data) :
    stiffnessWork data x (scalar • y) = scalar * stiffnessWork data x y := by
  simp [stiffnessWork, pieceMotion_smul, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Hold the physical motion fixed while varying the virtual displacement.
    Naming this map keeps the outer linearity proof from expanding its record. -/
def stiffnessVariation (data : Partition) (x : Motion data) : Motion data →ₗ[ℝ] ℝ where
  toFun := stiffnessWork data x
  map_add' := stiffness_add_right data x
  map_smul' := by
    intro scalar y
    change stiffnessWork data x (scalar • y) = scalar * stiffnessWork data x y
    exact stiffness_smul_right data scalar x y

theorem stiffnessVariation_add (data : Partition) (x y : Motion data) :
    stiffnessVariation data (x+y) = stiffnessVariation data x + stiffnessVariation data y := by
  apply LinearMap.ext
  intro z
  change stiffnessWork data (x+y) z = stiffnessWork data x z + stiffnessWork data y z
  exact stiffness_add_left data x y z

theorem stiffnessVariation_smul (data : Partition) (scalar : ℝ) (x : Motion data) :
    stiffnessVariation data (scalar • x) = scalar • stiffnessVariation data x := by
  apply LinearMap.ext
  intro y
  change stiffnessWork data (scalar • x) y = scalar * stiffnessWork data x y
  exact stiffness_smul_left data scalar x y

/-- The source stiffness form in the linear-map interface used by the stability
    argument. Linearity follows from the actual transforms and local stiffness. -/
def stiffnessForm (data : Partition) : Motion data →ₗ[ℝ] Motion data →ₗ[ℝ] ℝ where
  toFun := stiffnessVariation data
  map_add' := stiffnessVariation_add data
  map_smul' := stiffnessVariation_smul data

def pieceLoad (data : Partition) (piece : Piece) : LocalActions :=
  let direction := memberDirection data piece.member
  LocalFrameFields.consistentLoad (pieceLength data piece)
    (direction.sine * piece.vertical) (direction.sine * piece.verticalEnd)
    (direction.cosine * piece.vertical) (direction.cosine * piece.verticalEnd)

def pointLoadWork (data : Partition) (index : Fin data.source.loads.size)
    (variation : Motion data) : ℝ :=
    let load := data.source.loads[index.val]!
    let motion := pointMotion data variation (locate data load.member load.t)
    if load.kind = 0 then (load.fx : ℝ)*motion 0 + (load.fy : ℝ)*motion 1
    else if load.kind = 1 then (load.mz : ℝ)*motion 2 else 0

/-- Virtual work includes every original point action at its owned cut, and
    the exact affine consistent load of every physical segment. -/
def externalWork (data : Partition) (variation : Motion data) : ℝ :=
  (∑ s : Fin data.pieces.size,
    let piece := data.pieces[s.val]!
    ∑ i : Fin 6, pieceLoad data piece i * pieceMotion data piece variation i) +
  ∑ i : Fin data.source.loads.size, pointLoadWork data i variation

theorem pointLoadWork_add (data : Partition) (index : Fin data.source.loads.size)
    (first second : Motion data) :
    pointLoadWork data index (first+second) =
      pointLoadWork data index first + pointLoadWork data index second := by
  unfold pointLoadWork
  simp only [pointMotion_add, Pi.add_apply]
  split_ifs <;> ring

theorem pointLoadWork_smul (data : Partition) (index : Fin data.source.loads.size)
    (scalar : ℝ) (variation : Motion data) :
    pointLoadWork data index (scalar • variation) = scalar * pointLoadWork data index variation := by
  unfold pointLoadWork
  simp only [pointMotion_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem externalWork_add (data : Partition) (first second : Motion data) :
    externalWork data (first+second) = externalWork data first + externalWork data second := by
  simp only [externalWork, pieceMotion_add, Pi.add_apply, pointLoadWork_add,
    mul_add, Finset.sum_add_distrib]
  ring

theorem externalWork_smul (data : Partition) (scalar : ℝ) (variation : Motion data) :
    externalWork data (scalar • variation) = scalar * externalWork data variation := by
  simp [externalWork, pieceMotion_smul, pointLoadWork_smul, Finset.mul_sum,
    mul_add, mul_assoc, mul_left_comm]

def loadForm (data : Partition) : Motion data →ₗ[ℝ] ℝ where
  toFun := externalWork data
  map_add' := externalWork_add data
  map_smul' := by intro scalar variation; simpa using externalWork_smul data scalar variation

def residualWork (data : Partition) (motion variation : Motion data) : ℝ :=
  stiffnessWork data motion variation - externalWork data variation

/-- Reaction components belong to the rigid point. Repeated restraints do not
    create uniquely determined individual support shares. -/
def groupedReaction (data : Partition) (motion : Motion data)
    (point : Fin data.points.size) (direction : Fin 3) : ℝ :=
  residualWork data motion (fun p d => if p = point ∧ d = direction then 1 else 0)

/-- Six original-model loaded fields, with the global displacement components
    transformed back from the local axial/transverse polynomial fields. -/
def fieldValues (data : Partition) (piece : Piece) (motion : Motion data) (parameter : ℝ) : Fin 6 → ℝ :=
  let member := data.source.members[piece.member]!
  let direction := memberDirection data piece.member
  let L := pieceLength data piece
  let x := L * (parameter-piece.left) / ((piece.right : ℝ)-piece.left)
  let d := pieceMotion data piece motion
  let p₀ := direction.sine * piece.vertical
  let p₁ := direction.sine * piece.verticalEnd
  let q₀ := direction.cosine * piece.vertical
  let q₁ := direction.cosine * piece.verticalEnd
  let axial := (LocalFrameFields.axialDisplacement d L member.EA p₀ p₁).eval x
  let transverse := (LocalFrameFields.transverseDisplacement d L member.EI q₀ q₁).eval x
  ![(LocalFrameFields.normal d L member.EA p₀ p₁).eval x,
    (LocalFrameFields.shear d L member.EI q₀ q₁).eval x,
    (LocalFrameFields.moment d L member.EI q₀ q₁).eval x,
    (LocalFrameFields.rotation d L member.EI q₀ q₁).eval x,
    direction.cosine*axial - direction.sine*transverse,
    direction.sine*axial + direction.cosine*transverse]

theorem stiffness_nonnegative (data : Partition) (h : PartitionValid data) (motion : Motion data) :
    0 ≤ stiffnessWork data motion motion := by
  apply Finset.sum_nonneg
  intro s _
  have hp := piece_properties data h s
  exact FrameEnergy.stiffness_positive_semidefinite _ _ _ _ hp.1 hp.2.1 hp.2.2

theorem stiffness_symmetric (data : Partition) (motion variation : Motion data) :
    stiffnessWork data motion variation = stiffnessWork data variation motion := by
  apply Finset.sum_congr rfl
  intro s _
  dsimp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [LocalFrameFields.stiffness_symmetric _ _ _ j i]
  ring

end
end InclinedFrameReal
