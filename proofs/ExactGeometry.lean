import MemberCutAdapter

/-!
Exact geometry derived from original endpoints. The relation to a finite frame
model is explicit; it does not certify a parser, cut builder, or private model.
-/
open FrameInterfaces FrameTransform FrameAssemblyModel

namespace ExactGeometry
noncomputable section

abbrev Point := ℝ × ℝ

def dx (a b : Point) : ℝ := b.1 - a.1
def dy (a b : Point) : ℝ := b.2 - a.2
def distance (a b : Point) : ℝ := Real.sqrt (dx a b ^ 2 + dy a b ^ 2)
def position (a b : Point) (t : ℝ) : Point := (a.1 + t * dx a b, a.2 + t * dy a b)
def direction (a b : Point) : Orientation := ⟨dx a b / distance a b, dy a b / distance a b⟩
def degreeCos (angle : ℝ) : ℝ := Real.cos (angle * (Real.pi / 180))
def degreeSin (angle : ℝ) : ℝ := Real.sin (angle * (Real.pi / 180))

theorem displacement_positive (a b : Point) (h : a ≠ b) : 0 < dx a b ^ 2 + dy a b ^ 2 := by
  have hx : 0 ≤ dx a b ^ 2 := sq_nonneg _
  have hy : 0 ≤ dy a b ^ 2 := sq_nonneg _
  by_contra hn
  have hz : dx a b = 0 ∧ dy a b = 0 := by constructor <;> nlinarith
  apply h
  apply Prod.ext <;> dsimp [dx, dy] at hz <;> linarith [hz.1, hz.2]

theorem distance_positive (a b : Point) (h : a ≠ b) : 0 < distance a b := by
  exact Real.sqrt_pos.2 (displacement_positive a b h)

theorem distance_squared (a b : Point) : distance a b ^ 2 = dx a b ^ 2 + dy a b ^ 2 := by
  unfold distance
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]

theorem direction_normalized (a b : Point) (h : a ≠ b) :
    (direction a b).cosine ^ 2 + (direction a b).sine ^ 2 = 1 := by
  have hl := distance_positive a b h
  have hs := distance_squared a b
  simp only [direction]
  field_simp [ne_of_gt hl]
  nlinarith

theorem direction_components (a b : Point) (h : a ≠ b) :
    distance a b * (direction a b).cosine = dx a b ∧
    distance a b * (direction a b).sine = dy a b := by
  have hl := ne_of_gt (distance_positive a b h)
  constructor <;> dsimp [direction] <;> field_simp

theorem position_ends (a b : Point) : position a b 0 = a ∧ position a b 1 = b := by
  constructor <;> apply Prod.ext <;> simp [position, dx, dy]

theorem position_difference (a b : Point) (u v : ℝ) :
    dx (position a b u) (position a b v) = (v-u)*dx a b ∧
    dy (position a b u) (position a b v) = (v-u)*dy a b := by
  simp [position, dx, dy]
  constructor <;> ring

theorem position_injective (a b : Point) (h : a ≠ b) : Function.Injective (position a b) := by
  intro u v huv
  have hp := displacement_positive a b h
  have hx := congrArg Prod.fst huv
  have hy := congrArg Prod.snd huv
  simp only [position, Prod.fst, Prod.snd] at hx hy
  by_contra hn
  have hxzero : (u-v)*dx a b = 0 := by nlinarith [hx]
  have hyzero : (u-v)*dy a b = 0 := by nlinarith [hy]
  have hdx : dx a b = 0 := (mul_eq_zero.mp hxzero).resolve_left (sub_ne_zero.mpr hn)
  have hdy : dy a b = 0 := (mul_eq_zero.mp hyzero).resolve_left (sub_ne_zero.mpr hn)
  rw [hdx, hdy] at hp
  norm_num at hp

theorem transform_inverse_from_endpoints (a b : Point) (h : a ≠ b) (v : Triple) :
    toGlobal (direction a b).cosine (direction a b).sine
      (toLocal (direction a b).cosine (direction a b).sine v) = v := by
  exact inverse_transform _ _ v (direction_normalized a b h)

theorem transform_work_from_endpoints (a b : Point) (h : a ≠ b) (f v : Triple) :
    work (toLocal (direction a b).cosine (direction a b).sine f)
      (toLocal (direction a b).cosine (direction a b).sine v) = work f v := by
  exact work_invariant _ _ f v (direction_normalized a b h)

theorem degree_axis_normalized (angle : ℝ) : degreeCos angle ^ 2 + degreeSin angle ^ 2 = 1 := by
  unfold degreeCos degreeSin
  nlinarith [Real.sin_sq_add_cos_sq (angle * (Real.pi / 180))]

theorem position_interpolation (a b : Point) (u v z : ℝ) :
    position (position a b u) (position a b v) z = position a b (u+(v-u)*z) := by
  apply Prod.ext <;> simp [position, dx, dy] <;> ring

theorem segment_distance (a b : Point) (u v : ℝ) (huv : u < v) :
    distance (position a b u) (position a b v) = (v-u)*distance a b := by
  have hw : 0 ≤ v-u := le_of_lt (sub_pos.mpr huv)
  have hsq := position_difference a b u v
  unfold distance at *
  rw [hsq.1, hsq.2]
  have heq : ((v-u)*dx a b)^2 + ((v-u)*dy a b)^2 = (v-u)^2 * (dx a b^2+dy a b^2) := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg (v-u)), Real.sqrt_sq_eq_abs, abs_of_nonneg hw]

theorem segment_positive (a b : Point) (h : a ≠ b) (u v : ℝ) (huv : u < v) :
    0 < distance (position a b u) (position a b v) := by
  rw [segment_distance a b u v huv]
  exact mul_pos (sub_pos.mpr huv) (distance_positive a b h)

theorem segment_direction (a b : Point) (_h : a ≠ b) (u v : ℝ) (huv : u < v) :
    direction (position a b u) (position a b v) = direction a b := by
  have hd := position_difference a b u v
  have hw : v-u ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  unfold direction
  rw [hd.1, hd.2, segment_distance a b u v huv]
  congr 1 <;> field_simp [hw, ne_of_gt (distance_positive a b _h)] <;> ring

theorem position_reverse (a b : Point) (t : ℝ) : position b a (1-t) = position a b t := by
  apply Prod.ext <;> simp [position, dx, dy] <;> ring

/-- The drawing coordinates are external to Model. This relation anchors the
stored orientation, segment endpoints, length and inherited properties. -/
structure GeometryCorrespondence (model : Model nodes members cuts segments)
    (nodePosition : Fin nodes → Point) (drawingStart drawingEnd : Fin members → Fin nodes)
    (cutParameter : Fin members → Fin cuts → ℝ) (memberEA memberEI : Fin members → ℝ)
    (segmentStart segmentEnd : Fin segments → Point) : Prop where
  incidence : ∀ m, (model.member m).startNode = drawingStart m ∧ (model.member m).endNode = drawingEnd m
  orientation : ∀ m, (model.member m).orientation =
    direction (nodePosition (drawingStart m)) (nodePosition (drawingEnd m))
  startPosition : ∀ s, segmentStart s = position
    (nodePosition (drawingStart (model.segmentMember s)))
    (nodePosition (drawingEnd (model.segmentMember s)))
    (locationParameter cutParameter (model.segmentLeft s))
  endPosition : ∀ s, segmentEnd s = position
    (nodePosition (drawingStart (model.segmentMember s)))
    (nodePosition (drawingEnd (model.segmentMember s)))
    (locationParameter cutParameter (model.segmentRight s))
  length : ∀ s, model.segmentLength s = distance (segmentStart s) (segmentEnd s)
  properties : ∀ s, model.segmentEA s = memberEA (model.segmentMember s) ∧
    model.segmentEI s = memberEI (model.segmentMember s)

/-- Equal adjacent parameters on the same original member give the same
external physical endpoint; this does not weld different member owners. -/
theorem correspondence_shared_join (model : Model nodes members cuts segments)
    (nodePosition : Fin nodes → Point) (drawingStart drawingEnd : Fin members → Fin nodes)
    (cutParameter : Fin members → Fin cuts → ℝ) (memberEA memberEI : Fin members → ℝ)
    (segmentStart segmentEnd : Fin segments → Point)
    (geometry : GeometryCorrespondence model nodePosition drawingStart drawingEnd cutParameter memberEA memberEI segmentStart segmentEnd)
    (left right : Fin segments) (sameMember : model.segmentMember left = model.segmentMember right)
    (sameParameter : locationParameter cutParameter (model.segmentRight left) =
      locationParameter cutParameter (model.segmentLeft right)) : segmentEnd left = segmentStart right := by
  rw [geometry.endPosition left, geometry.startPosition right, sameMember, sameParameter]

/-- Only cut allocation, ownership and source representation are assumed here.
Their construction from a TypeScript artifact is a separate open obligation. -/
structure StructuralPremises (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ) : Prop where
  ownership : segmentOwnershipValid model
  ordered : ∀ s, 0 ≤ locationParameter cutParameter (model.segmentLeft s) ∧
    locationParameter cutParameter (model.segmentLeft s) < locationParameter cutParameter (model.segmentRight s) ∧
    locationParameter cutParameter (model.segmentRight s) ≤ 1
  coverage : ∀ m t, 0 ≤ t → t ≤ 1 → ∃ s, model.segmentMember s = m ∧
    locationParameter cutParameter (model.segmentLeft s) ≤ t ∧ t ≤ locationParameter cutParameter (model.segmentRight s)
  disjointInteriors : ∀ a b, a ≠ b → model.segmentMember a = model.segmentMember b →
    locationParameter cutParameter (model.segmentRight a) ≤ locationParameter cutParameter (model.segmentLeft b) ∨
    locationParameter cutParameter (model.segmentRight b) ≤ locationParameter cutParameter (model.segmentLeft a)
  canonicalLocations : ∀ m left right, locationBelongs m left → locationBelongs m right →
    representedLocation model left → representedLocation model right →
    locationParameter cutParameter left = locationParameter cutParameter right → left = right
  memberEnds : ∀ m, representedLocation model (.endSide (m, false)) ∧ representedLocation model (.endSide (m, true))
  interiorCuts : ∀ m cut, representedLocation model (.interior m cut) → 0 < cutParameter m cut ∧ cutParameter m cut < 1
  actionLocations : ∀ action, representedLocation model (actions action).location
  supportLocations : ∀ support, representedLocation model (supports support).location

/-- Only roller and guided axes need trigonometric correspondence. -/
def SupportAxisCorrespondence (supports : Fin supportCount → SupportInput members cuts)
    (angles : Fin supportCount → ℝ) : Prop :=
  ∀ s, (supports s).kind = .roller ∨ (supports s).kind = .guided →
    (supports s).cosine = degreeCos (angles s) ∧ (supports s).sine = degreeSin (angles s)

/-- Positivity is stated for actual active endConnection laws, including their
reference/explicit/default resolution; it is not assumed for arbitrary springs. -/
def EffectiveSpringPositive (model : Model nodes members cuts segments) : Prop :=
  ∀ side direction stiffness, activeEnd model side →
    directionLaw (endConnection model side) direction = .spring stiffness → 0 < stiffness

/-- Positivity of explicit spring inputs and semi-rigid default stiffnesses.
Reference ends and all default/explicit choices are resolved by endConnection. -/
def SpringInputPositive (model : Model nodes members cuts segments) : Prop :=
  (∀ (side : MemberEnd members) (connection : EndConnection) (direction : Fin 3) (stiffness : ℝ),
    (if side.2 then (model.member side.1).explicitEnd else (model.member side.1).explicitStart) = some connection →
    directionLaw connection direction = .spring stiffness → 0 < stiffness) ∧
  (∀ (node : Fin nodes), (model.joints node).kind = .semiRigid → 0 < (model.joints node).rotationStiffness)

theorem effective_springs_from_inputs (model : Model nodes members cuts segments)
    (inputs : SpringInputPositive model) : EffectiveSpringPositive model := by
  intro side direction stiffness _active law
  by_cases reference : referenceMember model (endNode model side) = some side.1
  · fin_cases direction <;> simp [endConnection, reference, directionLaw, rigidConnection] at law
  · simp only [endConnection, reference, if_false] at law
    cases choice : (if side.2 then (model.member side.1).explicitEnd else (model.member side.1).explicitStart) with
    | some connection =>
      rw [choice] at law
      exact inputs.1 side connection direction stiffness choice law
    | none =>
      rw [choice] at law
      cases joint : (model.joints (endNode model side)).kind <;>
        fin_cases direction <;> simp [joint, directionLaw] at law
      subst stiffness
      exact inputs.2 (endNode model side) joint

def memberDistance (nodePosition : Fin nodes → Point) (drawingStart drawingEnd : Fin members → Fin nodes) (m : Fin members) : ℝ :=
  distance (nodePosition (drawingStart m)) (nodePosition (drawingEnd m))

/-- Geometry and properties are derived, while the finite-builder premises and
actual spring-law positivity remain explicit. -/
theorem compose_exact_contract (model : Model nodes members cuts segments)
    (actions : Fin actionCount → PointAction members cuts)
    (supports : Fin supportCount → SupportInput members cuts)
    (cutParameter : Fin members → Fin cuts → ℝ)
    (nodePosition : Fin nodes → Point) (drawingStart drawingEnd : Fin members → Fin nodes)
    (memberEA memberEI : Fin members → ℝ) (segmentStart segmentEnd : Fin segments → Point) (angles : Fin supportCount → ℝ)
    (structureValid : StructuralPremises model actions supports cutParameter)
    (geometry : GeometryCorrespondence model nodePosition drawingStart drawingEnd cutParameter memberEA memberEI segmentStart segmentEnd)
    (noncoincident : ∀ m, nodePosition (drawingStart m) ≠ nodePosition (drawingEnd m))
    (positiveEA : ∀ m, 0 < memberEA m) (positiveEI : ∀ m, 0 < memberEI m)
    (supportAxes : SupportAxisCorrespondence supports angles)
    (springInputs : SpringInputPositive model) :
    ExactContract model actions supports cutParameter (memberDistance nodePosition drawingStart drawingEnd) memberEA memberEI ∧
      GeometryCorrespondence model nodePosition drawingStart drawingEnd cutParameter memberEA memberEI segmentStart segmentEnd := by
  constructor
  · constructor
    · exact structureValid.ownership
    · exact structureValid.ordered
    · exact structureValid.coverage
    · exact structureValid.disjointInteriors
    · exact structureValid.canonicalLocations
    · exact structureValid.memberEnds
    · exact structureValid.interiorCuts
    · exact structureValid.actionLocations
    · exact structureValid.supportLocations
    · intro m
      rw [geometry.orientation m]
      exact direction_normalized _ _ (noncoincident m)
    · intro s hs
      obtain ⟨hc, hsine⟩ := supportAxes s hs
      rw [hc, hsine]
      exact degree_axis_normalized (angles s)
    · intro m
      exact ⟨distance_positive _ _ (noncoincident m), positiveEA m, positiveEI m⟩
    · intro s
      rw [geometry.length s, geometry.startPosition s, geometry.endPosition s,
        segment_distance _ _ _ _ (structureValid.ordered s).2.1]
      simp [memberDistance, mul_comm]
    · exact geometry.properties
    · exact effective_springs_from_inputs model springInputs
  · exact geometry

end
end ExactGeometry
