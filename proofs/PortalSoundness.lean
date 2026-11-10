import PortalChecker
import PortalFramePilot
import FrameReuse

open FrameAssemblyModel FrameAssembly FrameTransform
open scoped BigOperators

namespace PortalSoundness
noncomputable section

-- Normalize finite numerals explicitly, as in the accepted portal incidence fixture.
@[local simp] theorem index3_2 : (2 : Fin 3) = ⟨2, by decide⟩ := rfl
@[local simp] theorem index4_2 : (2 : Fin 4) = ⟨2, by decide⟩ := rfl
@[local simp] theorem index4_3 : (3 : Fin 4) = ⟨3, by decide⟩ := rfl
@[local simp] theorem index6_2 : (2 : Fin 6) = ⟨2, by decide⟩ := rfl
@[local simp] theorem index6_3 : (3 : Fin 6) = ⟨3, by decide⟩ := rfl
@[local simp] theorem index6_4 : (4 : Fin 6) = ⟨4, by decide⟩ := rfl
@[local simp] theorem index6_5 : (5 : Fin 6) = ⟨5, by decide⟩ := rfl
@[local simp] theorem index12_2 : (2 : Fin 12) = ⟨2, by decide⟩ := rfl
@[local simp] theorem index12_3 : (3 : Fin 12) = ⟨3, by decide⟩ := rfl
@[local simp] theorem index12_4 : (4 : Fin 12) = ⟨4, by decide⟩ := rfl
@[local simp] theorem index12_5 : (5 : Fin 12) = ⟨5, by decide⟩ := rfl
@[local simp] theorem index12_6 : (6 : Fin 12) = ⟨6, by decide⟩ := rfl
@[local simp] theorem index12_7 : (7 : Fin 12) = ⟨7, by decide⟩ := rfl
@[local simp] theorem index12_8 : (8 : Fin 12) = ⟨8, by decide⟩ := rfl
@[local simp] theorem index12_9 : (9 : Fin 12) = ⟨9, by decide⟩ := rfl
@[local simp] theorem index12_10 : (10 : Fin 12) = ⟨10, by decide⟩ := rfl
@[local simp] theorem index12_11 : (11 : Fin 12) = ⟨11, by decide⟩ := rfl

/-- Exactly the accepted portal, changing only the uniform BC intensity. -/
def model (a : ℝ) : Model 4 3 0 3 :=
  { PortalFramePilot.model with
    segmentVerticalStart := fun i => if i = 1 then a else 0
    segmentVerticalEnd := fun i => if i = 1 then a else 0 }

abbrev actions := PortalFramePilot.actions
abbrev supports := PortalFramePilot.supports

theorem rigid (a : ℝ) (m : Fin 3) (ending : Bool) :
    endConnection (model a) (m, ending) = rigidConnection := by
  fin_cases m <;> cases ending <;> rfl

theorem no_slip (a : ℝ) (side : MemberEnd 3) (direction : Fin 3) :
    ¬ hasSlip (model a) side direction := by
  rcases side with ⟨m, ending⟩
  simp [hasSlip, rigid, directionLaw, rigidConnection]

theorem all_hubs (a : ℝ) (node : Fin 4) : activePoint (model a) (.inl node) := by
  fin_cases node
  · exact ⟨0, Or.inl rfl⟩
  · exact ⟨0, Or.inr rfl⟩
  · exact ⟨1, Or.inr rfl⟩
  · exact ⟨2, Or.inr rfl⟩

def hub (a : ℝ) (node : Fin 4) : ActivePoint (model a) := ⟨.inl node, all_hubs a node⟩

/-- Explicit order Ax,Ay,Arotation,Bx,...,Drotation. -/
def coordinate (a : ℝ) (i : Fin 12) : Coordinate (model a) :=
  .inl (hub a ⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩)

def motion (a : ℝ) (u : Fin 12 → ℝ) : Coordinate (model a) → ℝ
  | .inl (⟨.inl node, _⟩, direction) => u ⟨3 * node.val + direction.val, by omega⟩
  | .inl (⟨.inr (_, cut), _⟩, _) => Fin.elim0 cut
  | .inr slip => False.elim (no_slip a slip.val.1 slip.val.2 slip.property)

@[simp] theorem motion_coordinate (a : ℝ) (u : Fin 12 → ℝ) (i : Fin 12) :
    motion a u (coordinate a i) = u i := by
  fin_cases i <;> rfl

theorem coordinates_total (a : ℝ) (q : Coordinate (model a) → ℝ) :
    motion a (fun i => q (coordinate a i)) = q := by
  funext c
  rcases c with ⟨⟨point, hpoint⟩, direction⟩ | slip
  · rcases point with node | ⟨member, cut⟩
    · fin_cases node <;> fin_cases direction <;> rfl
    · exact Fin.elim0 cut
  · exact False.elim (no_slip a slip.val.1 slip.val.2 slip.property)

theorem motion_injective (a : ℝ) : Function.Injective (motion a) := by
  intro u v h
  funext i
  simpa using congrFun h (coordinate a i)

@[simp] theorem reference_motion (a : ℝ) (u : Fin 12 → ℝ) (n : Fin 4) (d : Fin 3) :
    referenceMotion (model a) (motion a u) (.inl n) d =
      u ⟨3 * n.val + d.val, by omega⟩ := by
  simp [referenceMotion, all_hubs, motion]

@[simp] theorem zero_slip (a : ℝ) (q : Coordinate (model a) → ℝ)
    (side : MemberEnd 3) (d : Fin 3) : slipValue (model a) q side d = 0 := by
  simp [slipValue, no_slip]

def elementMotion (u : Fin 12 → ℝ) : Fin 3 → FrameInterfaces.LocalDofs :=
  ![![u 1, -u 0, u 2, u 4, -u 3, u 5],
    ![u 3, u 4, u 5, u 6, u 7, u 8],
    ![-u 7, u 6, u 8, -u 10, u 9, u 11]]

theorem actual_side_motion (a : ℝ) (u : Fin 12 → ℝ) (side : MemberEnd 3) :
    sideMotion (model a) (motion a u) (.endSide side) =
      referenceMotion (model a) (motion a u) (.inl (endNode (model a) side)) := by
  funext d
  fin_cases d <;> simp [sideMotion, zero_slip, endMotion]

theorem actual_element_motion (a : ℝ) (u : Fin 12 → ℝ) (s : Fin 3) :
    segmentDofs (model a) (motion a u) s = elementMotion u s := by
  funext d
  fin_cases s <;> fin_cases d <;>
    simp only [segmentDofs, segmentMotion, actual_side_motion, reference_motion, toLocal6]
  all_goals norm_num [model, PortalFramePilot.model,
      PortalFramePilot.drawingStart, PortalFramePilot.drawingEnd, PortalFramePilot.cosine,
      PortalFramePilot.sine, endNode, endMotion, toLocal6, elementMotion,
      reference_motion, zero_slip]
  all_goals simp only [actual_side_motion, reference_motion]
  all_goals norm_num [endNode, model, PortalFramePilot.model, PortalFramePilot.drawingStart,
    PortalFramePilot.drawingEnd, Fin.instOfNat, Fin.ofNat', Fin.succ]
  all_goals rfl

def K (i j : Fin 12) : ℝ := (PortalChecker.stiffness i j : ℝ)
def F (a : ℝ) (i : Fin 12) : ℝ := a * (PortalChecker.force i : ℝ)
def residual (a : ℝ) (u : Fin 12 → ℝ) (i : Fin 12) : ℝ :=
  (∑ j, K i j * u j) - F a i

set_option maxHeartbeats 4000000 in
theorem actual_stiffness_work (a : ℝ) (u v : Fin 12 → ℝ) :
    stiffnessWork (model a) (motion a u) (motion a v) =
      ∑ i, v i * ∑ j, K i j * u j := by
  simp only [stiffnessWork, internalVirtualWork, actual_element_motion]
  simp only [zero_slip, mul_zero, Finset.sum_const_zero, add_zero]
  norm_num [model, PortalFramePilot.model, PortalFramePilot.lengths,
    PortalFramePilot.axialRigidity, PortalFramePilot.flexuralRigidity,
    LocalFrameFields.stiffness, elementMotion, K, PortalChecker.stiffness,
    PortalChecker.stiffnessRows, Fin.sum_univ_succ, rigid, springStiffness,
    directionLaw, rigidConnection, Fin.instOfNat, Fin.ofNat', Fin.succ]
  <;> ring!

set_option maxHeartbeats 2000000 in
theorem actual_force_work (a : ℝ) (v : Fin 12 → ℝ) :
    externalWork (model a) actions (motion a v) = ∑ i, F a i * v i := by
  simp only [externalWork, actual_element_motion]
  simp [actions, PortalFramePilot.actions, segmentLoad, model, PortalFramePilot.model,
    PortalFramePilot.cosine, PortalFramePilot.sine, PortalFramePilot.lengths,
    LocalFrameFields.consistentLoad, elementMotion, F, PortalChecker.force,
    PortalChecker.unitForce, Fin.sum_univ_succ]
  <;> ring

theorem actual_residual_work (a : ℝ) (u v : Fin 12 → ℝ) :
    residualWork (model a) actions (motion a u) (motion a v) = ∑ i, v i * residual a u i := by
  rw [residualWork, ← stiffnessWork, actual_stiffness_work, actual_force_work]
  simp [residual, mul_sub, Finset.sum_sub_distrib, mul_comm]

theorem actual_admissibility (a : ℝ) (u : Fin 12 → ℝ) :
    admissible (model a) supports (motion a u) ↔
      ∀ i : Fin 6, u (PortalChecker.baseIndex i) = 0 := by
  simp only [admissible, Fin.forall_fin_succ, supports, PortalFramePilot.supports,
    supportDirections, supportRow, actual_side_motion, reference_motion]
  norm_num [endNode, model, PortalFramePilot.model,
    PortalFramePilot.drawingStart, PortalFramePilot.drawingEnd, PortalFramePilot.cosine,
    PortalFramePilot.sine, PortalChecker.baseIndex, reference_motion, zero_slip,
    FrameTransform.work, Fin.instOfNat, Fin.ofNat', Fin.succ]
  simp only [actual_side_motion, reference_motion]
  norm_num [endNode, model, PortalFramePilot.model, PortalFramePilot.drawingStart,
    PortalFramePilot.drawingEnd, Fin.instOfNat, Fin.ofNat', Fin.succ]
  change ((u 0 + 0 * u 2 = 0 ∧ u 1 + 0 * u 2 = 0 ∧ ((1 : ℝ) = 0 ∨ u 2 = 0)) ∧
    u 9 + 0 * u 11 = 0 ∧ u 10 + 0 * u 11 = 0 ∧ ((1 : ℝ) = 0 ∨ u 11 = 0)) ↔
    u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 0 ∧ u 9 = 0 ∧ u 10 = 0 ∧ u 11 = 0
  simp [and_assoc]

def lift (z : Fin 6 → ℝ) : Fin 12 → ℝ :=
  ![0, 0, 0, z 0, z 1, z 2, z 3, z 4, z 5, 0, 0, 0]

theorem lift_image (a : ℝ) (q : Coordinate (model a) → ℝ) :
    admissible (model a) supports q ↔ ∃ z, q = motion a (lift z) := by
  rw [← coordinates_total a q, actual_admissibility]
  constructor
  · intro h
    refine ⟨fun i => q (coordinate a (PortalChecker.freeIndex i)), ?_⟩
    apply congrArg (motion a)
    funext i
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    norm_num [PortalChecker.baseIndex] at h0 h1 h2 h3 h4 h5
    fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | rfl
  · rintro ⟨z, hz⟩
    have heq := motion_injective a hz
    intro i
    rw [congrFun heq]
    fin_cases i <;> rfl

theorem acceptance_predicate (a : Rat) (q : PortalChecker.Motion)
    (r : PortalChecker.Reactions) (m u : Rat) (h : PortalChecker.accepts a q r m u = true) :
    PortalChecker.Valid a q r m u := of_decide_eq_true h

set_option maxHeartbeats 4000000 in
/-- The fixed inverse is a kernel-checked witness, also valid at zero load. -/
theorem fixed_inverse (i j : Fin 6) :
    (∑ k : Fin 6, (PortalChecker.inverse i k : ℝ) *
      K (PortalChecker.freeIndex k) (PortalChecker.freeIndex j)) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [PortalChecker.inverse, PortalChecker.inverseRows, PortalChecker.freeIndex,
      K, PortalChecker.stiffness, PortalChecker.stiffnessRows, Fin.sum_univ_succ,
      Fin.instOfNat, Fin.ofNat', Fin.succ]

theorem rational_residual_cast (a : Rat) (q : PortalChecker.Motion) (i : Fin 12) :
    (PortalChecker.residual a q i : ℝ) = residual a (fun j => (q j : ℝ)) i := by
  fin_cases i <;>
    norm_num [PortalChecker.residual, PortalChecker.dotRow, List.finRange,
      PortalChecker.stiffness, PortalChecker.stiffnessRows, PortalChecker.force,
      PortalChecker.unitForce, residual, K, F, Fin.sum_univ_succ] <;> push_cast <;> ring

theorem residual_equilibrium (a : ℝ) (u : Fin 12 → ℝ)
    (hbase : ∀ i, u (PortalChecker.baseIndex i) = 0)
    (hfree : ∀ i, residual a u (PortalChecker.freeIndex i) = 0) :
    equilibrium (model a) actions supports (motion a u) := by
  refine ⟨(actual_admissibility a u).mpr hbase, ?_⟩
  intro v hv
  obtain ⟨z, rfl⟩ := (lift_image a v).mp hv
  rw [actual_residual_work]
  have h0 := hfree 0
  have h1 := hfree 1
  have h2 := hfree 2
  have h3 := hfree 3
  have h4 := hfree 4
  have h5 := hfree 5
  change residual a u 3 = 0 at h0
  change residual a u 4 = 0 at h1
  change residual a u 5 = 0 at h2
  change residual a u 6 = 0 at h3
  change residual a u 7 = 0 at h4
  change residual a u 8 = 0 at h5
  simp [lift, Fin.sum_univ_succ, Fin.instOfNat, Fin.ofNat', Fin.succ] at *
  simp_all

theorem accepted_equilibrium (a : Rat) (q : PortalChecker.Motion)
    (r : PortalChecker.Reactions) (m u : Rat) (h : PortalChecker.accepts a q r m u = true) :
    equilibrium (model a) actions supports (motion a (fun i => (q i : ℝ))) := by
  obtain ⟨hbase, hfree, _, _, _⟩ := acceptance_predicate a q r m u h
  apply residual_equilibrium
  · intro i
    exact_mod_cast hbase i
  · intro i
    rw [← rational_residual_cast]
    exact_mod_cast hfree i

set_option maxHeartbeats 2000000 in
/-- Both formulas include the nonzero uniform-load particular field. -/
theorem actual_midpoint (a : ℝ) (u : Fin 12 → ℝ) :
    (LocalFrameFields.moment (segmentDofs (model a) (motion a u) 1) 6 20000 a a).eval 3 =
      (20000 / 6) * (u 8 - u 5) - (3 / 2) * a ∧
    (LocalFrameFields.transverseDisplacement (segmentDofs (model a) (motion a u) 1) 6 20000 a a).eval 3 =
      (u 4 + u 7) / 2 + (3 / 4) * (u 5 - u 8) + (27 / 160000) * a := by
  rw [actual_element_motion]
  constructor <;>
    norm_num [elementMotion, LocalFrameFields.moment, LocalFrameFields.rotation,
      LocalFrameFields.transverseDisplacement, LocalFrameFields.coordinate,
      Polynomial.derivative_mul, Polynomial.derivative_pow, Fin.instOfNat, Fin.ofNat', Fin.succ] <;> ring!

/-- The accepted positive contract is unchanged by the sole load parameter. -/
theorem physical_contract (a : ℝ) :
    ExactContract (model a) actions supports PortalFramePilot.cutParameter
      (ExactGeometry.memberDistance PortalFramePilot.nodePosition PortalFramePilot.drawingStart PortalFramePilot.drawingEnd)
      PortalFramePilot.sourceEA PortalFramePilot.sourceEI := by
  have h := PortalFramePilot.portalContract
  exact ⟨h.ownership, h.ordered, h.coverage, h.disjointInteriors, h.canonicalLocations,
    h.memberEnds, h.interiorCuts, h.actionLocations, h.supportLocations,
    h.orientationNormalized, h.supportNormalized, h.positiveMember, h.segmentLengthMatches,
    h.segmentPropertiesMatch, h.positiveSpring⟩

theorem positive_segments (a : ℝ) : positiveSegments (model a) :=
  contract_positive_segments _ _ _ _ _ _ _ (physical_contract a)

/-- No hidden slip or base motion remains in the actual admissible kernel.
    This uses the physical deformation map, not a floating determinant. -/
theorem no_mechanism (a : ℝ) (q : Coordinate (model a) → ℝ)
    (hadmissible : admissible (model a) supports q)
    (hzero : FrameDeformation.deformationMap (model a) q = 0) : q = 0 := by
  obtain ⟨z, rfl⟩ := (lift_image a q).mp hadmissible
  have h (s : Fin 3) (d : Fin 3) := congrFun hzero (Sum.inl (s, d))
  have h00 := h 0 0
  have h01 := h 0 1
  have h02 := h 0 2
  have h20 := h 2 0
  have h21 := h 2 1
  have h22 := h 2 2
  simp only [FrameDeformation.deformationMap, FrameDeformation.segmentDeformation,
    actual_element_motion] at h00 h01 h02 h20 h21 h22
  norm_num [FrameDeformation.memberDeformation, FrameEnergy.relativeRotationLeft,
    FrameEnergy.relativeRotationRight, elementMotion, lift, model, PortalFramePilot.model,
    PortalFramePilot.lengths, Fin.instOfNat, Fin.ofNat', Fin.succ] at h00 h01 h02 h20 h21 h22
  have hz : z = 0 := by
    funext i
    fin_cases i <;> simp [Fin.instOfNat, Fin.ofNat'] at * <;> linarith
  rw [hz]
  have hlift : lift (0 : Fin 6 → ℝ) = 0 := by
    funext i
    fin_cases i <;> rfl
  rw [hlift]
  exact coordinates_total a (0 : Coordinate (model a) → ℝ)

theorem unique_equilibrium (a : ℝ) (q v : Coordinate (model a) → ℝ)
    (hq : equilibrium (model a) actions supports q)
    (hv : equilibrium (model a) actions supports v) : q = v :=
  FrameDeformation.equilibrium_unique_if_no_mechanism _ _ _ _ _ _ _
    (physical_contract a) (no_mechanism a) q v hq hv

theorem accepted_midpoint (a : Rat) (q : PortalChecker.Motion) (r : PortalChecker.Reactions)
    (m u : Rat) (h : PortalChecker.accepts a q r m u = true) :
    (m : ℝ) = (LocalFrameFields.moment
      (segmentDofs (model a) (motion a (fun i => (q i : ℝ))) 1) 6 20000 a a).eval 3 ∧
    (u : ℝ) = (LocalFrameFields.transverseDisplacement
      (segmentDofs (model a) (motion a (fun i => (q i : ℝ))) 1) 6 20000 a a).eval 3 := by
  have valid := acceptance_predicate a q r m u h
  have fields := actual_midpoint (a : ℝ) (fun i => (q i : ℝ))
  rw [fields.1, fields.2]
  constructor
  · rw [valid.2.2.2.1]
    simp [PortalChecker.midpointMoment]
  · rw [valid.2.2.2.2]
    simp [PortalChecker.midpointDisplacement]

theorem accepted_reactions (a : Rat) (q : PortalChecker.Motion) (r : PortalChecker.Reactions)
    (m u : Rat) (h : PortalChecker.accepts a q r m u = true) (i : Fin 6) :
    (r i : ℝ) = residual a (fun j => (q j : ℝ)) (PortalChecker.baseIndex i) := by
  rw [← rational_residual_cast, (acceptance_predicate a q r m u h).2.2.1 i]

/-- One acceptance statement combines actual equilibrium, uniqueness and loaded
    field values. The grouped support interpretation is proved separately below. -/
theorem acceptance_actual_portal (a : Rat) (q : PortalChecker.Motion)
    (r : PortalChecker.Reactions) (m u : Rat) (h : PortalChecker.accepts a q r m u = true) :
    equilibrium (model a) actions supports (motion a (fun i => (q i : ℝ))) ∧
    (∀ v, equilibrium (model a) actions supports v → v = motion a (fun i => (q i : ℝ))) ∧
    (∀ i, (r i : ℝ) = residual a (fun j => (q j : ℝ)) (PortalChecker.baseIndex i)) ∧
    (m : ℝ) = (LocalFrameFields.moment
      (segmentDofs (model a) (motion a (fun i => (q i : ℝ))) 1) 6 20000 a a).eval 3 ∧
    (u : ℝ) = (LocalFrameFields.transverseDisplacement
      (segmentDofs (model a) (motion a (fun i => (q i : ℝ))) 1) 6 20000 a a).eval 3 := by
  have heq := accepted_equilibrium a q r m u h
  exact ⟨heq, fun v hv => unique_equilibrium _ _ _ hv heq,
    accepted_reactions a q r m u h, accepted_midpoint a q r m u h⟩

theorem coordinate_injective (a : ℝ) : Function.Injective (coordinate a) := by
  intro i j h
  have hv := congrArg (motion a (fun k => (k.val : ℝ))) h
  simp only [motion_coordinate] at hv
  apply Fin.ext
  exact_mod_cast hv

theorem motion_basis (a : ℝ) (i : Fin 12) :
    motion a (fun j => if j = i then 1 else 0) = coordinateBasis (model a) (coordinate a i) := by
  classical
  rw [← coordinates_total a (coordinateBasis (model a) (coordinate a i))]
  apply congrArg (motion a)
  funext j
  simp [coordinateBasis, (coordinate_injective a).eq_iff]

theorem actual_stiffness_entry (a : ℝ) (i j : Fin 12) :
    stiffnessEntry (model a) (coordinate a i) (coordinate a j) = K i j := by
  classical
  rw [stiffnessEntry, ← motion_basis, ← motion_basis, actual_stiffness_work]
  simp

theorem actual_force_entry (a : ℝ) (i : Fin 12) :
    forceEntry (model a) actions (coordinate a i) = F a i := by
  classical
  rw [forceEntry, ← motion_basis, actual_force_work]
  simp

def baseHub (i : Fin 6) : Fin 4 := if i.val < 3 then 0 else 3
def baseDirection (i : Fin 6) : Fin 3 := ⟨i.val % 3, by omega⟩

theorem base_coordinate (a : ℝ) (i : Fin 6) :
    coordinate a (PortalChecker.baseIndex i) = .inl (hub a (baseHub i), baseDirection i) := by
  fin_cases i <;> rfl

/-- These are grouped ground actions at the actual A/D hubs, including Kq−F.
    The original AB-start/CD-end support ownership is retained by `supports`. -/
theorem accepted_grouped_reactions (a : Rat) (q : PortalChecker.Motion)
    (r : PortalChecker.Reactions) (m u : Rat) (h : PortalChecker.accepts a q r m u = true) :
    ∃ coefficients : ConstraintIndex supports → ℝ,
      residualFunctional (model a) actions (motion a (fun i => (q i : ℝ))) =
        aggregateReaction (model a) supports coefficients ∧
      ∀ i : Fin 6, groupedGroundAction (model a) supports coefficients
        (hub a (baseHub i)) (baseDirection i) = (r i : ℝ) := by
  classical
  obtain ⟨_, coefficients, hcoefficients⟩ :=
    (equilibrium_iff_reaction_coefficients (model a) actions supports _ (positive_segments a)).mp
      (accepted_equilibrium a q r m u h)
  refine ⟨coefficients, hcoefficients, ?_⟩
  intro i
  rw [groupedGroundAction, ← hcoefficients,
    residual_functional_apply _ _ _ _ (positive_segments a), ← base_coordinate, ← motion_basis,
    actual_residual_work]
  simpa using (accepted_reactions a q r m u h i).symm

#print axioms acceptance_actual_portal
#print axioms accepted_grouped_reactions
#print axioms actual_stiffness_entry
#print axioms actual_force_entry
#print axioms lift_image
#print axioms no_mechanism
#print axioms fixed_inverse

end
end PortalSoundness
