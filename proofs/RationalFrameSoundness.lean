import RationalFrameStability
import RationalFrameReactions
import RationalFrameRecovery

/-! Source-level soundness of the generic executable predicate. Every result
    refers to the original-member interpretation of the compiled source.
    No independent matrix, graph, coordinate map, or support mask is assumed. -/
namespace RationalFrameSoundness
open RationalFrame RationalFrame.Interpretation FrameAssemblyModel FrameAssembly
noncomputable section

structure ActualModel (data : Compiled) (valid : PartitionValid data) : Prop where
  distributedLoads : ∀ (i : Fin data.segments.size) (t : ℝ),
    let segment := data.segments[i.val]!
    (model data valid).segmentVerticalStart i +
      ((model data valid).segmentVerticalEnd i - (model data valid).segmentVerticalStart i) *
      (t-(segment.left : ℝ)) / ((segment.right : ℝ)-(segment.left : ℝ)) =
      sourceSegmentIntensity data.source segment t
  geometry : ExactGeometry.GeometryCorrespondence (model data valid) (Geometry.nodePosition data)
    (Geometry.drawingStart data valid) (Geometry.drawingEnd data valid) (cutParameter data)
    (fun member => (data.source.members[member.val]!.EA : ℝ))
    (fun member => (data.source.members[member.val]!.EI : ℝ))
    (Geometry.segmentStartPosition data valid) (Geometry.segmentEndPosition data valid)
  contract : ExactContract (model data valid) (actions data valid) (supports data valid) (cutParameter data)
    (fun member => (memberLength data.source member.val : ℝ))
    (fun member => (data.source.members[member.val]!.EA : ℝ))
    (fun member => (data.source.members[member.val]!.EI : ℝ))
  stiffness : ∀ i j : Fin data.dofs,
    (RationalFrame.stiffnessEntry data i.val j.val : ℝ) =
      FrameAssembly.stiffnessEntry (model data valid) (coordinateEquiv data valid i) (coordinateEquiv data valid j)
  force : ∀ i : Fin data.dofs, (RationalFrame.forceEntry data i.val : ℝ) =
    FrameAssembly.forceEntry (model data valid) (actions data valid) (coordinateEquiv data valid i)
  constraints : ∀ q : Fin data.dofs → ℝ,
    admissible (model data valid) (supports data valid) (motion data valid q) ↔
      ∀ i : Fin data.dofs, blocked data i.val = true → q i = 0

def StableResult (data : Compiled) (valid : PartitionValid data)
    (query : Query) (certificate : Certificate) : Prop :=
  let q := motion data valid (fun i => (certificate.motion[i.val]! : ℝ))
  (equilibrium (model data valid) (actions data valid) (supports data valid) q ∧
    ∀ other, equilibrium (model data valid) (actions data valid) (supports data valid) other → other = q) ∧
  (∃ coefficients : ConstraintIndex (supports data valid) → ℝ,
    ∀ (point : ActivePoint (model data valid)) (direction : Fin 3),
      (certificate.reactions[((coordinateEquiv data valid).symm (.inl (point, direction))).val]! : ℝ) =
        groupedGroundAction (model data valid) (supports data valid) coefficients point direction) ∧
  (∃ segment : Fin data.segments.size, selectedIndex data query = some segment ∧
    SideContains data.segments[segment.val]! query ∧
    ∀ i : Fin 6, (certificate.readouts[i.val]! : ℝ) =
      Recovery.actualValues data valid certificate.motion segment query.t i)

def MechanismResult (data : Compiled) (valid : PartitionValid data) (certificate : Certificate) : Prop :=
  let z := motion data valid (fun i => (certificate.motion[i.val]! : ℝ))
  (admissible (model data valid) (supports data valid) z ∧ z ≠ 0 ∧
    FrameDeformation.deformationMap (model data valid) z = 0) ∧
  (certificate.loadWork : ℝ) = externalWork (model data valid) (actions data valid) z ∧
  (certificate.loadWork ≠ 0 → ¬ ∃ q,
    equilibrium (model data valid) (actions data valid) (supports data valid) q)

/-- Public acceptance yields an actual source-owned frame, its full geometry,
    contract and assembly correspondence, and the appropriate physical result.
    The retained query predicate includes side and unit/sign convention checks.
    Point equality binds the display map to the complete coordinate equivalence. -/
theorem acceptance_actual_frame (source : Source) (query : Query) (certificate : Certificate)
    (accepted : accepts source query certificate = true) :
    sourceValid source = true ∧ ∃ (data : Compiled) (valid : PartitionValid data),
      compileModel source = some data ∧ data.source = source ∧ certificate.points = data.points ∧
      queryValid data query = true ∧ ActualModel data valid ∧
      (if certificate.mechanism then MechanismResult data valid certificate
        else StableResult data valid query certificate) := by
  obtain ⟨sourceChecked, data, compiled, sameSource, valid, samePoints, queryChecked, restrained, result⟩ :=
    acceptance_source source query certificate accepted
  refine ⟨sourceChecked, data, valid, compiled, sameSource, samePoints, queryChecked, ?_, ?_⟩
  · exact ⟨segment_load_from_source data valid, Geometry.correspondence data valid, Contract.exact_contract data valid,
      Assembly.stiffness_entry data valid, Assembly.force_entry data valid,
      Constraints.admissible_finite data valid⟩
  · cases branch : certificate.mechanism with
    | false =>
      simp only [branch, Bool.false_eq_true, ↓reduceIte] at result ⊢
      exact ⟨Stability.checked_unique data valid query certificate restrained result,
        Reactions.checked_grouped_reactions data valid query certificate restrained result,
        Recovery.checked_readouts data valid query certificate queryChecked result⟩
    | true =>
      simp only [branch, ↓reduceIte] at result ⊢
      refine ⟨Stability.checked_mechanism data valid certificate restrained result, ?_,
        Stability.checked_incompatible data valid certificate restrained result⟩
      rw [result.2.2.1]
      exact Equations.load_work data valid certificate.motion

end
end RationalFrameSoundness
