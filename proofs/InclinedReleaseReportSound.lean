import InclinedReleaseFields
import FrameIntervalAccuracySound

namespace InclinedRelease.Sound
open InclinedFrameIntervalAssembly FrameEnclosure

/-- A successful ABI report identifies one layout obtained from the original
    source and one solution to its real virtual-work equations. The report
    fields are recovered from this same certificate, including the physical
    member end selected for a couple or rotational restraint. -/
theorem accepted_bytes {input output : String} (accepted : Wire.checkReport input = some output) :
    ∃ v l c fields, Wire.decode input = some v ∧ layout v.source v.rules = some l ∧
      verified l v.bits c = true ∧ Wire.readValues l v.bits c v.query = some fields ∧
      output = Wire.encode fields ∧
      ∃ z, FrameMatrixResidual.action (matrix l) z = force l ∧
        (∀ i, Contains (c.solve.solution i) (z i)) ∧
        (∀ other, FrameMatrixResidual.action (matrix l) other = force l → other = z) ∧
        Fields.NodeEnclosures v.bits c (motion l z) := by
  obtain ⟨v, decoded, checked⟩ := Option.bind_eq_some.mp accepted
  unfold Wire.report at checked
  obtain ⟨l, source, remainder⟩ := Option.bind_eq_some.mp checked
  obtain ⟨proposal, _, remainder⟩ := Option.bind_eq_some.mp remainder
  obtain ⟨c, _, remainder⟩ := Option.bind_eq_some.mp remainder
  dsimp only at remainder
  split at remainder
  next ok =>
    obtain ⟨fields, hf, last⟩ := Option.bind_eq_some.mp remainder
    try dsimp only at last
    split at last
    next =>
      have value := Option.some.inj last
      obtain ⟨z, eqn, sol, unique⟩ := equilibrium ok
      have gates := ok
      simp only [verified, Bool.and_eq_true, decide_eq_true_eq] at gates
      exact ⟨v, l, c, fields, decoded, source, ok, hf, value.symm,
        z, eqn, sol, unique, fun hm => nodal_motion gates.1.2.1 sol hm⟩
    next => cases last
  next => cases remainder

/-- For either global translation every coincident member end at the
    source joint receives exactly the same real displacement. -/
theorem shared_translation (l : Layout) (z : Fin l.basis.columns.size → ℝ)
    (a b : Fin l.expanded.points.size) (same : l.parent[a.val]! = l.parent[b.val]!)
    (d : Fin 3) (translation : d.val ≠ 2) : motion l z a d = motion l z b d := by
  simp [motion, unitMotion, translation, same]

/-- Component-wise end residuals add to the reaction at the physical joint.
    Internal forces between its coincident end points cancel in this sum. -/
theorem grouped_reaction {l : Layout} {bits : Nat} {c : Certificate l.expanded l.basis}
    (good : verified l bits c = true) {z : Fin l.basis.columns.size → ℝ}
    (enclosed : ∀ i, Contains (c.solve.solution i) (z i))
    {raw : Fin l.expanded.points.size → Fin 3 → FrameIntervalOps.Bounds}
    (calculated : ∀ i d, InclinedFrameIntervalReactions.reaction bits c i d = some (raw i d))
    {p : Nat} {d : Fin 3} {out : FrameIntervalOps.Bounds}
    (grouped : Wire.groupReaction l bits p d raw = some out) :
    Contains out (∑ i : Fin l.expanded.points.size, if l.parent[i.val]! = p then
      InclinedFrameReal.groupedReaction l.expanded (motion l z) i d else 0) := by
  simp only [verified, Bool.and_eq_true, decide_eq_true_eq] at good
  obtain ⟨⟨geometry, proj, loads, _⟩, _⟩ := good
  apply FrameIntervalAssemblySound.sumTerms_contains grouped
  intro i box term
  by_cases belongs : l.parent[i.val]! = p
  · simp [belongs] at term ⊢
    subst box
    exact Fields.reaction_contains l.valid (motion l z) geometry
      (fun hm => nodal_motion proj enclosed hm) loads (calculated i d)
  · simp [belongs] at term ⊢
    subst box
    simp [Contains]

/-- The serialized interval and its midpoint concern the same real value.
    Quantities use the tolerances of the established inclined-frame protocol. -/
def Reported (quantity : Fin 9) (box : FrameIntervalOps.Bounds) (actual : ℝ) : Prop :=
  Contains box actual ∧ |actual - (FrameIntervalAccuracy.midpoint box : ℝ)| ≤
    (FrameIntervalAccuracy.absoluteTolerance quantity : ℝ) +
      (FrameIntervalAccuracy.relativeTolerance : ℝ) * |actual|

def FieldReported (l : Layout) (physical : InclinedFrameReal.Motion l.expanded)
    (q : RationalFrame.Query) (d : Fin 6) (box : FrameIntervalOps.Bounds) : Prop :=
  ∃ index : Fin l.expanded.pieces.size, InclinedFrameIntervalRecovery.selectedPiece l.expanded q = some index ∧
    InclinedFrameIntervalRecovery.SideContains l.expanded.pieces[index.val]! q ∧
    Reported (InclinedFrameIntervalOutputs.fieldQuantity d) box
      (InclinedFrameReal.fieldValues l.expanded l.expanded.pieces[index.val]! physical q.t d)

def ReportMeaning {l : Layout} {bits : Nat} {c : Wire.Cert l} {q : RationalFrame.Query}
    (v : Wire.Values l bits c q) (z : Fin l.basis.columns.size → ℝ) : Prop :=
  let physical := motion l z
  (∀ d, FieldReported l physical q d (v.fields d).value) ∧
  (∀ p d, Reported (InclinedFrameIntervalOutputs.reactionQuantity d) (v.reactions p d).value
    (∑ i : Fin l.expanded.points.size, if l.parent[i.val]! = Wire.expandedPoint l p then
      InclinedFrameReal.groupedReaction l.expanded physical i d else 0)) ∧
  (∀ i, let side := (Wire.faceSides l)[i.val]!
    let f := v.faces i
    let atPoint := InclinedFrameReal.pointMotion l.expanded physical (Wire.facePoint l side)
    Reported 4 (f.motion.value 0) (atPoint 0) ∧ Reported 5 (f.motion.value 1) (atPoint 1) ∧
    Reported 3 (f.motion.value 2) (atPoint 2) ∧ FieldReported l physical (HingeFrame.faceQuery side) 2 f.moment.value)

theorem reported {k : Fin 9} {box : FrameIntervalOps.Bounds} {actual : ℝ}
    (accuracy : FrameIntervalAccuracy.check k box = true) (enclosed : Contains box actual) :
    Reported k box actual := ⟨enclosed, FrameIntervalAccuracySound.check_error accuracy enclosed⟩

/-- The same motion supplies every exported field, joint reaction, face
    displacement, absolute rotation and signed section moment. -/
theorem accepted_readouts {input output : String} (accepted : Wire.checkReport input = some output) :
    ∃ v l c values z, Wire.decode input = some v ∧ layout v.source v.rules = some l ∧
      Wire.readValues l v.bits c v.query = some values ∧ output = Wire.encode values ∧
      FrameMatrixResidual.action (matrix l) z = force l ∧
      (∀ other, FrameMatrixResidual.action (matrix l) other = force l → other = z) ∧
      ReportMeaning values z := by
  obtain ⟨v, l, c, values, decoded, source, good, outputs, encoded, z, eqn, sol, unique, nodes⟩ := accepted_bytes accepted
  refine ⟨v, l, c, values, z, decoded, source, outputs, encoded, eqn, unique, ?_⟩
  have gates := good
  simp only [verified, Bool.and_eq_true, decide_eq_true_eq] at gates
  obtain ⟨⟨geometry, _, loads, _⟩, _⟩ := gates
  have field {query : RationalFrame.Query} {d : Fin 6}
      (r : Wire.Accurate (InclinedFrameIntervalOutputs.fieldQuantity d) (InclinedFrameIntervalRecovery.field v.bits c query d)) :
      FieldReported l (motion l z) query d r.value := by
    obtain ⟨i, selected, side, contained⟩ := Fields.field_contains l.valid (motion l z) geometry nodes loads r.computed
    exact ⟨i, selected, side, reported r.accuracy contained⟩
  refine ⟨fun d => field (values.fields d), ?_, ?_⟩
  · intro p d
    exact reported (values.reactions p d).accuracy
      (grouped_reaction good sol (fun i k => (values.raw i k).computed) (values.reactions p d).computed)
  · intro i
    let f := values.faces i
    have contained := nodes f.motion.computed
    exact ⟨reported f.ux (contained 0), reported f.uy (contained 1), reported f.rotation (contained 2), field f.moment⟩

#print axioms accepted_readouts

#print axioms accepted_bytes
#print axioms shared_translation
#print axioms grouped_reaction
#print axioms InclinedRelease.Fields.field_contains
#print axioms InclinedRelease.Fields.reaction_contains
end InclinedRelease.Sound
