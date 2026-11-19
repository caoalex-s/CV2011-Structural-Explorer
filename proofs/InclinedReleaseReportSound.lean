import InclinedReleaseFields

namespace InclinedRelease.Sound
open InclinedFrameIntervalAssembly FrameEnclosure

/-- A successful ABI report identifies one layout obtained from the original
    source and one solution to its real virtual-work equations. The report
    fields are recovered from this same certificate, including the physical
    member end selected for a couple or rotational restraint. -/
theorem accepted_bytes {input output : String} (accepted : Wire.checkReport input = some output) :
    ∃ v l c fields, Wire.decode input = some v ∧ layout v.source v.rules = some l ∧
      verified l v.bits c = true ∧ Wire.resultFields l v.bits c v.query = some fields ∧
      output = String.intercalate "\n" fields ∧
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
    dsimp only at last
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

#print axioms accepted_bytes
#print axioms shared_translation
#print axioms grouped_reaction
#print axioms InclinedRelease.Fields.field_contains
#print axioms InclinedRelease.Fields.reaction_contains
end InclinedRelease.Sound
