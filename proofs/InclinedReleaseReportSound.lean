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

#print axioms accepted_bytes
#print axioms InclinedRelease.Fields.field_contains
#print axioms InclinedRelease.Fields.reaction_contains
end InclinedRelease.Sound
