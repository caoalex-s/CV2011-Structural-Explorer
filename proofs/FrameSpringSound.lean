import FrameSpringWire
import InclinedReleaseReportSound
import FrameTransform

namespace FrameSpring.Sound
open InclinedRelease InclinedRelease.Sound InclinedFrameIntervalAssembly FrameEnclosure
noncomputable section

def physicalMatrix (l : Layout) (ks : Array Rat) (row col : Fin l.basis.columns.size) : ℝ :=
  InclinedRelease.Sound.matrix l row col + (coupling l ks row col : ℝ)

def gap (l : Layout) (physical : InclinedFrameReal.Motion l.expanded) (side : Nat) : ℝ :=
  InclinedFrameReal.pointMotion l.expanded physical (InclinedRelease.Wire.facePoint l side) 2 -
    InclinedFrameReal.pointMotion l.expanded physical (InclinedRelease.Wire.faceNode l side) 2

theorem unit_rotation (l : Layout) (col : Fin l.basis.columns.size) (p : Nat) :
    InclinedFrameReal.pointMotion l.expanded (unitMotion l col) p 2 =
      (InclinedFrameIntervalBasis.pointAmplitude l.expanded l.basis col p 2 : ℝ) := by
  by_cases h : p < l.expanded.points.size
  · simp [InclinedFrameReal.pointMotion, h, unitMotion, InclinedFrameIntervalBasisSound.synthesizedValues]
  · simp [InclinedFrameReal.pointMotion, h, InclinedFrameIntervalBasis.pointAmplitude]

/-- In physical coordinates the entry is the Hessian of the same quadratic
spring potential whose derivative gives the two equal and opposite actions. -/
theorem coupling_physical (l : Layout) (ks : Array Rat) (r c : Fin l.basis.columns.size) :
    (coupling l ks r c : ℝ) =
      ∑ i : Fin l.sides.size, (ks[l.sides[i.val]!]! : ℝ) *
        gap l (unitMotion l r) l.sides[i.val]! * gap l (unitMotion l c) l.sides[i.val]! := by
  simp [coupling, relativeColumn, gap, unit_rotation]

theorem spring_energy_law (k memberRotation referenceRotation : ℝ) :
    HasDerivAt (FrameTransform.relativePotential k 0 0) (k * (memberRotation - referenceRotation))
      (memberRotation - referenceRotation) := by
  simpa using FrameTransform.potential_derivative k 0 0 (memberRotation - referenceRotation)

theorem equilibrium {l : Layout} {ks : Array Rat} {bits : Nat} {c : Certificate l.expanded l.basis}
    (accepted : FrameSpring.verified l ks bits c = true) :
    ∃ z, FrameMatrixResidual.action (physicalMatrix l ks) z = force l ∧
      (∀ i, Contains (c.solve.solution i) (z i)) ∧
      ∀ other, FrameMatrixResidual.action (physicalMatrix l ks) other = force l → other = z := by
  simp only [FrameSpring.verified, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨geometry, proj, loads, assembly⟩, solve⟩ := accepted
  have localMap (p : Fin l.expanded.pieces.size) (col : Fin l.basis.columns.size) :
      ∀ i, Contains (c.localColumns p col i) (projection l p i col) := by
    obtain ⟨_, hc, hs, _⟩ := InclinedFrameIntervalGeometrySound.piece_contains (geometry p)
    exact FrameIntervalTransformSound.localPiece_contains (proj.2 p col) hc hs
      (point_contains proj _ col) (point_contains proj _ col)
  apply FrameIntervalSolveSound.check_sound solve
  · intro row col
    obtain ⟨beam, hb, ha⟩ := Option.bind_eq_some.mp (assembly.1 row col)
    apply executable_add_contains ha _ (by simp [Contains] : Contains _ (coupling l ks row col : ℝ))
    apply FrameIntervalAssemblySound.matrixEntry_contains hb
    · intro p i j
      exact (InclinedFrameIntervalGeometrySound.piece_contains (geometry p)).2.2.2 i j
    · exact fun p i j => localMap p j i
  · intro row
    apply FrameIntervalAssemblySound.forceEntry_contains (assembly.2 row)
    · exact fun p i => InclinedFrameIntervalLoadSound.pieceLoad_contains (geometry p) (loads.1 p) i
    · exact fun p i j => localMap p j i
    · exact fun a i => InclinedFrameIntervalLoadSound.pointAction_contains (loads.2 a i)
    · exact fun a i col => point_contains proj _ col i

theorem grouped_reaction {l : Layout} {ks : Array Rat} {bits : Nat} {c : Certificate l.expanded l.basis}
    (good : FrameSpring.verified l ks bits c = true) {z : Fin l.basis.columns.size → ℝ}
    (enclosed : ∀ i, Contains (c.solve.solution i) (z i))
    {raw : Fin l.expanded.points.size → Fin 3 → FrameIntervalOps.Bounds}
    (calculated : ∀ i d, InclinedFrameIntervalReactions.reaction bits c i d = some (raw i d))
    {p : Nat} {d : Fin 3} {out : FrameIntervalOps.Bounds}
    (grouped : InclinedRelease.Wire.groupReaction l bits p d raw = some out) :
    Contains out (∑ i : Fin l.expanded.points.size, if l.parent[i.val]! = p then
      InclinedFrameReal.groupedReaction l.expanded (motion l z) i d else 0) := by
  simp only [FrameSpring.verified, Bool.and_eq_true, decide_eq_true_eq] at good
  obtain ⟨⟨geometry, proj, loads, _⟩, _⟩ := good
  apply FrameIntervalAssemblySound.sumTerms_contains grouped
  intro i box term
  by_cases belongs : l.parent[i.val]! = p
  · simp [belongs] at term ⊢
    subst box
    exact InclinedRelease.Fields.reaction_contains l.valid (motion l z) geometry
      (fun hm => nodal_motion proj enclosed hm) loads (calculated i d)
  · simp [belongs] at term ⊢
    subst box
    simp [Contains]


theorem field_readouts {l : Layout} {ks : Array Rat} {bits : Nat} {c : InclinedRelease.Wire.Cert l}
    {q : RationalFrame.Query} (values : InclinedRelease.Wire.Values l bits c q)
    (good : FrameSpring.verified l ks bits c = true) {z : Fin l.basis.columns.size → ℝ}
    (sol : ∀ i, Contains (c.solve.solution i) (z i))
    (nodes : Fields.NodeEnclosures bits c (motion l z)) : ReportMeaning values z := by
  have gates := good
  simp only [FrameSpring.verified, Bool.and_eq_true, decide_eq_true_eq] at gates
  obtain ⟨⟨geometry, _, loads, _⟩, _⟩ := gates
  have field {query : RationalFrame.Query} {d : Fin 6}
      (r : InclinedRelease.Wire.Accurate (InclinedFrameIntervalOutputs.fieldQuantity d) (InclinedFrameIntervalRecovery.field bits c query d)) :
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
    exact ⟨reported f.ux (contained 0), reported f.uy (contained 1), reported f.rotation (contained 2), field (query := HingeFrame.faceQuery (InclinedRelease.Wire.faceSides l)[i.val]!) (d := 2) f.moment⟩


theorem transfer_contains {l : Layout} {bits : Nat} {c : InclinedRelease.Wire.Cert l}
    {z : Fin l.basis.columns.size → ℝ} (nodes : Fields.NodeEnclosures bits c (motion l z))
    {side : Nat} {k : Rat} {out : FrameIntervalOps.Bounds × FrameIntervalOps.Bounds}
    (done : FrameSpring.Wire.springValues l bits c side k = some out) :
    Reported 3 out.1 (gap l (motion l z) side) ∧ Reported 2 out.2 (k * gap l (motion l z) side) := by
  simp only [FrameSpring.Wire.springValues, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at done
  obtain ⟨own, ho, ref, hr, slip, _, transfer, _, eq⟩ := done
  cases eq
  have delta := executable_subtract_contains slip.computed (nodes ho 2) (nodes hr 2)
  exact ⟨reported slip.accuracy delta, reported transfer.accuracy
    (executable_multiply_contains transfer.computed (by simp [Contains]) delta)⟩

theorem accepted_readouts {input output : String} (accepted : FrameSpring.Wire.checkReport input = some output) :
    ∃ v l ks c fields transfers z, FrameSpring.Wire.decode input = some v ∧
      resolve v.source v.rules = some (l, ks) ∧
      output = FrameSpring.Wire.encodeSprings l ks v.bits c (q := v.query) fields transfers ∧
      FrameMatrixResidual.action (physicalMatrix l ks) z = force l ∧
      (∀ other, FrameMatrixResidual.action (physicalMatrix l ks) other = force l → other = z) ∧
      ReportMeaning fields z ∧
      (∀ i, let side := (FrameSpring.Wire.activeSides l ks)[i.val]!
        Reported 3 ((transfers i).value.1) (gap l (motion l z) side) ∧
        Reported 2 ((transfers i).value.2) ((ks[side]! : ℝ) * gap l (motion l z) side)) := by
  obtain ⟨v, decoded, valid⟩ := Option.bind_eq_some.mp accepted
  unfold FrameSpring.Wire.report at valid
  obtain ⟨⟨l, ks⟩, resolved, rest⟩ := Option.bind_eq_some.mp valid
  obtain ⟨proposal, _, rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨c, _, rest⟩ := Option.bind_eq_some.mp rest
  dsimp only at rest
  split at rest
  next good =>
    obtain ⟨fields, _, rest⟩ := Option.bind_eq_some.mp rest
    obtain ⟨transfers, _, last⟩ := Option.bind_eq_some.mp rest
    try dsimp only at last
    split at last
    next =>
      obtain ⟨z, eqn, sol, unique⟩ := equilibrium good
      have gates := good
      simp only [FrameSpring.verified, Bool.and_eq_true, decide_eq_true_eq] at gates
      have nodes : Fields.NodeEnclosures v.bits c (motion l z) := fun h => nodal_motion gates.1.2.1 sol h
      exact ⟨v, l, ks, c, fields, transfers, z, decoded, resolved, (Option.some.inj last).symm,
        eqn, unique, field_readouts fields good sol nodes, fun i => transfer_contains nodes (transfers i).computed⟩
    next => cases last
  next => cases rest

#print axioms accepted_readouts
#print axioms coupling_physical
#print axioms spring_energy_law
end
end FrameSpring.Sound
