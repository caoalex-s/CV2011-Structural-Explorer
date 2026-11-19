import InclinedReleaseWire
import InclinedFrameIntervalAssemblySound
import FrameIntervalSolveSound

namespace InclinedRelease.Sound
open InclinedFrameSource InclinedFrameIntervalAssembly FrameEnclosure
noncomputable section

/-- Unit virtual motions use the original joint's translation and the
    selected member end's rotation. A roller uses its real trigonometric tangent. -/
def unitMotion (l : Layout) (col : Fin l.basis.columns.size) : InclinedFrameReal.Motion l.expanded :=
  fun p d =>
    let owner := if d.val == 2 then p.val else l.parent[p.val]!
    InclinedFrameIntervalBasisSound.synthesizedValues l.basis.points[owner]!
      (InclinedFrameIntervalBasis.pointAmplitude l.expanded l.basis col owner) d

theorem point_contains {l : Layout} {bits : Nat} {c : Certificate l.expanded l.basis}
    (proj : Projections l bits c) (p : Nat) (col : Fin l.basis.columns.size) (d : Fin 3) :
    Contains (pointColumnAt c p col d) (InclinedFrameReal.pointMotion l.expanded (unitMotion l col) p d) := by
  unfold pointColumnAt InclinedFrameReal.pointMotion
  split
  next hin =>
    have h := proj.1 ⟨p, hin⟩ col
    simp only [pointColumn, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
    obtain ⟨shared, hs, own, ho, eq⟩ := h
    rw [← Option.some.inj eq]
    by_cases rotation : d.val == 2
    · simpa [unitMotion, rotation] using InclinedFrameIntervalBasisSound.synthesize_contains ho d
    · simpa [unitMotion, rotation] using InclinedFrameIntervalBasisSound.synthesize_contains hs d
  next => simp [Contains]

def projection (l : Layout) (p : Fin l.expanded.pieces.size) (d : Fin 6)
    (col : Fin l.basis.columns.size) : ℝ :=
  InclinedFrameReal.pieceMotion l.expanded l.expanded.pieces[p.val]! (unitMotion l col) d

def matrix (l : Layout) (row col : Fin l.basis.columns.size) : ℝ :=
  ∑ p : Fin l.expanded.pieces.size, ∑ i : Fin 6, projection l p i row *
    (∑ j : Fin 6, LocalFrameFields.stiffness
      (InclinedFrameReal.pieceLength l.expanded l.expanded.pieces[p.val]!)
      (l.expanded.source.members[l.expanded.pieces[p.val]!.member]!.EA : ℝ)
      (l.expanded.source.members[l.expanded.pieces[p.val]!.member]!.EI : ℝ) i j * projection l p j col)

def force (l : Layout) (row : Fin l.basis.columns.size) : ℝ :=
  (∑ p : Fin l.expanded.pieces.size, ∑ i : Fin 6,
    projection l p i row * InclinedFrameReal.pieceLoad l.expanded l.expanded.pieces[p.val]! i) +
  ∑ a : Fin l.expanded.source.loads.size, ∑ i : Fin 3,
    InclinedFrameReal.pointMotion l.expanded (unitMotion l row)
      (locate l.expanded l.expanded.source.loads[a.val]!.member l.expanded.source.loads[a.val]!.t) i *
        InclinedFrameAssemblySound.sourceAction l.expanded a i

theorem equilibrium {l : Layout} {bits : Nat} {c : Certificate l.expanded l.basis}
    (accepted : verified l bits c = true) :
    ∃ z, FrameMatrixResidual.action (matrix l) z = force l ∧
      (∀ i, Contains (c.solve.solution i) (z i)) ∧
      ∀ other, FrameMatrixResidual.action (matrix l) other = force l → other = z := by
  simp only [verified, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨geometry, proj, loads, assembly⟩, solve⟩ := accepted
  have localMap (p : Fin l.expanded.pieces.size) (col : Fin l.basis.columns.size) :
      ∀ i, Contains (c.localColumns p col i) (projection l p i col) := by
    obtain ⟨_, hc, hs, _⟩ := InclinedFrameIntervalGeometrySound.piece_contains (geometry p)
    exact FrameIntervalTransformSound.localPiece_contains (proj.2 p col) hc hs
      (point_contains proj _ col) (point_contains proj _ col)
  apply FrameIntervalSolveSound.check_sound solve
  · intro row col
    apply FrameIntervalAssemblySound.matrixEntry_contains (assembly.1 row col)
    · intro p i j
      exact (InclinedFrameIntervalGeometrySound.piece_contains (geometry p)).2.2.2 i j
    · exact fun p i j => localMap p j i
  · intro row
    apply FrameIntervalAssemblySound.forceEntry_contains (assembly.2 row)
    · exact fun p i => InclinedFrameIntervalLoadSound.pieceLoad_contains (geometry p) (loads.1 p) i
    · exact fun p i j => localMap p j i
    · exact fun a i => InclinedFrameIntervalLoadSound.pointAction_contains (loads.2 a i)
    · exact fun a i col => point_contains proj _ col i

def motion (l : Layout) (z : Fin l.basis.columns.size → ℝ) : InclinedFrameReal.Motion l.expanded :=
  fun p d => ∑ j, unitMotion l j p d * z j

theorem nodal_motion {l : Layout} {bits : Nat} {c : Certificate l.expanded l.basis}
    (proj : Projections l bits c) {z : Fin l.basis.columns.size → ℝ}
    (sol : ∀ j, Contains (c.solve.solution j) (z j)) {p : Nat} {out : Fin 3 → FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.nodalMotion bits c p = some out) :
    ∀ i, Contains (out i) (InclinedFrameReal.pointMotion l.expanded (motion l z) p i) := by
  simp only [InclinedFrameIntervalRecovery.nodalMotion, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
  obtain ⟨x, hx, y, hy, rot, hr, rfl⟩ := h
  have hx' := FrameIntervalVectorSound.dot_contains hx (fun j => point_contains proj p j 0) sol
  have hy' := FrameIntervalVectorSound.dot_contains hy (fun j => point_contains proj p j 1) sol
  have hr' := FrameIntervalVectorSound.dot_contains hr (fun j => point_contains proj p j 2) sol
  intro i
  by_cases hp : p < l.expanded.points.size
  · fin_cases i <;> simp_all [InclinedFrameReal.pointMotion, motion]
  · simp only [InclinedFrameReal.pointMotion, dif_neg hp, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero] at hx' hy' hr' ⊢
    fin_cases i <;> assumption

end
end InclinedRelease.Sound
