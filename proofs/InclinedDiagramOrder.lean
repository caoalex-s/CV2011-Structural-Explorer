import InclinedDiagramCoverage

namespace InclinedDiagram.Sound
open FrameEnclosure (Contains)
noncomputable section

def orderMeans (a b : ℝ) : OrderEvidence → Prop
  | .less => a < b
  | .equal => a = b
  | .greater => b < a
  | .unresolved => True

/-- On one piece both rational shear offsets have a common, possibly
irrational baseline. Across pieces the signature premise is equality of
two reduced linear forms on the same solved frame. -/
theorem compare_sound {a b : Candidate} {x y : ℝ}
    (boundsA : Contains a.y x) (boundsB : Contains b.y y)
    (same : a.piece = b.piece → a.station = b.station → x = y)
    (offsets : a.piece = b.piece → ∀ u v, a.shearOffset = some u → b.shearOffset = some v →
      x-y = (u:ℝ)-v)
    (signature : a.signature.isEmpty = false → a.signature = b.signature → x = y) :
    orderMeans x y (compareValues a b) := by
  unfold compareValues
  split
  next eq =>
    simp only [Bool.and_eq_true,beq_iff_eq] at eq
    exact same eq.1 eq.2
  next =>
    split
    next off =>
      obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp off.2.1
      obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp off.2.2
      have diff := offsets off.1 u v hu hv
      simp only [hu,hv,Option.getD_some]
      split
      next lt =>
        have cast : (u:ℝ) < v := by exact_mod_cast lt
        exact (show x < y by linarith)
      next lt =>
        split
        next eq => subst v; exact (show x = y by linarith)
        next eq =>
          have cast : (v:ℝ) < u := by exact_mod_cast lt_of_le_of_ne (le_of_not_gt lt) (Ne.symm eq)
          exact (show y < x by linarith)
    next =>
      split
      next eq =>
        simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at eq
        exact signature eq.1 eq.2
      next =>
        split
        next lt => exact lt_of_le_of_lt boundsA.2 (lt_of_lt_of_le (by exact_mod_cast lt) boundsB.1)
        next =>
          split
          next lt => exact lt_of_le_of_lt boundsB.2 (lt_of_lt_of_le (by exact_mod_cast lt) boundsA.1)
          next =>
            split
            next eq =>
              obtain ⟨al,ah⟩ := boundsA
              obtain ⟨bl,bh⟩ := boundsB
              rw [←eq.1] at ah
              rw [←eq.2.1,←eq.2.2] at bh
              rw [←eq.2.2] at bl
              exact (show x = y by linarith)
            next => trivial

/-- A false flag has a strict counterexample. For a true flag the checker
has resolved every comparison, so all ties satisfy the extremum predicate. -/
theorem flags_mean {a : Candidate} {all : List Candidate} (value : Candidate → ℝ)
    (comparison : ∀ b ∈ all, orderMeans (value a) (value b) (compareValues a b))
    {maximum flag : Bool} (reported : isExtreme maximum a all = some flag) :
    flag = true ↔ ∀ b ∈ all, if maximum then value b ≤ value a else value a ≤ value b := by
  cases maximum <;> unfold isExtreme at reported <;> dsimp only at reported
  all_goals split at reported
  all_goals first
    | next bad =>
      cases reported
      simp only [Bool.false_eq_true,false_iff]
      intro hypothesis
      obtain ⟨b,mem,order⟩ := List.mem_map.mp (List.contains_iff_mem.mp bad)
      have actual := comparison b mem
      rw [order] at actual
      exact (not_lt_of_ge (hypothesis b mem)) actual
    | next nobad =>
      split at reported
      · cases reported
      next resolved =>
        cases reported
        simp only [true_iff]
        intro b mem
        have actual := comparison b mem
        have present := List.mem_map_of_mem (compareValues a) mem
        cases eq : compareValues a b <;> rw [eq] at actual present <;>
          first | exact le_of_lt actual | exact le_of_eq actual | exact le_of_eq actual.symm |
            exact False.elim (nobad (List.contains_iff_mem.mpr present)) |
            exact False.elim (resolved (List.contains_iff_mem.mpr present))

#print axioms flags_mean
end
end InclinedDiagram.Sound
