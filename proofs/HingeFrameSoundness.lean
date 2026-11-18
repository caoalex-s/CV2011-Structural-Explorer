import HingeFrameWire
import RationalFrameRecovery

namespace HingeFrame
open RationalFrame

/-- The selected section uses the loaded Euler–Bernoulli polynomial evaluated
    with the shared translations and the two segment-owned rotations. -/
theorem checked_fields (a : Assembly) (q : Query) (w : Certificate)
    (checked : Checked a q w) (stable : w.mechanism = false) (query : queryValid a.mesh q = true) :
    ∃ j : Fin a.mesh.segments.size, selectedIndex a.mesh q = some j ∧
      SideContains a.mesh.segments[j.val]! q ∧ ∀ i : Fin 6,
        let s := a.mesh.segments[j.val]!
        (w.readouts[i.val]! : ℝ) = Recovery.fieldValues
          (fun k => (localMotion s (segmentMotion a s w.motion) k : ℝ))
          s.length s.EA s.EI s.cosine s.sine s.vertical s.verticalEnd
          ((s.length * (q.t - s.left) / (s.right - s.left) : Rat) : ℝ) i := by
  obtain ⟨j, selected, contains⟩ := Recovery.checked_selection a.mesh q query
  refine ⟨j, selected, contains, ?_⟩
  intro i
  have equations := checked.2.2.2
  simp only [stable, Bool.false_eq_true, if_false] at equations
  rw [equations.2.2.2.1]
  simp only [sectionValues, selectedSegment, selected, Option.map_some]
  rcases Interpretation.segments_valid a.mesh a.valid j with
    ⟨_, _, _, _, _, _, _, length, axial, bending, _⟩
  apply Recovery.recover_segment_cast
  · exact_mod_cast ne_of_gt length
  · exact_mod_cast ne_of_gt axial
  · exact_mod_cast ne_of_gt bending

/-- The checked positive factor belongs to the constrained matrix assembled
    from the drawing, including the separately owned end rotations. -/
theorem stable_positive (a : Assembly) (q : Query) (w : Certificate)
    (checked : Checked a q w) (stable : w.mechanism = false) :
    let k := tabulate a.size fun i => tabulate a.size (stiffness a i)
    let free := ((List.range a.size).filter fun i => !restrained a i).toArray
    Matrix.PosDef (fun i j : Fin free.size => ((k[free[i.val]!]!)[free[j.val]!]! : ℝ)) := by
  have equations := checked.2.2.2
  simp only [stable, Bool.false_eq_true, if_false] at equations
  exact Algebra.checked_factor_positive _ _ _ equations.1

/-- End moments use the section sign convention. Both signs give zero at a
    released face with neither an applied couple nor a rotational restraint. -/
theorem unloaded_release (a : Assembly) (q : Query) (w : Certificate)
    (checked : Checked a q w) (stable : w.mechanism = false) (i : Fin a.sides.length)
    (unloaded : faceCouple a (faceQuery (a.sides.get i)) = 0)
    (free : restrained a (pointIndex a (faceQuery (a.sides.get i)).member
      (faceQuery (a.sides.get i)).t 2) = false) :
    (sectionValues a (faceQuery (a.sides.get i)) w.motion)[2]! = 0 := by
  have equations := checked.2.2.2
  simp only [stable, Bool.false_eq_true, if_false] at equations
  have balance := (equations.2.2.2.2.2 i).2
  simp only [unloaded, free, Bool.false_eq_true, if_false, add_zero] at balance
  split at balance <;> simpa using balance

end HingeFrame
