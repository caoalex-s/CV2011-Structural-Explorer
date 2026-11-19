import JointMemberDiagram
import MemberDiagramReport
import HingeFrameSoundness
import FrameSpringSound

namespace JointMemberDiagram.Sound
open RationalFrame MemberDiagram MemberDiagram.Sound

/-- Every piece uses the translations at its two ends and its actual pair of
member-end rotations. The real coordinate x includes either one-sided limit. -/
theorem physical_fields (a : HingeFrame.Assembly) (u : Array Rat) (m : Nat)
    (i : Index a.mesh m) (x : ℝ) :
    let s := segmentAt a.mesh m i
    let v := rotations a u s
    let d := fun k => (localMotion s v k : ℝ)
    let q := (s.cosine : ℝ) * s.vertical
    let qEnd := (s.cosine : ℝ) * s.verticalEnd
    field (polynomial s v false) x = (LocalFrameFields.shear d s.length s.EI q qEnd).eval x ∧
    field (polynomial s v true) x = (LocalFrameFields.moment d s.length s.EI q qEnd).eval x := by
  let j := (selected a.mesh m).get i
  rcases Interpretation.segments_valid a.mesh a.valid j with ⟨_,_,_,_,_,_,_,length,axial,bending,_⟩
  exact source_fields _ _ x (by exact_mod_cast ne_of_gt length)
    (by exact_mod_cast ne_of_gt axial) (by exact_mod_cast ne_of_gt bending)

/-- Start with the original bytes, including claimed section and face moments. -/
theorem hinge_accepted {input output} (h : hingeReport input = some output) :
    ∃ (p : HingeFrame.Wire.HingePacket) (a : HingeFrame.Assembly)
      (sheet : Sheet a.mesh p.query.member (rotations a p.certificate.motion)),
      HingeFrame.Wire.decode input = some p ∧ HingeFrame.compile p.source p.rules = some a ∧
      p.certificate.mechanism = false ∧ HingeFrame.Checked a p.query p.certificate ∧
      p.moments = HingeFrame.Wire.recoveredMoments a p ∧ output = encode sheet ∧
      correctFlags sheet false ∧ correctFlags sheet true := by
  obtain ⟨p,decoded,rest⟩ := Option.bind_eq_some.mp h
  obtain ⟨a,compiled,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next accepted =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', HingeFrame.Wire.checkValue, compiled,
      decide_eq_true_eq, beq_iff_eq] at accepted
    obtain ⟨sheet,built,result⟩ := Option.bind_eq_some.mp rest
    split at result
    next ranks =>
      cases result
      simp only [Bool.and_eq_true] at ranks
      exact ⟨p,a,sheet,decoded,compiled,accepted.1,accepted.2.1.2,accepted.2.2,rfl,
        global_flags ranks.1.1,global_flags ranks.1.2⟩
    next => contradiction
  next => contradiction

theorem spring_accepted {input output} (h : springReport input = some output) :
    ∃ (p : FrameSpring.Wire.Packet) (s : CardinalSpring.System) (w : Certificate)
      (sheet : Sheet s.beam.mesh p.query.member (rotations s.beam w.motion)),
      FrameSpring.Wire.decode input = some p ∧ CardinalSpring.compile p = some s ∧
      (∃ sectionReport, FrameSpring.Wire.checkReport input = some sectionReport) ∧
      CardinalSpring.Equilibrium s (CardinalSpring.matrix s) w ∧ output = encode sheet ∧
      correctFlags sheet false ∧ correctFlags sheet true := by
  obtain ⟨p,decoded,rest⟩ := Option.bind_eq_some.mp h
  obtain ⟨s,compiled,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨sectionReport,ordinary,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨w,solved,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next eqn =>
    obtain ⟨sheet,built,result⟩ := Option.bind_eq_some.mp rest
    split at result
    next ranks =>
      cases result
      simp only [Bool.and_eq_true] at ranks
      exact ⟨p,s,w,sheet,decoded,compiled,⟨sectionReport,by simp [FrameSpring.Wire.checkReport,decoded,ordinary]⟩,
        eqn,rfl,global_flags ranks.1.1,global_flags ranks.1.2⟩
    next => contradiction
  next => contradiction

theorem spring_positive {s w} (h : CardinalSpring.Equilibrium s (CardinalSpring.matrix s) w) :
    let k := CardinalSpring.matrix s
    let free := CardinalSpring.freeRows s
    Matrix.PosDef (fun i j : Fin free.size => ((k[free[i.val]!]!)[free[j.val]!]! : ℝ)) :=
  Algebra.checked_factor_positive _ _ _ h.1

#print axioms physical_fields
#print axioms hinge_accepted
#print axioms spring_accepted
#print axioms spring_positive
end JointMemberDiagram.Sound
