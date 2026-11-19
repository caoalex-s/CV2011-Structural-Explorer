import JointMemberDiagram
import MemberDiagramReport
import HingeFrameSoundness
import FrameSpringSound

namespace JointMemberDiagram.Sound
open RationalFrame MemberDiagram MemberDiagram.Sound
open scoped BigOperators Matrix
noncomputable section

/-- Every piece uses the translations at its two ends and its actual pair of
member-end rotations. The real coordinate x includes either one-sided limit. -/
theorem physical_fields (a : HingeFrame.Assembly) (u : Array Rat) (m : Nat)
    (agrees : SameActions a m u) (i : Index a.mesh m) (x : ℝ) :
    let s := segmentAt a.mesh m i
    let v := rotations a u s
    let d := fun k => (localMotion s v k : ℝ)
    let q := (s.cosine : ℝ) * s.vertical
    let qEnd := (s.cosine : ℝ) * s.verticalEnd
    field (polynomial s (memberMotion a m u) false) x = (LocalFrameFields.shear d s.length s.EI q qEnd).eval x ∧
    field (polynomial s (memberMotion a m u) true) x = (LocalFrameFields.moment d s.length s.EI q qEnd).eval x := by
  let j := (selected a.mesh m).get i
  rcases Interpretation.segments_valid a.mesh a.valid j with ⟨_,_,_,_,_,_,_,length,axial,bending,_⟩
  let s := segmentAt a.mesh m i
  have equal (flag : Bool) : polynomial s (memberMotion a m u) flag = polynomial s (rotations a u s) flag := by
    cases flag <;> simp [polynomial,(agrees i).1,(agrees i).2,s]
  dsimp only
  rw [equal, equal]
  exact source_fields _ _ x (by exact_mod_cast ne_of_gt length)
    (by exact_mod_cast ne_of_gt axial) (by exact_mod_cast ne_of_gt bending)

theorem rendered {a m u output} (h : render a m u = some output) :
    (SameActions a m u ∧ EndValues a m u) ∧ ∃ sheet : Sheet a.mesh m (memberMotion a m u),
      output = encode sheet ∧ correctFlags sheet false ∧ correctFlags sheet true := by
  unfold render at h
  split at h
  next agrees =>
    obtain ⟨sheet,_,result⟩ := Option.bind_eq_some.mp h
    split at result
    next ranks =>
      cases result
      simp only [Bool.and_eq_true] at ranks
      exact ⟨agrees,sheet,rfl,global_flags ranks.1.1,global_flags ranks.1.2⟩
    next => contradiction
  next => contradiction

/-- Start with the original bytes, including claimed section and face moments. -/
theorem hinge_accepted {input output} (h : hingeReport input = some output) :
    ∃ (p : HingeFrame.Wire.HingePacket) (a : HingeFrame.Assembly)
      (sheet : Sheet a.mesh p.query.member (memberMotion a p.query.member p.certificate.motion)),
      HingeFrame.Wire.decode input = some p ∧ HingeFrame.compile p.source p.rules = some a ∧
      p.certificate.mechanism = false ∧ HingeFrame.Checked a p.query p.certificate ∧
      p.moments = HingeFrame.Wire.recoveredMoments a p ∧ (SameActions a p.query.member p.certificate.motion ∧ EndValues a p.query.member p.certificate.motion) ∧ output = encode sheet ∧
      correctFlags sheet false ∧ correctFlags sheet true := by
  obtain ⟨p,decoded,rest⟩ := Option.bind_eq_some.mp h
  obtain ⟨a,compiled,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next accepted =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', HingeFrame.Wire.checkValue, compiled,
      decide_eq_true_eq, beq_iff_eq] at accepted
    obtain ⟨agrees,sheet,outputEq,flags⟩ := rendered rest
    exact ⟨p,a,sheet,decoded,compiled,accepted.1,accepted.2.1.2,accepted.2.2,agrees,outputEq,flags⟩
  next => contradiction

theorem spring_accepted {input output} (h : springReport input = some output) :
    ∃ (p : FrameSpring.Wire.Packet) (s : CardinalSpring.System) (w : Certificate)
      (sheet : Sheet s.beam.mesh p.query.member (memberMotion s.beam p.query.member w.motion)),
      FrameSpring.Wire.decode input = some p ∧ CardinalSpring.compile p = some s ∧
      (∃ sectionReport, FrameSpring.Wire.checkReport input = some sectionReport) ∧
      CardinalSpring.Equilibrium s (CardinalSpring.matrix s) w ∧ (SameActions s.beam p.query.member w.motion ∧ EndValues s.beam p.query.member w.motion) ∧ output = encode sheet ∧
      correctFlags sheet false ∧ correctFlags sheet true := by
  obtain ⟨p,decoded,rest⟩ := Option.bind_eq_some.mp h
  obtain ⟨s,compiled,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨sectionReport,ordinary,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨w,solved,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next eqn =>
    obtain ⟨agrees,sheet,outputEq,flags⟩ := rendered rest
    exact ⟨p,s,w,sheet,decoded,compiled,⟨sectionReport,by simp [FrameSpring.Wire.checkReport,decoded,ordinary]⟩,
      eqn,agrees,outputEq,flags⟩
  next => contradiction

theorem spring_positive {s w} (h : CardinalSpring.Equilibrium s (CardinalSpring.matrix s) w) :
    let k := CardinalSpring.matrix s
    let free := CardinalSpring.freeRows s
    Matrix.PosDef (fun i j : Fin free.size => ((k[free[i.val]!]!)[free[j.val]!]! : ℝ)) :=
  Algebra.checked_factor_positive _ _ _ h.1

/-- The accepted free motion is the unique real solution of the assembled
cardinal equations. Fixed coordinates have their prescribed zero values. -/
theorem unique_free_motion {s w} (h : CardinalSpring.Equilibrium s (CardinalSpring.matrix s) w) :
    let free := CardinalSpring.freeRows s
    let k : Matrix (Fin free.size) (Fin free.size) ℝ := fun i j =>
      (((CardinalSpring.matrix s)[free[i.val]!]!)[free[j.val]!]! : ℝ)
    let u := fun i : Fin free.size => (w.motion[free[i.val]!]! : ℝ)
    let f := fun i : Fin free.size => ((CardinalSpring.loads s)[free[i.val]!]! : ℝ)
    k.mulVec u = f ∧ ∀ other, k.mulVec other = f → other = u := by
  intro free k u f
  have eqn : k.mulVec u = f := by
    funext i
    have row := h.2.2.2.2.2 i
    rw [Algebra.sumFin_eq_sum] at row
    simpa [Matrix.mulVec,dotProduct,k,u,f,free] using congrArg (fun z : Rat => (z : ℝ)) row
  refine ⟨eqn,?_⟩
  intro other sol
  by_contra ne
  have diff : other-u ≠ 0 := sub_ne_zero.mpr ne
  have zero : k.mulVec (other-u) = 0 := by rw [Matrix.mulVec_sub, sol, eqn, sub_self]
  have pos := (spring_positive h).2 (other-u) diff
  change 0 < _ ⬝ᵥ k.mulVec (other-u) at pos
  simp [zero] at pos

theorem original_incidence {p s} (compiled : CardinalSpring.compile p = some s) :
    CardinalSpring.ConnectedRows s := by
  obtain ⟨⟨layout,ks⟩,_,rest⟩ := Option.bind_eq_some.mp compiled
  obtain ⟨mesh,_,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next =>
    dsimp only at rest
    split at rest
    next valid => cases rest; exact valid.2
    next => contradiction
  next => contradiction

/-- Recover the two rotations from the original member incidence, including
the reference member explicitly selected at a shared node. -/
theorem source_gap {p s} (compiled : CardinalSpring.compile p = some s)
    (u : Array Rat) (side : Nat) (listed : side ∈ s.beam.sides) :
    let face := HingeFrame.faceQuery side
    let source := s.beam.mesh.source
    let node := InclinedRelease.endpoint source.members[face.member]! side
    let ref := HingeFrame.reference source node
    let refT : Rat := if source.members[ref]!.a = node then 0 else 1
    CardinalSpring.gap s u side =
      u[HingeFrame.pointIndex s.beam face.member face.t 2]! - u[HingeFrame.pointIndex s.beam ref refT 2]! := by
  obtain ⟨_,_,own,reference⟩ := original_incidence compiled side listed
  dsimp only
  rw [own,reference]
  rfl

theorem resolved_system {p s} (compiled : CardinalSpring.compile p = some s) :
    ∃ layout, FrameSpring.resolve p.source p.rules = some (layout,s.stiffnesses) ∧
      compileModel p.source = some s.beam.mesh ∧ s.beam.sides = layout.sides.toList := by
  obtain ⟨⟨layout,ks⟩,resolved,rest⟩ := Option.bind_eq_some.mp compiled
  obtain ⟨mesh,built,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next =>
    dsimp only at rest
    split at rest
    next => cases rest; exact ⟨layout,resolved,built,rfl⟩
    next => contradiction
  next => contradiction

theorem free_complete (s : CardinalSpring.System) (i : Nat) :
    i ∈ (CardinalSpring.freeRows s).toList ↔ i < s.beam.size ∧ HingeFrame.restrained s.beam i = false := by
  simp [CardinalSpring.freeRows,List.mem_filter,Bool.not_eq_true]

/-- Derivative of k Δθ²/2 under a unit variation of coordinate row.
A second variation in column col yields exactly the entry added to K. -/
theorem energy_stiffness (s : CardinalSpring.System) (side row col : Nat) (delta : ℝ) :
    let k : ℝ := s.stiffnesses[side]!
    let b : ℝ := CardinalSpring.gapColumn s side row
    let c : ℝ := CardinalSpring.gapColumn s side col
    HasDerivAt (fun t : ℝ => k*(delta+t*b)^2/2) (k*delta*b) 0 ∧
    HasDerivAt (fun t : ℝ => k*(delta+t*c)*b) (k*b*c) 0 := by
  intro k b c
  constructor
  · have d := ((((hasDerivAt_id (0:ℝ)).mul_const b).const_add delta).pow 2).const_mul k
    convert d.div_const 2 using 1 <;> simp [id] <;> ring
  · have d := ((((hasDerivAt_id (0:ℝ)).mul_const c).const_add delta).const_mul k).mul_const b
    convert d using 1 <;> simp [id] <;> ring

theorem end_field {f : Cubic} {x : Rat} :
    field f (x : ℝ) = (evalRat f x : ℝ) := by simp [field,evalRat]

theorem signed_face {s w} (eqn : CardinalSpring.Equilibrium s (CardinalSpring.matrix s) w)
    (i : Fin s.beam.sides.length) :
    let side := s.beam.sides.get i
    let q := HingeFrame.faceQuery side
    let M := (HingeFrame.sectionValues s.beam q w.motion)[2]!
    let T := s.stiffnesses[side]! * CardinalSpring.gap s w.motion side
    let row := HingeFrame.pointIndex s.beam q.member q.t 2
    let C := HingeFrame.faceCouple s.beam q + (if HingeFrame.restrained s.beam row then w.reactions[row]! else 0)
    M = if q.right then T-C else C-T := by
  intro side q M T row C
  have balance := eqn.2.2.2.2.1 i
  change (if q.right then -M else M) + T = C at balance
  split <;> rename_i hq <;> simp [hq] at balance <;> linarith

/-- Use local x = 0 on a first face and local x = L on a last face.
The equality includes external and support couples on the selected face. -/
theorem spring_endpoint {s w m} (eqn : CardinalSpring.Equilibrium s (CardinalSpring.matrix s) w)
    (ends : EndValues s.beam m w.motion) (i : Index s.beam.mesh m)
    (j : Fin s.beam.sides.length) (first : Bool)
    (sideEq : s.beam.sides.get j = if first then 2*m else 2*m+1)
    (boundary : if first then (segmentAt s.beam.mesh m i).left = 0 else (segmentAt s.beam.mesh m i).right = 1) :
    let side := s.beam.sides.get j
    let q := HingeFrame.faceQuery side
    let piece := segmentAt s.beam.mesh m i
    let f := polynomial piece (memberMotion s.beam m w.motion) true
    let T := s.stiffnesses[side]! * CardinalSpring.gap s w.motion side
    let C := HingeFrame.faceCouple s.beam q + (if HingeFrame.restrained s.beam
      (HingeFrame.pointIndex s.beam q.member q.t 2) then w.reactions[HingeFrame.pointIndex s.beam q.member q.t 2]! else 0)
    evalRat f (if first then 0 else piece.length) = if q.right then T-C else C-T := by
  dsimp only
  have law := signed_face eqn j
  dsimp only at law
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] at sideEq boundary ⊢
  · rw [(ends i).2 boundary, ← sideEq]; exact law
  · rw [(ends i).1 boundary, ← sideEq]; exact law

theorem unloaded_hinge_endpoint {a q w m} (checked : HingeFrame.Checked a q w)
    (stable : w.mechanism = false) (ends : EndValues a m w.motion) (i : Index a.mesh m)
    (j : Fin a.sides.length) (first : Bool)
    (sideEq : a.sides.get j = if first then 2*m else 2*m+1)
    (boundary : if first then (segmentAt a.mesh m i).left = 0 else (segmentAt a.mesh m i).right = 1)
    (unloaded : HingeFrame.faceCouple a (HingeFrame.faceQuery (a.sides.get j)) = 0)
    (free : let face := HingeFrame.faceQuery (a.sides.get j)
      HingeFrame.restrained a (HingeFrame.pointIndex a face.member face.t 2) = false) :
    let piece := segmentAt a.mesh m i
    evalRat (polynomial piece (memberMotion a m w.motion) true) (if first then 0 else piece.length) = 0 := by
  dsimp only
  have law := HingeFrame.unloaded_release a q w checked stable j unloaded free
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] at sideEq boundary ⊢
  · rw [(ends i).2 boundary, ← sideEq]; exact law
  · rw [(ends i).1 boundary, ← sideEq]; exact law

theorem accepted_dispatch {input output} (h : checkReport input = some output) :
    (input.startsWith "CV2011_HINGE_1\n" = true ∧ hingeReport input = some output) ∨
    (input.startsWith "CV2011_HINGE_1\n" = false ∧ springReport input = some output) := by
  unfold checkReport at h
  split at h <;> simp_all

#print axioms spring_endpoint
#print axioms unloaded_hinge_endpoint
#print axioms accepted_dispatch
#print axioms unique_free_motion
#print axioms source_gap
#print axioms resolved_system
#print axioms original_incidence
#print axioms energy_stiffness
#print axioms signed_face
#print axioms physical_fields
#print axioms hinge_accepted
#print axioms spring_accepted
#print axioms spring_positive
end
end JointMemberDiagram.Sound
