import InclinedDiagramAssemblySound

namespace InclinedDiagram.Sound
open InclinedDiagram.Statics
open InclinedDiagram.Statics.Sound
open InclinedFrameSource InclinedFrameReal InclinedFrameBasis InclinedFrameIntervalAssembly
open FrameEnclosure (Contains)
noncomputable section

theorem singleton_form {n} (state : Fin n → ℝ) {r : Row} {i : Fin n} {v : Rat}
    (width : r.size = n) (pureForm : onlyCoefficient r i.val = some v) :
    value state r = (v:ℝ)*state i := by
  unfold onlyCoefficient at pureForm
  split at pureForm
  next check =>
    cases pureForm
    have eq := eq_of_beq check
    unfold value
    apply Finset.sum_eq_single i
    · intro j _ ne
      have ji : j.val ≠ i.val := fun h => ne (Fin.ext h)
      have hi : i.val < r.size := by simpa only [width] using i.isLt
      have hj : j.val < r.size := by simpa only [width] using j.isLt
      have atJ := congrArg (fun x : Row => x[j.val]!) eq
      have zero : r[j.val]! = 0 := by simpa [getElem!_pos,Array.set!,hi,hj,ji,Ne.symm ji] using atJ
      simp [zero]
    · simp
  next => cases pureForm

theorem start_projection (data : Partition) (h : PartitionValid data) (motion : Motion data)
    (i : Fin data.pieces.size) :
    let seg := data.pieces[i.val]!
    let member := data.source.members[seg.member]!
    let a := data.source.nodes[member.a]!
    let b := data.source.nodes[member.b]!
    ((a.y:ℝ)-b.y)*globalActions data motion i 0 + ((b.x:ℝ)-a.x)*globalActions data motion i 1 =
      (physicalState data motion i).L*(physicalState data motion i).V := by
  rcases h with ⟨src,_,_,_,_,_,_,pieces,_,_,_,_⟩
  let seg := data.pieces[i.val]!
  let owner : Fin data.source.members.size := ⟨seg.member,(pieces i).1.1⟩
  let orientation := memberDirection data seg.member
  let L := memberLength data seg.member
  have eq := ExactGeometry.direction_components _ _ (endpoints_distinct data src owner)
  have hx : L*orientation.cosine =
      (data.source.nodes[data.source.members[seg.member]!.b]!.x:ℝ)-
      data.source.nodes[data.source.members[seg.member]!.a]!.x := by
    simpa [L,orientation,owner,endpoints,memberLength,memberDirection,ExactGeometry.dx] using eq.1
  have hy : L*orientation.sine =
      (data.source.nodes[data.source.members[seg.member]!.b]!.y:ℝ)-
      data.source.nodes[data.source.members[seg.member]!.a]!.y := by
    simpa [L,orientation,owner,endpoints,memberLength,memberDirection,ExactGeometry.dy] using eq.2
  have unit : orientation.cosine^2+orientation.sine^2=1 := member_normalized data src owner
  let v := (physicalState data motion i).V
  dsimp only
  rw [←show -((data.source.nodes[data.source.members[seg.member]!.b]!.y:ℝ)-
    data.source.nodes[data.source.members[seg.member]!.a]!.y) = _ from neg_sub _ _,←hy,←hx]
  change -(L*orientation.sine)*(_-orientation.sine*v)+(L*orientation.cosine)*(_+orientation.cosine*v) = L*v
  linear_combination L*v*unit

structure Forms {n} (state : Fin n → ℝ) (p : InclinedDiagram.Piece) (s : State) : Prop where
  shear_width : p.scaledShear.size = n
  moment_width : p.initialMoment.size = n
  length_slot : ∃ i : Fin n, i.val = p.lengthColumn ∧ state i = s.L
  shear_value : value state p.scaledShear = s.L*s.V
  moment_value : value state p.initialMoment = s.M

#print axioms start_projection
end
end InclinedDiagram.Sound
