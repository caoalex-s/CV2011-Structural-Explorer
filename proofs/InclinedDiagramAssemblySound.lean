import InclinedDiagramStaticsSound
import InclinedDiagramSound

namespace InclinedDiagram.Statics.Sound
open InclinedFrameSource InclinedFrameBasis InclinedFrameReal InclinedFrameIntervalAssembly
noncomputable section

def globalActions (data : Partition) (motion : Motion data) (i : Fin data.pieces.size) : Fin 6 → ℝ :=
  let seg := data.pieces[i.val]!
  let member := data.source.members[seg.member]!
  let orientation := memberDirection data seg.member
  FrameTransform.toGlobal6 orientation.cosine orientation.sine (LocalFrameFields.endActions
    (pieceMotion data seg motion) (pieceLength data seg) member.EA member.EI
    (orientation.sine*seg.vertical) (orientation.sine*seg.verticalEnd)
    (orientation.cosine*seg.vertical) (orientation.cosine*seg.verticalEnd))

/-- End actions, transmitted spring torques and source lengths use disjoint
coordinates. The last coordinate represents the constant one. -/
def frameState {data : Partition} (motion : Motion data) {count : Nat} (torque : Fin count → ℝ)
    (index : Fin (width data count)) : ℝ :=
  if h : index.val/6 < data.pieces.size then
    globalActions data motion ⟨_,h⟩ ⟨index.val%6,Nat.mod_lt _ (by decide)⟩
  else if h : index.val-6*data.pieces.size < count then torque ⟨_,h⟩
  else if index.val < 6*data.pieces.size+count+data.source.members.size then
    memberLength data (index.val-(6*data.pieces.size+count))
  else 1

theorem end_slot {data : Partition} (motion : Motion data) {count : Nat} (torque : Fin count → ℝ)
    (i : Fin data.pieces.size) (d : Fin 6) :
    atSlot (frameState motion torque) (6*i.val+d.val) = globalActions data motion i d := by
  have bound : 6*i.val+d.val < width data count := by unfold width; omega
  have owner : (6*i.val+d.val)/6 = i.val := by omega
  have component : (6*i.val+d.val)%6 = d.val := by omega
  simp [atSlot,bound,frameState,owner,i.isLt,component]

theorem torque_slot {data : Partition} (motion : Motion data) {count : Nat} (torque : Fin count → ℝ)
    (i : Fin count) : atSlot (frameState motion torque) (6*data.pieces.size+i.val) = torque i := by
  have bound : 6*data.pieces.size+i.val < width data count := by unfold width; omega
  have outside : ¬(6*data.pieces.size+i.val)/6 < data.pieces.size := by omega
  simp [atSlot,bound,frameState,outside,i.isLt]

theorem length_slot {data : Partition} (motion : Motion data) {count : Nat} (torque : Fin count → ℝ)
    (i : Fin data.source.members.size) :
    atSlot (frameState motion torque) (6*data.pieces.size+count+i.val) = memberLength data i.val := by
  let index := 6*data.pieces.size+count+i.val
  have bound : index < width data count := by dsimp [index,width]; omega
  have notEnd : ¬index/6 < data.pieces.size := by dsimp [index]; omega
  have notTorque : ¬index-6*data.pieces.size < count := by dsimp [index]; omega
  have member : index < 6*data.pieces.size+count+data.source.members.size := by dsimp [index]; omega
  change atSlot _ index = _
  simp [atSlot,bound,frameState,notEnd,notTorque,member,index]

theorem constant_slot {data : Partition} (motion : Motion data) {count : Nat} (torque : Fin count → ℝ) :
    atSlot (frameState motion torque) (width data count-1) = 1 := by
  let index := width data count-1
  have bound : index < width data count := by dsimp [index,width]; omega
  have notEnd : ¬index/6 < data.pieces.size := by dsimp [index,width]; omega
  have notTorque : ¬index-6*data.pieces.size < count := by dsimp [index,width]; omega
  have noMember : ¬index < 6*data.pieces.size+count+data.source.members.size := by dsimp [index,width]; omega
  change atSlot _ index = _
  simp [atSlot,bound,frameState,notEnd,notTorque,noMember]

theorem element_terms_zero {data : Partition} (valid : PartitionValid data)
    (motion : Motion data) {count : Nat} (torque : Fin count → ℝ)
    (i : Fin data.pieces.size) (terms : List (Nat × Rat)) (belongs : terms ∈ elementTerms data count i) :
    termsValue (frameState motion torque) terms = 0 := by
  let seg := data.pieces[i.val]!
  let member := data.source.members[seg.member]!
  let direction := memberDirection data seg.member
  let ell := pieceLength data seg
  let L := memberLength data seg.member
  let fraction := (seg.right:ℝ)-seg.left
  let dx := data.source.nodes[member.b]!.x-data.source.nodes[member.a]!.x
  let dy := data.source.nodes[member.b]!.y-data.source.nodes[member.a]!.y
  have positive := piece_properties data valid i
  rcases valid with ⟨source,_,_,_,_,_,_,pieces,_,_,_,_⟩
  let owner : Fin data.source.members.size := ⟨seg.member,(pieces i).1.1⟩
  have directions := ExactGeometry.direction_components _ _ (endpoints_distinct data source owner)
  have hx : L*direction.cosine = (dx:ℝ) := by
    simpa [L,direction,dx,member,owner,endpoints,memberLength,memberDirection,ExactGeometry.dx] using directions.1
  have hy : L*direction.sine = (dy:ℝ) := by
    simpa [L,direction,dy,member,owner,endpoints,memberLength,memberDirection,ExactGeometry.dy] using directions.2
  have xpos : fraction*(dx:ℝ) = ell*direction.cosine := by rw [←hx]; dsimp [ell,pieceLength,L,fraction]; ring
  have ypos : fraction*(dy:ℝ) = ell*direction.sine := by rw [←hy]; dsimp [ell,pieceLength,L,fraction]; ring
  have balance := element_balance (pieceMotion data seg motion) ell member.EA member.EI
    direction.cosine direction.sine seg.vertical seg.verticalEnd (ne_of_gt positive.1)
    (ne_of_gt positive.2.1) (ne_of_gt positive.2.2) (member_normalized data source owner)
  let state := frameState motion torque
  have action (d : Fin 6) : atSlot state (6*i.val+d.val) = globalActions data motion i d :=
    end_slot motion torque i d
  have len : atSlot state (6*data.pieces.size+count+seg.member) = L := length_slot motion torque owner
  have at0 : atSlot state (6*i.val) = globalActions data motion i 0 := action 0
  have at1 : atSlot state (6*i.val+1) = globalActions data motion i 1 := action 1
  have at2 : atSlot state (6*i.val+2) = globalActions data motion i 2 := action 2
  have at3 : atSlot state (6*i.val+3) = globalActions data motion i 3 := action 3
  have at4 : atSlot state (6*i.val+4) = globalActions data motion i 4 := action 4
  have at5 : atSlot state (6*i.val+5) = globalActions data motion i 5 := action 5
  change termsValue state terms = 0
  simp only [elementTerms,List.mem_cons,List.not_mem_nil,or_false] at belongs
  rcases belongs with rfl | rfl | rfl
  · simpa [termsValue,at0,at3,globalActions,forceX,FrameTransform.toGlobal6,ell,seg,direction] using balance.1
  · simp only [termsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      Rat.cast_one,one_mul,at1,at4,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat]
    change globalActions data motion i 1 + (globalActions data motion i 4 +
      fraction*((seg.vertical:ℝ)+seg.verticalEnd)/2 * atSlot state (6*data.pieces.size+count+seg.member)) = 0
    rw [len]
    change _ = 0
    convert balance.2.1 using 1 <;> dsimp [globalActions,FrameTransform.toGlobal6,forceY,ell,pieceLength,L,fraction,seg,direction] <;> ring
  · simp only [termsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      Rat.cast_one,one_mul,at2,at5,at3,at4,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_neg,Rat.cast_ofNat]
    change globalActions data motion i 2 + (globalActions data motion i 5 +
      (fraction*(dx:ℝ)*globalActions data motion i 4 + (-(fraction*(dy:ℝ))*globalActions data motion i 3 +
       (fraction*(fraction*(dx:ℝ))*((seg.vertical:ℝ)+2*seg.verticalEnd)/6)*atSlot state
          (6*data.pieces.size+count+seg.member)))) = 0
    rw [len,xpos,ypos]
    convert balance.2.2 using 1 <;> dsimp [globalActions,FrameTransform.toGlobal6,forceX,forceY,ell,pieceLength,L,fraction,seg,direction] <;> ring

#print axioms element_terms_zero
end
end InclinedDiagram.Statics.Sound
