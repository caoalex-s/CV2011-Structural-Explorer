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

end
end InclinedDiagram.Statics.Sound
