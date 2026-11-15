import InclinedFrameIntervalReactions
import InclinedFrameIntervalRecoverySound

/-! Grouped reaction containment uses global virtual unit motion, including
    every original point action. Support duplicates do not create new shares. -/
namespace InclinedFrameIntervalReactionsSound
open InclinedFrameSource InclinedFrameBasis InclinedFrameGlobalBasis
open InclinedFrameIntervalAssembly InclinedFrameIntervalEquilibrium FrameEnclosure
open InclinedFrameIntervalReactions
noncomputable section

def virtualMotion {data : Partition} (point : Fin data.points.size) (direction : Fin 3) :
    InclinedFrameReal.Motion data := fun index component => if index = point ∧ component = direction then 1 else 0

theorem virtualPoint_contains {data : Partition} (point : Fin data.points.size) (direction : Fin 3)
    (endpoint : Nat) (component : Fin 3) :
    Contains (virtualPoint point direction endpoint component)
      (InclinedFrameReal.pointMotion data (virtualMotion point direction) endpoint component) := by
  by_cases hin : endpoint < data.points.size
  · simp [virtualPoint, virtualMotion, InclinedFrameReal.pointMotion, hin, Fin.ext_iff, Contains]
  · have hne : endpoint ≠ point.val := by
      intro equal
      apply hin
      simpa only [equal] using point.isLt
    simp [virtualPoint, virtualMotion, InclinedFrameReal.pointMotion, hin, hne, Contains]

def actualPieceWork (data : Partition) (motion variation : InclinedFrameReal.Motion data)
    (index : Fin data.pieces.size) : ℝ :=
  let segment := data.pieces[index.val]!
  let member := data.source.members[segment.member]!
  let direction := InclinedFrameReal.memberDirection data segment.member
  let actions := LocalFrameFields.endActions (InclinedFrameReal.pieceMotion data segment motion)
    (InclinedFrameReal.pieceLength data segment) member.EA member.EI
    (direction.sine*segment.vertical) (direction.sine*segment.verticalEnd)
    (direction.cosine*segment.vertical) (direction.cosine*segment.verticalEnd)
  ∑ i, InclinedFrameReal.pieceMotion data segment variation i * actions i

theorem pieceWork_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (hbasis : GlobalBasisValid data basis)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (hprojection : ProjectionChecks bits certificate) (hload : LoadChecks bits certificate)
    {values : Fin basis.columns.size → ℝ}
    (hvalues : ∀ column, Contains (certificate.solve.solution column) (values column))
    {point : Fin data.points.size} {direction : Fin 3} {index : Fin data.pieces.size}
    {out : FrameIntervalOps.Bounds} (h : pieceWork bits certificate point direction index = some out) :
    Contains out (actualPieceWork data (embed data basis (liftCoordinates hbasis values))
      (virtualMotion point direction) index) := by
  unfold pieceWork at h
  dsimp only at h
  obtain ⟨motion, hmotion, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨axialStart, has, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨shearStart, hss, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨momentStart, hms, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨axialEnd, hae, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨shearEnd, hse, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨momentEnd, hme, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨variation, hvariation, hdot⟩ := Option.bind_eq_some.mp h
  have hd := InclinedFrameIntervalRecoverySound.localMotion_contains hbasis hgeometry hprojection hvalues hmotion
  have ha := InclinedFrameIntervalRecoverySound.endAction_contains hpartition hbasis hgeometry hload hd has
  have hb := InclinedFrameIntervalRecoverySound.endAction_contains hpartition hbasis hgeometry hload hd hss
  have hc := InclinedFrameIntervalRecoverySound.endAction_contains hpartition hbasis hgeometry hload hd hms
  have hd' := InclinedFrameIntervalRecoverySound.endAction_contains hpartition hbasis hgeometry hload hd hae
  have he := InclinedFrameIntervalRecoverySound.endAction_contains hpartition hbasis hgeometry hload hd hse
  have hf := InclinedFrameIntervalRecoverySound.endAction_contains hpartition hbasis hgeometry hload hd hme
  obtain ⟨_, hcosine, hsine, _⟩ := InclinedFrameIntervalGeometrySound.piece_contains (hgeometry index)
  have hv := FrameIntervalTransformSound.localPiece_contains hvariation hcosine hsine
    (virtualPoint_contains point direction _) (virtualPoint_contains point direction _)
  apply FrameIntervalVectorSound.dot_contains hdot hv
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa using hd'
  · simpa using he
  · simpa using hf

theorem point_action_unit {data : Partition} (hpartition : PartitionValid data)
    (point : Fin data.points.size) (direction : Fin 3) (index : Fin data.source.loads.size) :
    InclinedFrameReal.pointLoadWork data index (virtualMotion point direction) =
      if locate data data.source.loads[index.val]!.member data.source.loads[index.val]!.t = point.val
      then InclinedFrameAssemblySound.sourceAction data index direction else 0 := by
  have hlocation := (load_location hpartition index).1.2.1
  unfold InclinedFrameReal.pointLoadWork InclinedFrameAssemblySound.sourceAction
  dsimp only
  simp only [InclinedFrameReal.pointMotion, dif_pos hlocation, virtualMotion, Fin.ext_iff]
  split_ifs <;> fin_cases direction <;> simp_all

theorem appliedAction_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) {certificate : Certificate data basis}
    (hload : LoadChecks bits certificate) (point : Fin data.points.size) (direction : Fin 3)
    (index : Fin data.source.loads.size) :
    Contains (appliedAction certificate point direction index)
      (InclinedFrameReal.pointLoadWork data index (virtualMotion point direction)) := by
  rw [point_action_unit hpartition]
  unfold appliedAction
  dsimp only
  split
  · exact InclinedFrameIntervalLoadSound.pointAction_contains (hload.2 index direction)
  · simp [Contains]

theorem total_piece_work {data : Partition} (hpartition : PartitionValid data)
    (motion variation : InclinedFrameReal.Motion data) :
    (∑ index, actualPieceWork data motion variation index) =
      InclinedFrameReal.stiffnessWork data motion variation -
        ∑ index : Fin data.pieces.size, ∑ i : Fin 6,
          InclinedFrameReal.pieceLoad data data.pieces[index.val]! i *
            InclinedFrameReal.pieceMotion data data.pieces[index.val]! variation i := by
  have localIdentity (index : Fin data.pieces.size) :
      actualPieceWork data motion variation index =
        (∑ i : Fin 6, ∑ j : Fin 6,
          InclinedFrameReal.pieceMotion data data.pieces[index.val]! variation i *
            InclinedFrameAssemblySound.sourceStiffness data index i j *
            InclinedFrameReal.pieceMotion data data.pieces[index.val]! motion j) -
        ∑ i : Fin 6, InclinedFrameReal.pieceLoad data data.pieces[index.val]! i *
          InclinedFrameReal.pieceMotion data data.pieces[index.val]! variation i := by
    have hp := InclinedFrameReal.piece_properties data hpartition index
    dsimp only [actualPieceWork]
    simp_rw [LocalFrameFields.end_actions_from_fields _ _ _ _ _ _ _ _
      (ne_of_gt hp.1) (ne_of_gt hp.2.1) (ne_of_gt hp.2.2)]
    simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp_rw [localIdentity]
  rw [Finset.sum_sub_distrib]
  rfl

theorem reaction_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (hbasis : GlobalBasisValid data basis)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (hprojection : ProjectionChecks bits certificate) (hload : LoadChecks bits certificate)
    {values : Fin basis.columns.size → ℝ}
    (hvalues : ∀ column, Contains (certificate.solve.solution column) (values column))
    {point : Fin data.points.size} {direction : Fin 3} {out : FrameIntervalOps.Bounds}
    (h : reaction bits certificate point direction = some out) :
    Contains out (InclinedFrameReal.groupedReaction data
      (embed data basis (liftCoordinates hbasis values)) point direction) := by
  simp only [reaction, Option.bind_eq_bind, Option.bind_eq_some] at h
  obtain ⟨elementWork, helements, externalWork, hexternal, hout⟩ := h
  have he : Contains elementWork (∑ index, actualPieceWork data
      (embed data basis (liftCoordinates hbasis values)) (virtualMotion point direction) index) := by
    apply FrameIntervalAssemblySound.sumTerms_contains helements
    intro index bounds hterm
    exact pieceWork_contains hpartition hbasis hgeometry hprojection hload hvalues hterm
  have hx : Contains externalWork (∑ index,
      InclinedFrameReal.pointLoadWork data index (virtualMotion point direction)) := by
    apply FrameIntervalAssemblySound.sumTerms_contains hexternal
    intro index bounds hterm
    have heq := Option.some.inj hterm
    subst bounds
    exact appliedAction_contains hpartition hload point direction index
  have hresult := executable_subtract_contains hout he hx
  rw [total_piece_work hpartition] at hresult
  convert hresult using 1
  simp only [InclinedFrameReal.groupedReaction, InclinedFrameReal.residualWork,
    InclinedFrameReal.externalWork, virtualMotion]
  ring

end
end InclinedFrameIntervalReactionsSound
