import InclinedReleaseSound
import InclinedFrameIntervalReactionsSound

/-! The existing member field and residual calculations can operate on any
    enclosed physical point motion. The released-frame solver supplies that
    premise from its shared translation and member-owned rotation columns. -/
namespace InclinedRelease.Fields
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly FrameEnclosure
open InclinedFrameIntervalRecoverySound (checked_selection)
open InclinedFrameIntervalReactions
open InclinedFrameIntervalReactionsSound (actualPieceWork virtualMotion virtualPoint_contains appliedAction_contains total_piece_work)
noncomputable section

def NodeEnclosures {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (certificate : Certificate data basis) (physical : InclinedFrameReal.Motion data) : Prop :=
  ∀ {point : Nat} {out : Fin 3 → FrameIntervalOps.Bounds},
    InclinedFrameIntervalRecovery.nodalMotion bits certificate point = some out →
    ∀ i, Contains (out i) (InclinedFrameReal.pointMotion data physical point i)

theorem localMotion_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (physical : InclinedFrameReal.Motion data) {certificate : Certificate data basis}
    (hgeometry : GeometryChecks bits certificate) (nodal : NodeEnclosures bits certificate physical)
    {index : Fin data.pieces.size} {out : Fin 6 → FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.localMotion bits certificate index = some out) :
    ∀ i, Contains (out i) (InclinedFrameReal.pieceMotion data data.pieces[index.val]!
      physical i) := by
  simp only [InclinedFrameIntervalRecovery.localMotion, Option.bind_eq_bind, Option.bind_eq_some] at h
  obtain ⟨first, hfirst, second, hsecond, hout⟩ := h
  obtain ⟨_, hc, hs, _⟩ := InclinedFrameIntervalGeometrySound.piece_contains (hgeometry index)
  exact FrameIntervalTransformSound.localPiece_contains hout hc hs
    (nodal hfirst)
    (nodal hsecond)

theorem endAction_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (physical : InclinedFrameReal.Motion data)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (hload : LoadChecks bits certificate)
    {index : Fin data.pieces.size} {motion : Fin 6 → FrameIntervalOps.Bounds}
    (hmotion : ∀ i, Contains (motion i) (InclinedFrameReal.pieceMotion data data.pieces[index.val]!
      physical i))
    {component : Fin 6} {out : FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.endAction bits certificate index motion component = some out) :
    let segment := data.pieces[index.val]!
    let member := data.source.members[segment.member]!
    let direction := InclinedFrameReal.memberDirection data segment.member
    Contains out (LocalFrameFields.endActions
      (InclinedFrameReal.pieceMotion data segment physical)
      (InclinedFrameReal.pieceLength data segment) member.EA member.EI
      (direction.sine*segment.vertical) (direction.sine*segment.verticalEnd)
      (direction.cosine*segment.vertical) (direction.cosine*segment.verticalEnd) component) := by
  dsimp only
  have hp := InclinedFrameReal.piece_properties data hpartition index
  rw [LocalFrameFields.end_actions_from_fields _ _ _ _ _ _ _ _
    (ne_of_gt hp.1) (ne_of_gt hp.2.1) (ne_of_gt hp.2.2)]
  obtain ⟨elastic, helastic, hout⟩ := Option.bind_eq_some.mp h
  have hcoefficients := (InclinedFrameIntervalGeometrySound.piece_contains (hgeometry index)).2.2.2
  have helasticContains := FrameIntervalVectorSound.dot_contains helastic
    (fun j => hcoefficients component j) hmotion
  have hloadContains := InclinedFrameIntervalLoadSound.pieceLoad_contains
    (hgeometry index) (hload.1 index) component
  exact executable_subtract_contains hout helasticContains hloadContains

def sourceInputs (data : Partition) (physical : InclinedFrameReal.Motion data) (index : Fin data.pieces.size) (parameter : Rat) : Fin 15 → ℝ :=
  let segment := data.pieces[index.val]!
  let member := data.source.members[segment.member]!
  let direction := InclinedFrameReal.memberDirection data segment.member
  let length := InclinedFrameReal.pieceLength data segment
  FrameIntervalRecoverySound.inputs
    (InclinedFrameReal.pieceMotion data segment physical)
    length member.EA member.EI
    (direction.sine*segment.vertical) (direction.sine*segment.verticalEnd)
    (direction.cosine*segment.vertical) (direction.cosine*segment.verticalEnd)
    (length*((parameter : ℝ)-segment.left)/((segment.right : ℝ)-segment.left))
    direction.cosine direction.sine

theorem fieldInputs_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (physical : InclinedFrameReal.Motion data)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (nodal : NodeEnclosures bits certificate physical) (hload : LoadChecks bits certificate)
    {index : Fin data.pieces.size} {parameter : Rat} {out : Fin 15 → FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.fieldInputs bits certificate index parameter = some out) :
    ∀ i, Contains (out i) (sourceInputs data physical index parameter i) := by
  unfold InclinedFrameIntervalRecovery.fieldInputs at h
  dsimp only at h
  obtain ⟨motion, hmotion, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨actionX, hactionX, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨actionY, hactionY, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨actionMoment, hactionMoment, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨loads, hloads, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨slopes, hslopes, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨properties, hproperties, h⟩ := Option.bind_eq_some.mp h
  unfold InclinedFrameIntervalRecovery.loadComponents at hloads
  obtain ⟨left, hleft, hloads⟩ := Option.bind_eq_some.mp hloads
  obtain ⟨right, hright, hloads⟩ := Option.bind_eq_some.mp hloads
  obtain ⟨p, hp, hloads⟩ := Option.bind_eq_some.mp hloads
  obtain ⟨pEnd, hpEnd, hloads⟩ := Option.bind_eq_some.mp hloads
  obtain ⟨q, hq, hloads⟩ := Option.bind_eq_some.mp hloads
  obtain ⟨qEnd, hqEnd, hloads⟩ := Option.bind_eq_some.mp hloads
  have loadsEquality := Option.some.inj hloads
  subst loads
  unfold InclinedFrameIntervalRecovery.loadSlopes at hslopes
  dsimp only at hslopes
  obtain ⟨pChange, hpChange, hslopes⟩ := Option.bind_eq_some.mp hslopes
  obtain ⟨qChange, hqChange, hslopes⟩ := Option.bind_eq_some.mp hslopes
  obtain ⟨dp, hdp, hslopes⟩ := Option.bind_eq_some.mp hslopes
  obtain ⟨dq, hdq, hslopes⟩ := Option.bind_eq_some.mp hslopes
  have slopesEquality := Option.some.inj hslopes
  subst slopes
  unfold InclinedFrameIntervalRecovery.positionMaterial at hproperties
  obtain ⟨offset, hoffset, hproperties⟩ := Option.bind_eq_some.mp hproperties
  obtain ⟨x, hx, hproperties⟩ := Option.bind_eq_some.mp hproperties
  obtain ⟨EA, hEA, hproperties⟩ := Option.bind_eq_some.mp hproperties
  obtain ⟨EI, hEI, hproperties⟩ := Option.bind_eq_some.mp hproperties
  have propertiesEquality := Option.some.inj hproperties
  subst properties
  have hout := Option.some.inj h
  subst out
  obtain ⟨hL, hc, hs, _⟩ := InclinedFrameIntervalGeometrySound.piece_contains (hgeometry index)
  have hd := localMotion_contains physical hgeometry nodal hmotion
  have hax := endAction_contains hpartition physical hgeometry hload hd hactionX
  have hay := endAction_contains hpartition physical hgeometry hload hd hactionY
  have ham := endAction_contains hpartition physical hgeometry hload hd hactionMoment
  have hl := executable_point_contains hleft
  have hr := executable_point_contains hright
  have hp0 := executable_multiply_contains hp hs hl
  have hp1 := executable_multiply_contains hpEnd hs hr
  have hq0 := executable_multiply_contains hq hc hl
  have hq1 := executable_multiply_contains hqEnd hc hr
  have hdpContains := executable_divide_contains hdp (executable_subtract_contains hpChange hp1 hp0) hL
  have hdqContains := executable_divide_contains hdq (executable_subtract_contains hqChange hq1 hq0) hL
  have hxContains := executable_multiply_contains hx hL (executable_point_contains hoffset)
  have hEAContains := executable_point_contains hEA
  have hEIContains := executable_point_contains hEI
  intro i
  fin_cases i
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hax
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hay
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using ham
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hd 0
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hd 1
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hd 2
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hp0
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hdpContains
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hq0
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hdqContains
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs, Rat.cast_div, Rat.cast_sub, mul_div_assoc] using hxContains
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hEAContains
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hEIContains
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hc
  · simpa [InclinedFrameIntervalRecovery.inputVector, sourceInputs, FrameIntervalRecoverySound.inputs] using hs

theorem field_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (physical : InclinedFrameReal.Motion data)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (nodal : NodeEnclosures bits certificate physical) (hload : LoadChecks bits certificate)
    {query : RationalFrame.Query} {component : Fin 6} {out : FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.field bits certificate query component = some out) :
    ∃ index : Fin data.pieces.size,
      InclinedFrameIntervalRecovery.selectedPiece data query = some index ∧
      InclinedFrameIntervalRecovery.SideContains data.pieces[index.val]! query ∧
      Contains out (InclinedFrameReal.fieldValues data data.pieces[index.val]!
        physical query.t component) := by
  by_cases hquery : InclinedFrameIntervalRecovery.queryValid data query = true
  · obtain ⟨index, hselected, hside⟩ := InclinedFrameIntervalRecoverySound.checked_selection data query hquery
    have hbody : (InclinedFrameIntervalRecovery.fieldInputs bits certificate index query.t >>= fun inputs =>
        FrameIntervalRecovery.field bits inputs component) = some out := by
      simpa [InclinedFrameIntervalRecovery.field, hquery, hselected] using h
    obtain ⟨inputs, hinputs, hfield⟩ := Option.bind_eq_some.mp hbody
    have hi := fieldInputs_contains hpartition physical hgeometry nodal hload hinputs
    have hp := InclinedFrameReal.piece_properties data hpartition index
    have hresult := FrameIntervalRecoverySound.field_contains
      (ne_of_gt hp.1) (ne_of_gt hp.2.1) (ne_of_gt hp.2.2) hi hfield
    refine ⟨index, hselected, hside, ?_⟩
    simpa only [FrameIntervalRecoverySound.actualFields, InclinedFrameReal.fieldValues] using hresult
  · simp [InclinedFrameIntervalRecovery.field, hquery] at h

theorem pieceWork_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (physical : InclinedFrameReal.Motion data)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (nodal : NodeEnclosures bits certificate physical) (hload : LoadChecks bits certificate)
    {point : Fin data.points.size} {direction : Fin 3} {index : Fin data.pieces.size}
    {out : FrameIntervalOps.Bounds} (h : pieceWork bits certificate point direction index = some out) :
    Contains out (actualPieceWork data physical
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
  have hd := localMotion_contains physical hgeometry nodal hmotion
  have ha := endAction_contains hpartition physical hgeometry hload hd has
  have hb := endAction_contains hpartition physical hgeometry hload hd hss
  have hc := endAction_contains hpartition physical hgeometry hload hd hms
  have hd' := endAction_contains hpartition physical hgeometry hload hd hae
  have he := endAction_contains hpartition physical hgeometry hload hd hse
  have hf := endAction_contains hpartition physical hgeometry hload hd hme
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

theorem reaction_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (physical : InclinedFrameReal.Motion data)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (nodal : NodeEnclosures bits certificate physical) (hload : LoadChecks bits certificate)
    {point : Fin data.points.size} {direction : Fin 3} {out : FrameIntervalOps.Bounds}
    (h : reaction bits certificate point direction = some out) :
    Contains out (InclinedFrameReal.groupedReaction data
      physical point direction) := by
  simp only [reaction, Option.bind_eq_bind, Option.bind_eq_some] at h
  obtain ⟨elementWork, helements, externalWork, hexternal, hout⟩ := h
  have he : Contains elementWork (∑ index, actualPieceWork data
      physical (virtualMotion point direction) index) := by
    apply FrameIntervalAssemblySound.sumTerms_contains helements
    intro index bounds hterm
    exact pieceWork_contains hpartition physical hgeometry nodal hload hterm
  have hx : Contains externalWork (∑ index,
      InclinedFrameReal.pointLoadWork data index (virtualMotion point direction)) := by
    apply FrameIntervalAssemblySound.sumTerms_contains hexternal
    intro index bounds hterm
    have heq := Option.some.inj hterm
    subst bounds
    exact appliedAction_contains hpartition hload point direction index
  have hresult := executable_subtract_contains hout he hx
  rw [total_piece_work hpartition] at hresult
  rw [sub_sub] at hresult
  exact hresult

end
end InclinedRelease.Fields
