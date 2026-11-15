import InclinedFrameIntervalRecovery
import InclinedFrameIntervalEquilibrium
import FrameIntervalRecoverySound

/-! Recovery inputs refer to the same physical motion as the checked reduced
    solution. In particular, nodal intervals are derived from source columns. -/
namespace InclinedFrameIntervalRecoverySound
open InclinedFrameSource InclinedFrameBasis InclinedFrameGlobalBasis
open InclinedFrameIntervalAssembly InclinedFrameIntervalEquilibrium FrameEnclosure
noncomputable section

def pointEvaluation (data : Partition) (point : Nat) (component : Fin 3) :
    InclinedFrameReal.Motion data →ₗ[ℝ] ℝ where
  toFun motion := InclinedFrameReal.pointMotion data motion point component
  map_add' first second := congrFun (InclinedFrameReal.pointMotion_add data first second point) component
  map_smul' scalar motion := congrFun (InclinedFrameReal.pointMotion_smul data scalar motion point) component

theorem source_point_expansion {data : Partition} {basis : GlobalBasis}
    (h : GlobalBasisValid data basis) (values : Fin basis.columns.size → ℝ)
    (point : Nat) (component : Fin 3) :
    InclinedFrameReal.pointMotion data (embed data basis (liftCoordinates h values)) point component =
      ∑ column, InclinedFrameReal.pointMotion data
        (embed data basis (InclinedFrameReduced.unit data basis (columnIndex h column))) point component * values column := by
  let functional := (pointEvaluation data point component).comp (embedding data basis)
  calc
    _ = ∑ index, liftCoordinates h values index * functional (InclinedFrameReduced.unit data basis index) :=
      InclinedFrameReduced.linear_expansion data basis functional (liftCoordinates h values)
    _ = ∑ column, values column * functional (InclinedFrameReduced.unit data basis (columnIndex h column)) := by
      have reindexed := ((columnEquivalence h).sum_comp
        (fun index => liftCoordinates h values index * functional (InclinedFrameReduced.unit data basis index))).symm
      change (∑ index, liftCoordinates h values index * functional (InclinedFrameReduced.unit data basis index)) =
        ∑ column, liftCoordinates h values (columnIndex h column) *
          functional (InclinedFrameReduced.unit data basis (columnIndex h column)) at reindexed
      simpa only [lift_at_column] using reindexed
    _ = _ := by
      apply Finset.sum_congr rfl
      intro column _
      exact mul_comm _ _

theorem nodalMotion_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hbasis : GlobalBasisValid data basis) {certificate : Certificate data basis}
    (hprojection : ProjectionChecks bits certificate) {values : Fin basis.columns.size → ℝ}
    (hvalues : ∀ column, Contains (certificate.solve.solution column) (values column))
    {point : Nat} {out : Fin 3 → FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.nodalMotion bits certificate point = some out) :
    ∀ i, Contains (out i)
      (InclinedFrameReal.pointMotion data (embed data basis (liftCoordinates hbasis values)) point i) := by
  simp only [InclinedFrameIntervalRecovery.nodalMotion, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
  obtain ⟨horizontal, hx, vertical, hy, rotation, hr, hout⟩ := h
  subst out
  have hcolumn := InclinedFrameIntervalAssemblySound.pointColumnAt_contains hbasis hprojection point
  have hxContains := FrameIntervalVectorSound.dot_contains hx (fun column => hcolumn column 0) hvalues
  have hyContains := FrameIntervalVectorSound.dot_contains hy (fun column => hcolumn column 1) hvalues
  have hrContains := FrameIntervalVectorSound.dot_contains hr (fun column => hcolumn column 2) hvalues
  rw [← source_point_expansion hbasis values point 0] at hxContains
  rw [← source_point_expansion hbasis values point 1] at hyContains
  rw [← source_point_expansion hbasis values point 2] at hrContains
  intro i
  fin_cases i
  · simpa using hxContains
  · simpa using hyContains
  · simpa using hrContains

theorem localMotion_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hbasis : GlobalBasisValid data basis) {certificate : Certificate data basis}
    (hgeometry : GeometryChecks bits certificate) (hprojection : ProjectionChecks bits certificate)
    {values : Fin basis.columns.size → ℝ}
    (hvalues : ∀ column, Contains (certificate.solve.solution column) (values column))
    {index : Fin data.pieces.size} {out : Fin 6 → FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.localMotion bits certificate index = some out) :
    ∀ i, Contains (out i) (InclinedFrameReal.pieceMotion data data.pieces[index.val]!
      (embed data basis (liftCoordinates hbasis values)) i) := by
  simp only [InclinedFrameIntervalRecovery.localMotion, Option.bind_eq_bind, Option.bind_eq_some] at h
  obtain ⟨first, hfirst, second, hsecond, hout⟩ := h
  obtain ⟨_, hc, hs, _⟩ := InclinedFrameIntervalGeometrySound.piece_contains (hgeometry index)
  exact FrameIntervalTransformSound.localPiece_contains hout hc hs
    (nodalMotion_contains hbasis hprojection hvalues hfirst)
    (nodalMotion_contains hbasis hprojection hvalues hsecond)

theorem checked_selection (data : Partition) (query : RationalFrame.Query)
    (h : InclinedFrameIntervalRecovery.queryValid data query = true) :
    ∃ index : Fin data.pieces.size, InclinedFrameIntervalRecovery.selectedPiece data query = some index ∧
      InclinedFrameIntervalRecovery.SideContains data.pieces[index.val]! query := by
  cases selected : InclinedFrameIntervalRecovery.selectedPiece data query with
  | none => simp [InclinedFrameIntervalRecovery.queryValid, selected] at h
  | some index =>
    refine ⟨index, rfl, ?_⟩
    simp only [InclinedFrameIntervalRecovery.queryValid, selected, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

theorem endAction_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (hbasis : GlobalBasisValid data basis)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (hload : LoadChecks bits certificate) {values : Fin basis.columns.size → ℝ}
    {index : Fin data.pieces.size} {motion : Fin 6 → FrameIntervalOps.Bounds}
    (hmotion : ∀ i, Contains (motion i) (InclinedFrameReal.pieceMotion data data.pieces[index.val]!
      (embed data basis (liftCoordinates hbasis values)) i))
    {component : Fin 6} {out : FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.endAction bits certificate index motion component = some out) :
    let segment := data.pieces[index.val]!
    let member := data.source.members[segment.member]!
    let direction := InclinedFrameReal.memberDirection data segment.member
    Contains out (LocalFrameFields.endActions
      (InclinedFrameReal.pieceMotion data segment (embed data basis (liftCoordinates hbasis values)))
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

def sourceInputs (data : Partition) (basis : GlobalBasis) (hbasis : GlobalBasisValid data basis)
    (values : Fin basis.columns.size → ℝ) (index : Fin data.pieces.size) (parameter : Rat) : Fin 15 → ℝ :=
  let segment := data.pieces[index.val]!
  let member := data.source.members[segment.member]!
  let direction := InclinedFrameReal.memberDirection data segment.member
  let length := InclinedFrameReal.pieceLength data segment
  FrameIntervalRecoverySound.inputs
    (InclinedFrameReal.pieceMotion data segment (embed data basis (liftCoordinates hbasis values)))
    length member.EA member.EI
    (direction.sine*segment.vertical) (direction.sine*segment.verticalEnd)
    (direction.cosine*segment.vertical) (direction.cosine*segment.verticalEnd)
    (length*((parameter : ℝ)-segment.left)/((segment.right : ℝ)-segment.left))
    direction.cosine direction.sine

theorem fieldInputs_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (hpartition : PartitionValid data) (hbasis : GlobalBasisValid data basis)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (hprojection : ProjectionChecks bits certificate) (hload : LoadChecks bits certificate)
    {values : Fin basis.columns.size → ℝ}
    (hvalues : ∀ column, Contains (certificate.solve.solution column) (values column))
    {index : Fin data.pieces.size} {parameter : Rat} {out : Fin 15 → FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.fieldInputs bits certificate index parameter = some out) :
    ∀ i, Contains (out i) (sourceInputs data basis hbasis values index parameter i) := by
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
  have hd := localMotion_contains hbasis hgeometry hprojection hvalues hmotion
  have hax := endAction_contains hpartition hbasis hgeometry hload hd hactionX
  have hay := endAction_contains hpartition hbasis hgeometry hload hd hactionY
  have ham := endAction_contains hpartition hbasis hgeometry hload hd hactionMoment
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
    (hpartition : PartitionValid data) (hbasis : GlobalBasisValid data basis)
    {certificate : Certificate data basis} (hgeometry : GeometryChecks bits certificate)
    (hprojection : ProjectionChecks bits certificate) (hload : LoadChecks bits certificate)
    {values : Fin basis.columns.size → ℝ}
    (hvalues : ∀ column, Contains (certificate.solve.solution column) (values column))
    {query : RationalFrame.Query} {component : Fin 6} {out : FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalRecovery.field bits certificate query component = some out) :
    ∃ index : Fin data.pieces.size,
      InclinedFrameIntervalRecovery.selectedPiece data query = some index ∧
      InclinedFrameIntervalRecovery.SideContains data.pieces[index.val]! query ∧
      Contains out (InclinedFrameReal.fieldValues data data.pieces[index.val]!
        (embed data basis (liftCoordinates hbasis values)) query.t component) := by
  by_cases hquery : InclinedFrameIntervalRecovery.queryValid data query = true
  · obtain ⟨index, hselected, hside⟩ := checked_selection data query hquery
    have hbody : (InclinedFrameIntervalRecovery.fieldInputs bits certificate index query.t >>= fun inputs =>
        FrameIntervalRecovery.field bits inputs component) = some out := by
      simpa [InclinedFrameIntervalRecovery.field, hquery, hselected] using h
    obtain ⟨inputs, hinputs, hfield⟩ := Option.bind_eq_some.mp hbody
    have hi := fieldInputs_contains hpartition hbasis hgeometry hprojection hload hvalues hinputs
    have hp := InclinedFrameReal.piece_properties data hpartition index
    have hresult := FrameIntervalRecoverySound.field_contains
      (ne_of_gt hp.1) (ne_of_gt hp.2.1) (ne_of_gt hp.2.2) hi hfield
    refine ⟨index, hselected, hside, ?_⟩
    simpa only [FrameIntervalRecoverySound.actualFields, InclinedFrameReal.fieldValues] using hresult
  · simp [InclinedFrameIntervalRecovery.field, hquery] at h

end
end InclinedFrameIntervalRecoverySound
