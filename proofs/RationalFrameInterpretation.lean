import RationalFrameAlgebra
import MemberCutAdapter

/-! Interpretation of checked source-owned subdivisions in the existing
    FrameAssemblyModel. Original members and interior ownership are retained;
    this is not an unrelated expanded graph with assumed matrix entries. -/
namespace RationalFrame.Interpretation
open FrameAssemblyModel FrameTransform
noncomputable section

theorem members_bounded (data : Compiled) (valid : PartitionValid data)
    (i : Fin data.source.members.size) :
    data.source.members[i.val]!.a < data.source.nodes.size ∧
    data.source.members[i.val]!.b < data.source.nodes.size ∧ 0 < memberLength data.source i.val := by
  rcases valid with ⟨_, _, _, _, _, members, _⟩
  exact members i

theorem segments_valid (data : Compiled) (valid : PartitionValid data)
    (i : Fin data.segments.size) : SegmentValid data data.segments[i.val]! := by
  rcases valid with ⟨_, _, _, _, _, _, _, _, _, segments, _⟩
  exact segments i

theorem points_valid (data : Compiled) (valid : PartitionValid data)
    (i : Fin data.points.size) : PointValid data i := by
  rcases valid with ⟨_, _, _, _, _, _, points, _⟩
  exact points i

theorem supports_valid (data : Compiled) (valid : PartitionValid data)
    (i : Fin data.source.supports.size) :
    let support := data.source.supports[i.val]!
    LocationValid data support.member support.t (locationIndex data support.member support.t) := by
  rcases valid with ⟨_, _, _, _, _, _, _, _, _, _, _, supports, _⟩
  exact supports i

theorem loads_valid (data : Compiled) (valid : PartitionValid data)
    (i : Fin data.source.loads.size) :
    let load := data.source.loads[i.val]!
    LocationValid data load.member load.t (locationIndex data load.member load.t) := by
  rcases valid with ⟨_, _, _, _, _, _, _, _, _, _, _, _, loads⟩
  exact (loads i).1

/-- Cut slots are the derived point indices, but the Location still carries
    its original member owner. Equal global coordinates never weld cuts. -/
def location (data : Compiled) (member : Fin data.source.members.size) (t : Rat)
    (point : Fin data.points.size) : Location data.source.members.size data.points.size :=
  if t = 0 then .endSide (member, false)
  else if t = 1 then .endSide (member, true)
  else .interior member point

def segmentMember (data : Compiled) (valid : PartitionValid data) (i : Fin data.segments.size) :
    Fin data.source.members.size := ⟨data.segments[i.val]!.member, (segments_valid data valid i).1⟩

def segmentStart (data : Compiled) (valid : PartitionValid data) (i : Fin data.segments.size) :
    Fin data.points.size := ⟨data.segments[i.val]!.a, (segments_valid data valid i).2.1.2.1⟩

def segmentEnd (data : Compiled) (valid : PartitionValid data) (i : Fin data.segments.size) :
    Fin data.points.size := ⟨data.segments[i.val]!.b, (segments_valid data valid i).2.2.1.2.1⟩

/-- All supported ends are rigid. Retaining the requested reference is exact,
    although it has no mechanical effect when every incident end is rigid. -/
def requestedReference (data : Compiled) (i : Fin data.source.nodes.size) : Option (Fin data.source.members.size) :=
  match data.source.nodes[i.val]!.reference with
  | none => none
  | some member => if h : member < data.source.members.size then some ⟨member, h⟩ else none

def model (data : Compiled) (valid : PartitionValid data) :
    Model data.source.nodes.size data.source.members.size data.points.size data.segments.size where
  joints := fun i => {
    kind := .rigid
    rotationStiffness := (data.source.nodes[i.val]!.rotationStiffness : ℝ)
    requestedReference := requestedReference data i }
  member := fun i => {
    startNode := ⟨data.source.members[i.val]!.a, (members_bounded data valid i).1⟩
    endNode := ⟨data.source.members[i.val]!.b, (members_bounded data valid i).2.1⟩
    orientation := ⟨(memberCosine data.source i.val : ℝ), (memberSine data.source i.val : ℝ)⟩
    explicitStart := some rigidConnection
    explicitEnd := some rigidConnection }
  segmentMember := segmentMember data valid
  segmentLeft := fun i => location data (segmentMember data valid i)
    data.segments[i.val]!.left (segmentStart data valid i)
  segmentRight := fun i => location data (segmentMember data valid i)
    data.segments[i.val]!.right (segmentEnd data valid i)
  segmentLength := fun i => (data.segments[i.val]!.length : ℝ)
  segmentEA := fun i => (data.segments[i.val]!.EA : ℝ)
  segmentEI := fun i => (data.segments[i.val]!.EI : ℝ)
  segmentVerticalStart := fun i => (data.segments[i.val]!.vertical : ℝ)
  segmentVerticalEnd := fun i => (data.segments[i.val]!.vertical : ℝ)

def cutParameter (data : Compiled) (_member : Fin data.source.members.size) (point : Fin data.points.size) : ℝ :=
  (data.points[point.val]!.t : ℝ)

def supports (data : Compiled) (valid : PartitionValid data) (i : Fin data.source.supports.size) :
    SupportInput data.source.members.size data.points.size :=
  let support := data.source.supports[i.val]!
  let represented := supports_valid data valid i
  {
    location := location data ⟨support.member, represented.1⟩ support.t
      ⟨locationIndex data support.member support.t, represented.2.1⟩
    kind := if support.kind = 0 then .pin else if support.kind = 1 then .fixed else .roller
    cosine := if support.angle = 0 then 1 else if support.angle = 180 then -1 else 0
    sine := if support.angle = 90 then 1 else if support.angle = 270 then -1 else 0
    fixX := false, fixY := false, fixRotation := false }

/-- Distributed source entries contribute zero point action here; their exact
    restricted intensity is already on each segment. Direct actions retain
    their member-side location and the force/couple kind semantics. -/
def actions (data : Compiled) (valid : PartitionValid data) (i : Fin data.source.loads.size) :
    PointAction data.source.members.size data.points.size :=
  let load := data.source.loads[i.val]!
  let represented := loads_valid data valid i
  {
    location := location data ⟨load.member, represented.1⟩ load.t
      ⟨locationIndex data load.member load.t, represented.2.1⟩
    globalAction := if load.kind = 0 then ![(load.fx : ℝ), (load.fy : ℝ), 0]
      else if load.kind = 1 then ![0, 0, (load.mz : ℝ)] else ![0, 0, 0] }

theorem rigid (data : Compiled) (valid : PartitionValid data)
    (side : MemberEnd data.source.members.size) : endConnection (model data valid) side = rigidConnection := by
  simp [endConnection, model]

theorem no_slip (data : Compiled) (valid : PartitionValid data)
    (side : MemberEnd data.source.members.size) (direction : Fin 3) :
    ¬ hasSlip (model data valid) side direction := by
  simp [hasSlip, rigid, directionLaw, rigidConnection]

theorem ownership (data : Compiled) (valid : PartitionValid data) : segmentOwnershipValid (model data valid) := by
  intro i
  constructor <;> simp [model, location, locationBelongs] <;> split_ifs <;> rfl

theorem location_parameter (data : Compiled) (member : Fin data.source.members.size) (t : Rat)
    (point : Fin data.points.size) (valid : LocationValid data member.val t point.val) :
    locationParameter (cutParameter data) (location data member t point) = (t : ℝ) := by
  unfold location
  split_ifs with hzero hone
  · simp [locationParameter, hzero]
  · simp [locationParameter, hone]
  · have hp := valid.2.2
    simp only [hzero, hone, ↓reduceIte] at hp
    simpa [locationParameter, cutParameter] using congrArg (fun value : Rat => (value : ℝ)) hp.2

/-- The finite source coordinate allocation maps to the original-node or
    original-member-owned point in FrameAssemblyModel. -/
def point (data : Compiled) (valid : PartitionValid data) (i : Fin data.points.size) :
    FrameAssemblyModel.Point data.source.nodes.size data.source.members.size data.points.size := by
  have hp := points_valid data valid i
  cases ho : data.points[i.val]!.owner with
  | none =>
    simp only [PointValid, ho] at hp
    exact .inl ⟨i.val, hp.2.1⟩
  | some owner =>
    simp only [PointValid, ho] at hp
    exact .inr (⟨owner, hp.2.1⟩, i)

theorem point_prefix (data : Compiled) (valid : PartitionValid data) (i : Fin data.points.size)
    (bound : i.val < data.source.nodes.size) : point data valid i = .inl ⟨i.val, bound⟩ := by
  cases ho : data.points[i.val]!.owner with
  | none => simp [point, ho]
  | some owner =>
    have hp := points_valid data valid i
    simp only [PointValid, ho] at hp
    exact False.elim (Nat.not_le_of_lt bound hp.1)

theorem location_point (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size) (t : Rat) (index : Fin data.points.size)
    (represented : LocationValid data member.val t index.val) :
    locationPoint (model data valid) (location data member t index) = point data valid index := by
  by_cases hzero : t = 0
  · have hi : index.val = data.source.members[member.val]!.a := by
      simpa [LocationValid, hzero] using represented.2.2
    have bound : index.val < data.source.nodes.size := by
      rw [hi]
      exact (members_bounded data valid member).1
    rw [point_prefix data valid index bound]
    simp only [location, hzero, ↓reduceIte, locationPoint, endNode, Bool.false_eq_true, ↓reduceIte, model]
    congr 1
    exact Fin.ext hi.symm
  · by_cases hone : t = 1
    · have hi : index.val = data.source.members[member.val]!.b := by
        simpa [hzero, hone] using represented.2.2
      have bound : index.val < data.source.nodes.size := by
        rw [hi]
        exact (members_bounded data valid member).2.1
      rw [point_prefix data valid index bound]
      simp only [location, hzero, hone, ↓reduceIte, locationPoint, endNode, model]
      congr 1
      exact Fin.ext hi.symm
    · have owned : data.points[index.val]!.owner = some member.val := by
        have hi := represented.2.2
        simp only [hzero, hone, ↓reduceIte] at hi
        exact hi.1
      simp [location, hzero, hone, locationPoint, point, owned]

theorem point_active (data : Compiled) (valid : PartitionValid data) (i : Fin data.points.size) :
    activePoint (model data valid) (point data valid i) := by
  have represented : ∃ segment : Fin data.segments.size,
      data.segments[segment.val]!.a = i.val ∨ data.segments[segment.val]!.b = i.val := by
    rcases valid with ⟨_, _, _, _, _, _, _, _, active, _⟩
    have hi := active i
    push_neg at hi
    exact hi
  obtain ⟨segment, hstart | hend⟩ := represented
  · refine ⟨segment, Or.inl ?_⟩
    change locationPoint (model data valid)
      (location data (segmentMember data valid segment) data.segments[segment.val]!.left
        (segmentStart data valid segment)) = point data valid i
    rw [location_point data valid _ _ _ (segments_valid data valid segment).2.1]
    congr 1
    exact Fin.ext hstart
  · refine ⟨segment, Or.inr ?_⟩
    change locationPoint (model data valid)
      (location data (segmentMember data valid segment) data.segments[segment.val]!.right
        (segmentEnd data valid segment)) = point data valid i
    rw [location_point data valid _ _ _ (segments_valid data valid segment).2.2.1]
    congr 1
    exact Fin.ext hend

theorem positive_segments (data : Compiled) (valid : PartitionValid data) : FrameAssembly.positiveSegments (model data valid) := by
  intro i
  rcases segments_valid data valid i with ⟨_, _, _, _, _, _, _, hlength, hEA, hEI, _⟩
  change 0 < (data.segments[i.val]!.length : ℝ) ∧ 0 < (data.segments[i.val]!.EA : ℝ) ∧ 0 < (data.segments[i.val]!.EI : ℝ)
  exact_mod_cast And.intro hlength (And.intro hEA hEI)

/-- The executable chain test implies the existing exact real interval-chain
    predicate. No rounded cut sorting or coverage assumption is imported. -/
theorem chain_real (start : Rat) (segments : List Segment)
    (checked : chainFrom start segments = true) (nonempty : segments ≠ []) :
    MemberCutAdapter.IntervalChain (start : ℝ) 1
      (segments.map (fun segment => ((segment.left : ℝ), (segment.right : ℝ)))) := by
  induction segments generalizing start with
  | nil => exact False.elim (nonempty rfl)
  | cons segment rest ih =>
    simp only [chainFrom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at checked
    obtain ⟨⟨hleft, hpositive⟩, hrest⟩ := checked
    cases rest with
    | nil =>
      have hright : segment.right = 1 := by simpa [chainFrom] using hrest
      simp only [List.map_cons, List.map_nil, hleft, hright, Rat.cast_one]
      apply MemberCutAdapter.IntervalChain.single
      exact_mod_cast hleft ▸ hright ▸ hpositive
    | cons next tail =>
      simp only [List.map_cons, hleft]
      apply MemberCutAdapter.IntervalChain.step
      · exact_mod_cast hleft ▸ hpositive
      · exact ih segment.right hrest (by simp)

theorem member_chain (data : Compiled) (valid : PartitionValid data) (member : Fin data.source.members.size) :
    MemberCutAdapter.IntervalChain 0 1
      ((memberSegments data member.val).map (fun segment => ((segment.left : ℝ), (segment.right : ℝ)))) := by
  rcases valid with ⟨_, _, _, _, _, _, _, _, _, _, chains, _⟩
  have checked := chains member
  have nonempty : memberSegments data member.val ≠ [] := by
    intro hempty
    simp [hempty, chainFrom] at checked
  simpa using chain_real 0 (memberSegments data member.val) checked nonempty

theorem member_coverage (data : Compiled) (valid : PartitionValid data)
    (member : Fin data.source.members.size) (t : ℝ) (hzero : 0 ≤ t) (hone : t ≤ 1) :
    ∃ segment ∈ memberSegments data member.val, (segment.left : ℝ) ≤ t ∧ t ≤ (segment.right : ℝ) := by
  obtain ⟨piece, hpiece, hl, hr⟩ := MemberCutAdapter.chain_coverage (member_chain data valid member) t hzero hone
  obtain ⟨segment, hsegment, heq⟩ := List.mem_map.mp hpiece
  cases heq
  exact ⟨segment, hsegment, hl, hr⟩

end
end RationalFrame.Interpretation
