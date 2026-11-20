import InclinedDiagramReportSound

namespace InclinedDiagram.Sound
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly
open InclinedDiagram.Statics.Sound
open InclinedFrameReal (Motion)
noncomputable section

def group (bits : Nat) (pieces : List InclinedDiagram.Piece) (m : Bool) := do
  let lists ← pieces.zipIdx.mapM fun (p,i) => rows bits i p m
  let all := lists.flatten
  all.mapM (candidateText (if m then "M" else "V") all)

/-- The exact bytes carry the source-owned coefficients followed by one
record per computed candidate. The two printed bits are the checked extrema
predicates on the concatenation of all one-sided source pieces. -/
def printed (field : String) (all : List Candidate) (c : Candidate) (low high : Bool) :=
  String.intercalate " " ([field,toString c.piece,c.side] ++ boxText c.t ++ boxText c.x ++ boxText c.y ++
    [if low then "1" else "0",if high then "1" else "0"])

set_option maxHeartbeats 1600000 in
theorem printed_flags {name all c text} (done : candidateText name all c = some text) :
    ∃ low high, isExtreme false c all = some low ∧ isExtreme true c all = some high ∧
      text = printed name all c low high := by
  unfold candidateText at done
  obtain ⟨lo,hl,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨hi,hh,eq⟩ := Option.bind_eq_some.mp rest
  exact ⟨lo,hi,hl,hh,(Option.some.inj eq).symm⟩

def Ordered {α β : Type} (xs : List α) (ys : List β) (related : α → β → Prop) :=
  ∃ equal : xs.length = ys.length, ∀ i : Fin xs.length, related (xs.get i) (ys.get (i.cast equal))

theorem each_group {dimension bits : Nat} {pieces : List InclinedDiagram.Piece} {m : Bool} {lines : List String} (state : Fin dimension → ℝ)
    (physical : Fin pieces.length → State) (L : ℝ)
    (same : ∀ i, (physical i).L = L)
    (fitsPiece : ∀ i, fits (pieces.get i) (physical i))
    (formsPiece : ∀ i, Forms state (pieces.get i) (physical i))
    (accepted : group bits pieces m = some lines) :
    ∃ table : FieldTable pieces.length dimension,
      table.pieces = pieces.get ∧ table.physical = physical ∧ table.moment = m ∧
      Ordered table.all lines (fun c line => ∃ lo hi,
        line = printed (if m then "M" else "V") table.all c lo hi ∧
        (lo = true ↔ ∀ y, table.attained y → table.atRow c ≤ y) ∧
        (hi = true ↔ ∀ y, table.attained y → y ≤ table.atRow c)) := by
  obtain ⟨lists,hm,rendered⟩ := Option.bind_eq_some.mp accepted
  obtain ⟨equal,each⟩ := mapM_index _ hm
  have length : pieces.length = lists.length := by simpa using equal
  let table : FieldTable pieces.length dimension := {
    pieces := pieces.get, physical, state, moment := m, length := L, lengthEq := same, bits,
    output := fun i => lists.get (i.cast length), fit := fitsPiece, forms := formsPiece
    made := by
      intro i
      have e := each (⟨i.val,by simpa using i.isLt⟩ : Fin pieces.zipIdx.length)
      simpa using e }
  have all : table.all = lists.flatten := by
    unfold FieldTable.all
    change ((List.finRange pieces.length).map (fun i => lists.get (i.cast length))).flatten = lists.flatten
    congr 1
    apply List.ext_getElem
    · simpa using length
    · intro i hl hr
      simp [List.finRange,List.map_ofFn,getElem!_pos]
  rw [←all] at rendered
  obtain ⟨size,outputs⟩ := mapM_index _ rendered
  refine ⟨table,rfl,rfl,rfl,size,?_⟩
  intro i
  obtain ⟨lo,hi,hl,hh,eq⟩ := printed_flags (outputs i)
  have belongs : table.all.get i ∈ table.all := List.get_mem _ _
  exact ⟨lo,hi,eq,by simpa using table.flagged belongs false hl,
    by simpa using table.flagged belongs true hh⟩

def PhysicalReport (data : Partition) (member : Nat) (motion : Motion data) (text : String) :=
  ∃ (pieces : List InclinedDiagram.Piece) (locations : (selected data member).length = pieces.length)
    (shearRows momentRows : List String),
    text = String.intercalate "\n" (["CV2011_INCLINED_DIAGRAM_1",data.source.members[member]!.id] ++
      pieces.map pieceText ++ shearRows ++ momentRows) ∧
    (∀ i : Fin pieces.length, let index := (selected data member).get (i.cast locations.symm)
      fits (pieces.get i) (physicalState data motion index) ∧ sourceShape data index (pieces.get i)) ∧
    (∀ m : Bool, ∃ dimension, ∃ table : FieldTable pieces.length dimension,
      table.pieces = pieces.get ∧
      table.physical = (fun i => physicalState data motion ((selected data member).get (i.cast locations.symm))) ∧
      table.moment = m ∧ Ordered table.all (if m then momentRows else shearRows) (fun c line => ∃ lo hi,
        line = printed (if m then "M" else "V") table.all c lo hi ∧
        (lo = true ↔ ∀ y, table.attained y → table.atRow c ≤ y) ∧
        (hi = true ↔ ∀ y, table.attained y → y ≤ table.atRow c)))

set_option maxHeartbeats 1600000 in
theorem sheet_sound {data : Partition} {basis : GlobalBasis} {bits member}
    {cert : Certificate data basis} {motion : Motion data}
    {springs : Array (Fin basis.columns.size → Rat)} {torque : Fin springs.size → ℝ}
    (partition : PartitionValid data) (geometry : GeometryChecks bits cert) (loads : LoadChecks bits cert)
    (nodes : InclinedRelease.Fields.NodeEnclosures bits cert motion) (work : WorkColumns cert motion springs torque)
    {text} (accepted : sheet bits member cert springs = some text) : PhysicalReport data member motion text := by
  obtain ⟨pieces,hp,encoded⟩ := Option.bind_eq_some.mp accepted
  obtain ⟨length,each⟩ := mapM_index _ hp
  let source := fun i : Fin pieces.length => (selected data member).get (i.cast length.symm)
  let physical := fun i => physicalState data motion (source i)
  let state := frameState motion torque
  have info (i : Fin pieces.length) : fits (pieces.get i) (physical i) ∧
      sourceShape data (source i) (pieces.get i) ∧ Forms state (pieces.get i) (physical i) := by
    have op := each (i.cast length.symm)
    let system := Statics.assemble cert springs
    change (fromSource bits cert (source i)).map (withStatics data system (source i)) = some (pieces.get i) at op
    cases derived : fromSource bits cert (source i) with
    | none => rw [derived] at op; cases op
    | some raw =>
      rw [derived] at op
      have base := fromSource_fits motion partition geometry loads nodes derived
      have refined := refined_forms partition work _ raw base
      have shape := fromSource_shape derived
      have eq : withStatics data system (source i) raw = pieces.get i := Option.some.inj op
      rw [←eq]
      exact ⟨refined.1,shape,refined.2⟩
  have same (i : Fin pieces.length) : (physical i).L = InclinedFrameReal.memberLength data member := by
    have mem : source i ∈ selected data member := List.get_mem _ _
    have selectedMember := (List.mem_filter.mp mem).2
    change InclinedFrameReal.memberLength data data.pieces[(source i).val]!.member = _
    rw [beq_iff_eq.mp selectedMember]
  unfold encode at encoded
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp encoded
  obtain ⟨shear,hs,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨mom,hm,rest⟩ := Option.bind_eq_some.mp rest
  dsimp only at rest
  split at rest
  next =>
    cases rest
    refine ⟨pieces,length,shear,mom,rfl,fun i => ⟨(info i).1,(info i).2.1⟩,?_⟩
    intro m
    have emitted : group bits pieces m = some (if m then mom else shear) := by
      cases m <;> assumption
    obtain ⟨table,p,h,flag,rows⟩ := each_group state physical _ same (fun i => (info i).1)
      (fun i => (info i).2.2) emitted
    exact ⟨_,table,p,h,flag,rows⟩
  next => cases rest

open InclinedFrameGlobalBasis
open InclinedFrameIntervalEquilibrium (liftCoordinates lift_at_column)

theorem rigid_accepted {input text} (ok : rigid input = some text) :
    ∃ p : InclinedFrameIntervalWire.Packet, InclinedFrameIntervalWire.decode input = some p ∧
      ∃ data, checkedPartition p.source = some data ∧ ∃ motion : Motion data,
        InclinedFrameReduced.Equilibrium data motion ∧
        (∀ other, InclinedFrameReduced.Equilibrium data other → other = motion) ∧
        PhysicalReport data p.query.member motion text := by
  obtain ⟨p,hp,rest⟩ := Option.bind_eq_some.mp ok
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨data,hd,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨basis,hb,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨cert,hc,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next verified =>
    have checks : Checks p.bits cert := of_decide_eq_true verified
    obtain ⟨basisValid,z,eq,unique,boxed⟩ := InclinedFrameIntervalEquilibrium.check_physical_equilibrium verified
    let motion := embed data basis (liftCoordinates basisValid z)
    have values : ∀ j, FrameEnclosure.Contains (cert.solve.solution j) (z j) :=
      fun j => by simpa only [lift_at_column] using boxed j
    have nodes : InclinedRelease.Fields.NodeEnclosures p.bits cert motion :=
      fun h => InclinedFrameIntervalRecoverySound.nodalMotion_contains basisValid checks.2.2.2.1 values h
    exact ⟨p,hp,data,hd,motion,eq,unique,sheet_sound checks.1 checks.2.2.1 checks.2.2.2.2.1 nodes
      (rigid_columns checks.1 basisValid checks.2.2.2.1 motion eq) rest⟩
  next => cases rest

theorem released_accepted {input text} (ok : released input = some text) :
    ∃ p : InclinedRelease.Wire.Packet, InclinedRelease.Wire.decode input = some p ∧
      ∃ l, InclinedRelease.layout p.source p.rules = some l ∧ ∃ z,
        FrameMatrixResidual.action (InclinedRelease.Sound.matrix l) z = InclinedRelease.Sound.force l ∧
        (∀ other, FrameMatrixResidual.action (InclinedRelease.Sound.matrix l) other = InclinedRelease.Sound.force l → other=z) ∧
        PhysicalReport l.expanded p.query.member (InclinedRelease.Sound.motion l z) text := by
  obtain ⟨p,hp,rest⟩ := Option.bind_eq_some.mp ok
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨l,hl,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨proposal,_,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨cert,_,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next verified =>
    obtain ⟨z,eq,values,unique⟩ := InclinedRelease.Sound.equilibrium verified
    simp only [InclinedRelease.verified,Bool.and_eq_true,decide_eq_true_eq] at verified
    obtain ⟨⟨geometry,cols,loads,_⟩,_⟩ := verified
    have nodes : InclinedRelease.Fields.NodeEnclosures p.bits cert (InclinedRelease.Sound.motion l z) :=
      fun h => InclinedRelease.Sound.nodal_motion cols values h
    exact ⟨p,hp,l,hl,z,eq,unique,sheet_sound l.valid geometry loads nodes (release_columns l cols z eq) rest⟩
  next => cases rest

theorem spring_accepted {input text} (ok : spring input = some text) :
    ∃ p : FrameSpring.Wire.Packet, FrameSpring.Wire.decode input = some p ∧
      ∃ l ks, FrameSpring.resolve p.source p.rules = some (l,ks) ∧ ∃ z,
        FrameMatrixResidual.action (FrameSpring.Sound.physicalMatrix l ks) z = InclinedRelease.Sound.force l ∧
        (∀ other, FrameMatrixResidual.action (FrameSpring.Sound.physicalMatrix l ks) other = InclinedRelease.Sound.force l → other=z) ∧
        PhysicalReport l.expanded p.query.member (InclinedRelease.Sound.motion l z) text := by
  obtain ⟨p,hp,rest⟩ := Option.bind_eq_some.mp ok
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨⟨l,ks⟩,hl,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨proposal,_,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨cert,_,rest⟩ := Option.bind_eq_some.mp rest
  split at rest
  next verified =>
    obtain ⟨z,eq,values,unique⟩ := FrameSpring.Sound.equilibrium verified
    simp only [FrameSpring.verified,Bool.and_eq_true,decide_eq_true_eq] at verified
    obtain ⟨⟨geometry,cols,loads,_⟩,_⟩ := verified
    have nodes : InclinedRelease.Fields.NodeEnclosures p.bits cert (InclinedRelease.Sound.motion l z) :=
      fun h => InclinedRelease.Sound.nodal_motion cols values h
    exact ⟨p,hp,l,ks,hl,z,eq,unique,sheet_sound l.valid geometry loads nodes (spring_columns l ks cols z eq) rest⟩
  next => cases rest

theorem accepted_dispatch {input text} (ok : checkReport input = some text) :
    spring input = some text ∨ released input = some text ∨ rigid input = some text := by
  unfold checkReport at ok
  split at ok
  · exact Or.inl ok
  · split at ok
    · exact Or.inr (Or.inl ok)
    · exact Or.inr (Or.inr ok)

#print axioms rigid_accepted
#print axioms released_accepted
#print axioms spring_accepted
#print axioms accepted_dispatch
#print axioms sheet_sound
#print axioms each_group
end
end InclinedDiagram.Sound
