import MemberKinematicsTable
import FrameSpringSound
import InclinedFrameIntervalEquilibrium

namespace MemberKinematics.Sound
open FrameEnclosure (Contains)
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly
open InclinedFrameReal (Motion)
open InclinedDiagram.Sound (mapM_index)
noncomputable section

def EndReport (p : Segment) (h : PhysicalPiece) (i : Nat) (line : String) :=
  ∃ a b u v, line = String.intercalate " " (["P", toString i, MemberDiagram.number p.left,
      MemberDiagram.number p.right] ++ InclinedDiagram.boxText a ++ InclinedDiagram.boxText b ++
      InclinedDiagram.boxText u ++ InclinedDiagram.boxText v) ∧
    Contains a (h.dofs 2) ∧ Contains b (h.dofs 5) ∧ Contains u (h.dofs 1) ∧ Contains v (h.dofs 4)

private theorem end_parts {bits : Nat} {p : Segment} {i : Nat} {line : String}
    (made : endRow bits p i = some line) :
    ∃ a b u v, MemberKinematics.evaluate bits p (quantity .slope) ⟨0,0⟩ = some a ∧
      MemberKinematics.evaluate bits p (quantity .slope) ⟨1,1⟩ = some b ∧
      MemberKinematics.evaluate bits p transverse ⟨0,0⟩ = some u ∧
      MemberKinematics.evaluate bits p transverse ⟨1,1⟩ = some v ∧
      line = String.intercalate " " (["P", toString i, MemberDiagram.number p.left, MemberDiagram.number p.right] ++
        InclinedDiagram.boxText a ++ InclinedDiagram.boxText b ++ InclinedDiagram.boxText u ++ InclinedDiagram.boxText v) := by
  unfold endRow at made
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at made
  obtain ⟨a,ha,b,hb,u,hu,v,hv,eq⟩ := made
  exact ⟨a,b,u,v,ha,hb,hu,hv,eq.symm⟩

private theorem physical_value {bits : Nat} {p : Segment} (h : PhysicalPiece)
    (positive : h.positive) (fits : Fits p (h.inputs 0) h.length) (f : Field)
    (t : ℝ) {box value : FrameIntervalOps.Bounds} (whereAt : Contains box t)
    (checked : MemberKinematics.evaluate bits p (quantity f) box = some value) :
    Contains value ((h.field f).eval (h.length*t)) := by
  have enclosed := enclosure (expr := quantity f) fits whereAt checked
  change Contains value (functionAt (h.inputs 0) h.length (quantity f) t) at enclosed
  rw [physical_recovery h positive f t] at enclosed
  exact enclosed

theorem end_sound {bits : Nat} {p : Segment} {i : Nat} {line : String} (h : PhysicalPiece)
    (positive : h.positive) (fits : Fits p (h.inputs 0) h.length) (made : endRow bits p i = some line) :
    EndReport p h i line := by
  obtain ⟨a,b,u,v,ha,hb,hu,hv,printed⟩ := end_parts made
  have start : Contains ⟨0,0⟩ (0:ℝ) := by norm_num [FrameEnclosure.Contains]
  have finish : Contains ⟨1,1⟩ (1:ℝ) := by norm_num [FrameEnclosure.Contains]
  have ra := physical_value h positive fits .slope 0 start ha
  have rb := physical_value h positive fits .slope 1 finish hb
  have ua := physical_value h positive fits .displacement 0 start hu
  have ub := physical_value h positive fits .displacement 1 finish hv
  have rot := LocalFrameFields.rotation_end_kinematics h.dofs h.length h.flexural h.q h.qEnd positive.1.ne' positive.2.2.ne'
  have disp := LocalFrameFields.transverse_end_kinematics h.dofs h.length h.flexural h.q h.qEnd positive.1.ne' positive.2.2.ne'
  simp only [PhysicalPiece.field, mul_zero, rot.1] at ra
  simp only [PhysicalPiece.field, mul_one, rot.2] at rb
  simp only [PhysicalPiece.field, mul_zero, disp.1] at ua
  simp only [PhysicalPiece.field, mul_one, disp.2] at ub
  exact ⟨a,b,u,v,printed,ra,rb,ua,ub⟩

def FieldReport (pieces : List Segment) (physical : Fin pieces.length → PhysicalPiece)
    (L : ℝ) (f : Field) (lines : List String) :=
  ∃ rows e, lines = renderRows f rows e ∧ PhysicalTable pieces physical L f rows ∧ soundLimits rows e ∧
    ∀ maximum i t, t ∈ Set.Icc (0:ℝ) 1 → MemberExtreme physical f maximum (fieldValue physical f i t) →
      Contains (if maximum then e.maximum else e.minimum) (fieldValue physical f i t) ∧
      ∃ r ∈ rows, r.piece = i.val ∧ Contains r.station (station (pieces.get i) L t) ∧
        (if maximum then e.maximum.lower ≤ r.value.upper else r.value.lower ≤ e.minimum.upper)

theorem field_report {bits : Nat} {pieces : List Segment} {whole : FrameIntervalOps.Bounds} {L : ℝ} {f : Field} {lines : List String} (physical : Fin pieces.length → PhysicalPiece)
    (len : Contains whole L) (fits : ∀ i, Fits (pieces.get i) ((physical i).inputs 0) (physical i).length)
    (positive : ∀ i, (physical i).positive) (made : fieldRows bits pieces whole f = some lines) :
    FieldReport pieces physical L f lines := by
  obtain ⟨rows,hr,rest⟩ := Option.bind_eq_some.mp made
  obtain ⟨e,he,rest⟩ := Option.bind_eq_some.mp rest
  cases rest
  have tab := collection_sound physical len fits positive hr
  exact ⟨rows,e,rfl,tab,summary_checks he,member_extreme tab he⟩

def PhysicalReport (data : Partition) (member : Nat) (motion : Motion data) (text : String) :=
  ∃ (pieces : List Segment) (indices : (InclinedDiagram.selected data member).length = pieces.length)
    (ends slopes deflections : List String) (endCount : ends.length = pieces.length),
    let src := fun i : Fin pieces.length => (InclinedDiagram.selected data member).get (i.cast indices.symm)
    let physical := fun i => physicalPiece data motion (src i)
    text = String.intercalate "\n" (["CV2011_MEMBER_KINEMATICS_1",data.source.members[member]!.id] ++ ends ++ slopes ++ deflections) ∧
    (∀ i : Fin pieces.length, (pieces.get i).left = data.pieces[(src i).val]!.left ∧
      (pieces.get i).right = data.pieces[(src i).val]!.right ∧
      EndReport (pieces.get i) (physical i) i.val (ends.get (i.cast endCount.symm))) ∧
    FieldReport pieces physical (InclinedFrameReal.memberLength data member) .slope slopes ∧
    FieldReport pieces physical (InclinedFrameReal.memberLength data member) .displacement deflections

theorem sheet_sound {data : Partition} {basis : GlobalBasis} {bits member}
    {cert : Certificate data basis} {motion : Motion data}
    (valid : PartitionValid data) (geometry : GeometryChecks bits cert) (loads : LoadChecks bits cert)
    (nodes : InclinedRelease.Fields.NodeEnclosures bits cert motion)
    {text} (made : sheet bits member cert = some text) : PhysicalReport data member motion text := by
  obtain ⟨pieces,hp,rest⟩ := Option.bind_eq_some.mp made
  obtain ⟨g,hg,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨ends,he,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨slopes,hs,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨v,hv,rest⟩ := Option.bind_eq_some.mp rest
  dsimp only at rest
  split at rest
  next =>
    cases rest
    obtain ⟨length,each⟩ := mapM_index _ hp
    obtain ⟨endLength,endOf⟩ := mapM_index _ he
    have endCount : ends.length = pieces.length := by simpa using endLength.symm
    let src := fun i : Fin pieces.length => (InclinedDiagram.selected data member).get (i.cast length.symm)
    let phys := fun i => physicalPiece data motion (src i)
    have recovered (i : Fin pieces.length) : recover bits cert (src i) = some (pieces.get i) :=
      each (i.cast length.symm)
    have fits (i : Fin pieces.length) : Fits (pieces.get i) ((phys i).inputs 0) (phys i).length := by
      simpa [phys,physicalPiece,PhysicalPiece.inputs,InclinedRelease.Fields.sourceInputs] using
        source_fits valid motion geometry loads nodes (recovered i)
    have positive (i : Fin pieces.length) : (phys i).positive := positive_source valid motion _
    have len := (InclinedFrameIntervalGeometrySound.member_contains hg).1
    refine ⟨pieces,length,ends,slopes,v,endCount,rfl,?_,field_report phys len fits positive hs,
      field_report phys len fits positive hv⟩
    intro i
    have rhs := endOf (⟨i.val,by simpa using i.isLt⟩ : Fin pieces.zipIdx.length)
    have computed : endRow bits (pieces.get i) i.val = some (ends.get (i.cast endCount.symm)) := by simpa using rhs
    have base := recovered i
    obtain ⟨_,_,eq⟩ := Option.bind_eq_some.mp base
    have coordinates := Option.some.inj eq
    exact ⟨congrArg Segment.left coordinates.symm,congrArg Segment.right coordinates.symm,
      end_sound (phys i) (positive i) (fits i) computed⟩
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
    exact ⟨p,hp,data,hd,motion,eq,unique,sheet_sound checks.1 checks.2.2.1 checks.2.2.2.2.1 nodes rest⟩
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
    exact ⟨p,hp,l,hl,z,eq,unique,sheet_sound l.valid geometry loads nodes rest⟩
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
    exact ⟨p,hp,l,ks,hl,z,eq,unique,sheet_sound l.valid geometry loads nodes rest⟩
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
#print axioms end_sound
end
end MemberKinematics.Sound
