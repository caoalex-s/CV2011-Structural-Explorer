import MemberKinematicsPhysical
import InclinedDiagramReportSound

namespace MemberKinematics.Sound
open FrameEnclosure Set FrameIntervalOps
open InclinedDiagram.Sound (mapM_index)
noncomputable section

/-- One row list per one-sided source piece. Distances use the original
member length and fractions measured from the drawn start. -/
def station (p : Segment) (length t : ℝ) := length*((p.left:ℝ)+((p.right:ℝ)-p.left)*t)

theorem located {bits p piece whole row out} (made : locate bits p piece whole row = some out) :
    out.piece = piece ∧ out.value = row.value ∧ ∀ L t, Contains whole L → Contains row.t t →
      Contains out.station (station p L t) := by
  obtain ⟨dist,hd,rest⟩ := Option.bind_eq_some.mp made
  cases rest
  refine ⟨rfl,rfl,fun L t len loc => ?_⟩
  apply executable_multiply_contains hd len
  simpa [station,Rat.cast_sub] using InclinedDiagram.Sound.shifted p.left (InclinedDiagram.Sound.scaled (p.right-p.left) loc)

structure PhysicalTable (pieces : List Segment) (physical : Fin pieces.length → PhysicalPiece)
    (L : ℝ) (f : Field) (rows : List Located) : Prop where
  witness : ∀ r ∈ rows, ∃ i t, t ∈ Icc (0:ℝ) 1 ∧ r.piece = i.val ∧
    Contains r.value (((physical i).field f).eval ((physical i).length*t))
  covered : ∀ i t, t ∈ Icc (0:ℝ) 1 →
    let h := physical i
    let value := fun z => (h.field f).eval (h.length*z)
    (IsMaxOn value (Icc 0 1) t ∨ IsMinOn value (Icc 0 1) t) →
    ∃ r ∈ rows, r.piece = i.val ∧ Contains r.station (station (pieces.get i) L t) ∧ Contains r.value (value t)

private theorem memberIndex {α : Type} {xs : List α} {x : α} (mem : x ∈ xs) :
    ∃ i : Fin xs.length, xs.get i = x := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  exact ⟨⟨i,hi⟩,eq⟩

theorem collection_sound {bits : Nat} {pieces : List Segment} {whole : FrameIntervalOps.Bounds} {L : ℝ} {f : Field} {rows : List Located} (physical : Fin pieces.length → PhysicalPiece)
    (length : Contains whole L) (fits : ∀ i, Fits (pieces.get i) ((physical i).inputs 0) (physical i).length)
    (positive : ∀ i, (physical i).positive) (checked : collectedRows bits pieces whole f = some rows) :
    PhysicalTable pieces physical L f rows := by
  obtain ⟨groups,hg,rest⟩ := Option.bind_eq_some.mp checked
  cases rest
  obtain ⟨eq,each⟩ := mapM_index _ hg
  have count : pieces.length = groups.length := by simpa using eq
  have perPiece (i : Fin pieces.length) :
      ∃ cs, candidates bits (pieces.get i) f = some cs ∧
        cs.mapM (locate bits (pieces.get i) i.val whole) = some (groups.get (i.cast count)) := by
    have made := each (⟨i.val,by simpa using i.isLt⟩ : Fin pieces.zipIdx.length)
    simpa [Option.bind_eq_some] using made
  constructor
  · intro r mem
    obtain ⟨g,hg,hr⟩ := List.mem_flatten.mp mem
    obtain ⟨j,ej⟩ := memberIndex hg
    let i := j.cast count.symm
    obtain ⟨cs,hc,hl⟩ := perPiece i
    have groupEq : groups.get (i.cast count) = g := ej
    rw [groupEq] at hl
    obtain ⟨n,locations⟩ := mapM_index _ hl
    obtain ⟨k,ek⟩ := memberIndex hr
    have loc := locations (k.cast n.symm)
    have here : g.get ((k.cast n.symm).cast n) = r := ek
    rw [here] at loc
    have binding := located loc
    obtain ⟨t,dom,value⟩ := candidates_witness (fits i) hc (List.get_mem cs (k.cast n.symm))
    refine ⟨i,t,dom,binding.1,?_⟩
    rw [binding.2.1,←physical_recovery _ (positive i)]
    exact value
  · intro i t dom
    dsimp only
    intro ext
    obtain ⟨cs,hc,hl⟩ := perPiece i
    obtain ⟨r,hr,loc,val⟩ := physical_extreme_covered _ (positive i) (fits i) hc dom ext
    obtain ⟨k,hk⟩ := memberIndex hr
    obtain ⟨n,locations⟩ := mapM_index _ hl
    have binding := locations k
    rw [hk] at binding
    have enclosed := located binding
    exact ⟨_,List.mem_flatten.mpr ⟨_,List.get_mem _ _,List.get_mem _ _⟩,enclosed.1,
      enclosed.2.2 _ _ length loc,enclosed.2.1 ▸ val⟩

def fieldValue {n} (physical : Fin n → PhysicalPiece) (f : Field) (i : Fin n) (t : ℝ) :=
  ((physical i).field f).eval ((physical i).length*t)

def MemberExtreme {n} (physical : Fin n → PhysicalPiece) (f : Field) (maximum : Bool) (value : ℝ) :=
  ∀ i t, t ∈ Icc (0:ℝ) 1 → if maximum then fieldValue physical f i t ≤ value
    else value ≤ fieldValue physical f i t

/-- A global extremum of the original member is in the reported ordinate
box and has a flagged station interval on its own physical piece. -/
theorem member_extreme {pieces physical L f rows e} (tab : PhysicalTable pieces physical L f rows)
    (made : summarize rows = some e) (maximum : Bool) (i : Fin pieces.length) (t : ℝ)
    (dom : t ∈ Icc 0 1) (bound : MemberExtreme physical f maximum (fieldValue physical f i t)) :
    let value := fieldValue physical f i t
    Contains (if maximum then e.maximum else e.minimum) value ∧
    ∃ r ∈ rows, r.piece = i.val ∧ Contains r.station (station (pieces.get i) L t) ∧
      (if maximum then e.maximum.lower ≤ r.value.upper else r.value.lower ≤ e.minimum.upper) := by
  obtain ⟨outer,⟨lo,hlo,low⟩,⟨hi,hhi,high⟩⟩ := summary_checks made
  cases maximum with
  | false =>
    obtain ⟨r,mem,owner,loc,val⟩ := tab.covered i t dom (Or.inr (fun _ hx => bound i _ hx))
    obtain ⟨j,x,hx,_,vx⟩ := tab.witness lo hlo
    have upper : fieldValue physical f i t ≤ (e.minimum.upper:ℝ) :=
      (bound j x hx).trans (vx.2.trans (by exact_mod_cast low))
    exact ⟨⟨le_trans (by exact_mod_cast (outer r mem).1) val.1,upper⟩,r,mem,owner,loc,
      by exact_mod_cast val.1.trans upper⟩
  | true =>
    obtain ⟨r,mem,owner,loc,val⟩ := tab.covered i t dom (Or.inl (fun _ hx => bound i _ hx))
    obtain ⟨j,x,hx,_,vx⟩ := tab.witness hi hhi
    have lower : (e.maximum.lower:ℝ) ≤ fieldValue physical f i t :=
      le_trans (by exact_mod_cast high) (vx.1.trans (bound j x hx))
    exact ⟨⟨lower,val.2.trans (by exact_mod_cast (outer r mem).2)⟩,r,mem,owner,loc,
      by exact_mod_cast lower.trans val.2⟩

#print axioms collection_sound
#print axioms member_extreme
end
end MemberKinematics.Sound
