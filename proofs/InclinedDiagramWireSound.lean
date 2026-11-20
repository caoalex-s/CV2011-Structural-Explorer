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

theorem printed_flags {name all c text} (done : candidateText name all c = some text) :
    ∃ low high, isExtreme false c all = some low ∧ isExtreme true c all = some high ∧
      text = printed name all c low high := by
  obtain ⟨lo,hl,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨hi,hh,eq⟩ := Option.bind_eq_some.mp rest
  cases eq
  exact ⟨lo,hi,hl,hh,rfl⟩

def Ordered {α β : Type} (xs : List α) (ys : List β) (related : α → β → Prop) :=
  ∃ equal : xs.length = ys.length, ∀ i : Fin xs.length, related (xs.get i) (ys.get (i.cast equal))

theorem each_group {dimension bits pieces m lines} (state : Fin dimension → ℝ)
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

#print axioms each_group
end
end InclinedDiagram.Sound
