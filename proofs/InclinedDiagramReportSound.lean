import InclinedDiagramFormsSound
import InclinedDiagramOrder

namespace InclinedDiagram.Sound
open FrameEnclosure (Contains)
open InclinedDiagram.Statics.Sound (value frameState)
open Set
noncomputable section

def signedValue (s : State) (m : Bool) (y : ℝ) := if m then y else s.L*y
def ordinate (p : Piece) (s : State) (m : Bool) (r : Candidate) := field p s m (stationValue p s r.station)

/-- These two relations exhaust the exact comparisons that do not use
disjoint ordinate bounds. Flat rows retain the metadata of their first end. -/
def Metadata {n} (state : Fin n → ℝ) (p : Piece) (s : State) (m : Bool) (r : Candidate) :=
  (∀ u, r.shearOffset = some u → ordinate p s m r = s.V+u) ∧
  (r.signature.isEmpty = false → value state r.signature = signedValue s m (ordinate p s m r))

theorem row_metadata {n bits i p s m side r c} {state : Fin n → ℝ}
    (forms : Forms state p s) (made : row bits i p m side r = some c) : Metadata state p s m c := by
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp made
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨_,_,eq⟩ := Option.bind_eq_some.mp rest
  cases eq
  cases r with
  | fixed t =>
    constructor
    · intro u hu
      cases m <;> simp [ordinate,stationValue,field,shear] at hu ⊢
      subst u
      simp
    · intro nonempty
      have base : p.scaledShear.isEmpty = false := by
        cases e : p.scaledShear.isEmpty
        · rfl
        · simp [fieldSignature,e,Id.run] at nonempty
      cases m <;> simpa [signedValue,ordinate,stationValue,field] using signature_value forms _ t base
  | linearRoot => constructor <;> simp
  | quadraticRoot plus => constructor <;> simp

theorem piece_metadata {n bits i p s m all} {state : Fin n → ℝ}
    (forms : Forms state p s) (made : rows bits i p m = some all) {c} (mem : c ∈ all) :
    Metadata state p s m c := by
  obtain ⟨a,ha,rest⟩ := Option.bind_eq_some.mp made
  obtain ⟨b,hb,rest⟩ := Option.bind_eq_some.mp rest
  by_cases flatPiece : flat p m = true
  · simp [flatPiece] at rest
    subst all
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact row_metadata forms ha
    · exact (show Metadata state p s m a from row_metadata forms ha)
    · exact row_metadata forms hb
  · simp only [flatPiece,↓reduceIte] at rest
    obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp rest
    obtain ⟨mid,hm,eq⟩ := Option.bind_eq_some.mp rest
    cases eq
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at mem
    rcases mem with (rfl | inner) | rfl
    · exact row_metadata forms ha
    · obtain ⟨st,_,inside⟩ := (collected hm).2 c inner
      obtain ⟨_,_,rest⟩ := Option.bind_eq_some.mp inside
      split at rest
      · cases rest
      next =>
        split at rest
        · obtain ⟨entry,he,eq⟩ := Option.bind_eq_some.mp rest
          cases eq
          exact row_metadata forms he
        next => cases rest
    · exact row_metadata forms hb

theorem mapM_index {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (done : xs.mapM f = some ys) :
    ∃ equal : xs.length = ys.length, ∀ i : Fin xs.length,
      f (xs.get i) = some (ys.get (i.cast equal)) := by
  induction xs generalizing ys with
  | nil =>
    simp at done
    subst ys
    exact ⟨rfl,fun i => Fin.elim0 i⟩
  | cons a tail ih =>
    rw [List.mapM_cons] at done
    obtain ⟨b,hb,rest⟩ := Option.bind_eq_some.mp done
    obtain ⟨others,ho,eq⟩ := Option.bind_eq_some.mp rest
    cases eq
    obtain ⟨length,each⟩ := ih ho
    refine ⟨by simp [length],?_⟩
    intro i
    refine Fin.cases (by simpa using hb) (fun j => ?_) i
    simpa using each j

/-- A table for one physical member. Indices identify one-sided pieces,
so two limits at a discontinuity can both attain a global extremum. -/
structure FieldTable (n dimension : Nat) where
  pieces : Fin n → Piece
  physical : Fin n → State
  state : Fin dimension → ℝ
  moment : Bool
  length : ℝ
  lengthEq : ∀ i, (physical i).L = length
  bits : Nat
  output : Fin n → List Candidate
  made : ∀ i, rows bits i.val (pieces i) moment = some (output i)
  fit : ∀ i, fits (pieces i) (physical i)
  forms : ∀ i, Forms state (pieces i) (physical i)

namespace FieldTable
variable {n dimension : Nat} (table : FieldTable n dimension)

def all := (List.finRange n).flatMap table.output
def atRow (r : Candidate) : ℝ :=
  if h : r.piece < n then ordinate (table.pieces ⟨_,h⟩) (table.physical ⟨_,h⟩) table.moment r else 0
def attained (y : ℝ) := ∃ i t, t ∈ Icc (0:ℝ) 1 ∧ field (table.pieces i) (table.physical i) table.moment t = y

theorem owner {r} (mem : r ∈ table.all) : ∃ i : Fin n, r ∈ table.output i ∧ r.piece = i.val := by
  obtain ⟨i,_,hr⟩ := List.mem_flatMap.mp mem
  exact ⟨i,hr,(all_rows_attained (table.fit i) (table.made i) hr).2.2⟩

theorem row_value {i : Fin n} {r} (mem : r ∈ table.output i) :
    table.atRow r = ordinate (table.pieces i) (table.physical i) table.moment r := by
  have index := (all_rows_attained (table.fit i) (table.made i) mem).2.2
  simp [atRow,index]

theorem comparative {r q} (hr : r ∈ table.all) (hq : q ∈ table.all) :
    orderMeans (table.atRow r) (table.atRow q) (compareValues r q) := by
  obtain ⟨i,ri,ei⟩ := table.owner hr
  obtain ⟨j,qj,ej⟩ := table.owner hq
  rw [table.row_value ri,table.row_value qj]
  have mr := piece_metadata (table.forms i) (table.made i) ri
  have mq := piece_metadata (table.forms j) (table.made j) qj
  apply compare_sound (all_rows_attained (table.fit i) (table.made i) ri).2.1
    (all_rows_attained (table.fit j) (table.made j) qj).2.1
  · intro same station
    have sameOwner : i = j := Fin.ext (ei.symm.trans (same.trans ej))
    subst j
    simp [ordinate,station]
  · intro same u v hu hv
    have sameOwner : i = j := Fin.ext (ei.symm.trans (same.trans ej))
    subst j
    change ordinate _ _ _ r - ordinate _ _ _ q = _
    rw [mr.1 u hu,mq.1 v hv]
    ring
  · intro notEmpty same
    have eq := (mr.2 notEmpty).symm.trans ((congrArg (value table.state) same).trans
      (mq.2 (same ▸ notEmpty)))
    simp only [signedValue,table.lengthEq] at eq
    split at eq
    · exact eq
    next =>
      have positive : 0 < table.length := table.lengthEq i ▸ (table.fit i).2.2.2.1
      exact mul_left_cancel₀ (ne_of_gt positive) eq

theorem flagged {r flag} (hr : r ∈ table.all) (maximum : Bool)
    (reported : isExtreme maximum r table.all = some flag) :
    flag = true ↔ ∀ y, table.attained y → if maximum then y ≤ table.atRow r else table.atRow r ≤ y := by
  rw [flags_mean table.atRow (fun _ h => table.comparative hr h) reported]
  constructor
  · intro bounds y hy
    obtain ⟨i,t,domain,rfl⟩ := hy
    obtain ⟨⟨lo,hlo,below⟩,⟨hi,hhi,above⟩⟩ := piece_range (table.fit i) (table.made i) t domain
    have member {c} (h : c ∈ table.output i) : c ∈ table.all := List.mem_flatMap.mpr ⟨i,by simp,h⟩
    cases maximum
    · have lower : table.atRow r ≤ table.atRow lo := bounds lo (member hlo)
      rw [table.row_value hlo] at lower
      exact lower.trans below
    · have upper : table.atRow hi ≤ table.atRow r := bounds hi (member hhi)
      rw [table.row_value hhi] at upper
      exact above.trans upper
  · intro bounds q hq
    obtain ⟨j,mem,_⟩ := table.owner hq
    have domain := (all_rows_attained (table.fit j) (table.made j) mem).1
    exact bounds _ ⟨j,_,domain,(table.row_value mem).symm⟩

#print axioms flagged
end FieldTable
#print axioms piece_metadata
end
end InclinedDiagram.Sound
