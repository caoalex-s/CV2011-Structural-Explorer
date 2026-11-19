import RationalFrameFields
import FrameSpringSound
import InclinedDiagramStatics

namespace InclinedDiagram.Statics.Sound
noncomputable section

/-- Rotate both element end forces into the global drawing axes. -/
def forceX (c s axial transverse : ℝ) := c*axial - s*transverse
def forceY (c s axial transverse : ℝ) := s*axial + c*transverse

/-- Global balance of an arbitrary Euler-Bernoulli element carrying a
vertical affine load. This holds for every physical element motion. -/
theorem element_balance (motion : FrameInterfaces.LocalDofs) (ell EA EI c s f₀ f₁ : ℝ)
    (length : ell ≠ 0) (axial : EA ≠ 0) (bending : EI ≠ 0) (unit : c^2+s^2=1) :
    let actions := LocalFrameFields.endActions motion ell EA EI (s*f₀) (s*f₁) (c*f₀) (c*f₁)
    let xa := forceX c s (actions 0) (actions 1)
    let ya := forceY c s (actions 0) (actions 1)
    let xb := forceX c s (actions 3) (actions 4)
    let yb := forceY c s (actions 3) (actions 4)
    xa+xb = 0 ∧ ya+yb+ell*(f₀+f₁)/2 = 0 ∧
      actions 2+actions 5+(ell*c)*yb-(ell*s)*xb+ell*(ell*c)*(f₀+2*f₁)/6 = 0 := by
  let a := LocalFrameFields.endActions motion ell EA EI (s*f₀) (s*f₁) (c*f₀) (c*f₁)
  have recover := RationalFrame.Fields.affine_recovery motion ell EA EI
    (s*f₀) (s*f₁) (c*f₀) (c*f₁) ell length axial bending
  have n : a 3 = -a 0 - s*f₀*ell - (s*f₁-s*f₀)/ell*ell^2/2 := recover.1
  have v : a 4 = -(a 1 + c*f₀*ell + (c*f₁-c*f₀)/ell*ell^2/2) :=
    congrArg Neg.neg recover.2.1
  have m : a 5 = -a 2 + a 1*ell + c*f₀*ell^2/2 + (c*f₁-c*f₀)/ell*ell^3/6 :=
    recover.2.2.1
  have axialEnd : a 3 = -a 0-ell*s*(f₀+f₁)/2 := by rw [n]; field_simp [length]; ring
  have shearEnd : a 4 = -a 1-ell*c*(f₀+f₁)/2 := by rw [v]; field_simp [length]; ring
  have momentEnd : a 5 = -a 2+ell*a 1+ell^2*c*(2*f₀+f₁)/6 := by rw [m]; field_simp [length]; ring
  change forceX c s (a 0) (a 1) + forceX c s (a 3) (a 4) = 0 ∧
    forceY c s (a 0) (a 1) + forceY c s (a 3) (a 4) + ell*(f₀+f₁)/2=0 ∧
    a 2+a 5+ell*c*forceY c s (a 3) (a 4)-ell*s*forceX c s (a 3) (a 4)+
      ell*(ell*c)*(f₀+2*f₁)/6=0
  rw [axialEnd,shearEnd,momentEnd]
  unfold forceX forceY
  constructor
  · ring
  constructor
  · linear_combination -ell*(f₀+f₁)/2 * unit
  · linear_combination ell*(-a 1-ell*c*(f₀+f₁)/2) * unit

def value {n : Nat} (state : Fin n → ℝ) (row : Row) :=
  ∑ i, ((row[i.val]! : Rat) : ℝ)*state i

def validRow {n : Nat} (state : Fin n → ℝ) (row : Row) :=
  row.size = n ∧ value state row = 0

theorem subtract_value {n} (state : Fin n → ℝ) (a b : Row) (k : Rat)
    (width : a.size = n) :
    (subtractMultiple a b k).size = n ∧
    value state (subtractMultiple a b k) = value state a - (k:ℝ)*value state b := by
  by_cases zero : k = 0
  · simp [subtractMultiple,zero,width]
  · have sizes : (subtractMultiple a b k).size = n := by simp [subtractMultiple,zero,width]
    refine ⟨sizes,?_⟩
    unfold value
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have inside : i.val < a.size := by simpa only [width] using i.isLt
    simp [subtractMultiple,zero,inside]
    ring

theorem pivots_preserve {n} (state : Fin n → ℝ) (pivots : List (Nat × Row))
    (valid : ∀ e ∈ pivots, validRow state e.2) (a : Row) (width : a.size = n) :
    (applyPivots pivots a).size = n ∧ value state (applyPivots pivots a) = value state a := by
  induction pivots generalizing a with
  | nil => exact ⟨width,rfl⟩
  | cons entry tail ih =>
    obtain ⟨index,pivot⟩ := entry
    have equation := (valid (index,pivot) List.mem_cons_self).2
    obtain ⟨size,step⟩ := subtract_value state a pivot a[index]! width
    obtain ⟨final,result⟩ := ih (fun e h => valid e (List.mem_cons_of_mem _ h)) _ size
    exact ⟨final,by simpa [applyPivots,step,equation] using result⟩

theorem divided_value {n} (state : Fin n → ℝ) (a : Row) (k : Rat) (width : a.size = n) :
    value state (a.map (· / k)) = value state a / (k:ℝ) := by
  unfold value
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have inside : i.val < a.size := by simpa only [width] using i.isLt
  simp [inside]
  ring

theorem insert_preserves {n} (state : Fin n → ℝ) (system : System) (equation : Row)
    (old : ∀ e ∈ system.pivots.toList, validRow state e.2) (row : validRow state equation) :
    ∀ e ∈ (insert system equation).pivots.toList, validRow state e.2 := by
  unfold insert
  dsimp only
  split
  next pivot =>
    have reduced := pivots_preserve state system.pivots.toList old equation row.1
    have size : (reduce system equation).size = n := reduced.1
    have zero : value state (reduce system equation) = 0 := reduced.2.trans row.2
    intro e member
    have memArray := Array.mem_def.mpr member
    rcases Array.mem_push.mp memArray with before | rfl
    · exact old e (Array.mem_def.mp before)
    · exact ⟨by simp [size],by rw [divided_value state _ _ size,zero,zero_div]⟩
  · exact old

def atSlot {n} (state : Fin n → ℝ) (index : Nat) : ℝ :=
  if h : index < n then state ⟨index,h⟩ else 0

def termsValue {n} (state : Fin n → ℝ) (terms : List (Nat × Rat)) : ℝ :=
  (terms.map fun term => (term.2:ℝ)*atSlot state term.1).sum

theorem equation_value {n} (state : Fin n → ℝ) (terms : List (Nat × Rat)) :
    value state (equation n terms) = termsValue state terms := by
  have entry (i : Fin n) (xs : List (Nat × Rat)) :
      ((equation n xs)[i.val]! : Rat) = coefficient i.val xs := by simp [equation,i.isLt]
  unfold value
  simp_rw [entry]
  induction terms with
  | nil => simp [coefficient,termsValue]
  | cons term rest ih =>
    obtain ⟨index,a⟩ := term
    simp only [coefficient,Rat.cast_add,add_mul,Finset.sum_add_distrib,ih]
    congr 1
    by_cases h : index < n
    · let j : Fin n := ⟨index,h⟩
      have same (i : Fin n) : (i.val = index) ↔ i = j := Fin.ext_iff.symm
      simp [same,apply_ite,ite_mul,atSlot,h,j]
    · have different (i : Fin n) : i.val ≠ index := by omega
      simp [different,atSlot,h]

theorem inserted_rows_valid {n} (state : Fin n → ℝ) (rows : List (List (Nat × Rat))) (system : System)
    (old : ∀ e ∈ system.pivots.toList, validRow state e.2)
    (zero : ∀ terms ∈ rows, termsValue state terms = 0) :
    ∀ e ∈ (insertRows n rows system).pivots.toList, validRow state e.2 := by
  induction rows generalizing system with
  | nil => exact old
  | cons terms tail ih =>
    have row : validRow state (equation n terms) :=
      ⟨by simp [equation],(equation_value state terms).trans (zero terms List.mem_cons_self)⟩
    exact ih _ (insert_preserves state system _ old row)
      (fun xs mem => zero xs (List.mem_cons_of_mem _ mem))

#print axioms inserted_rows_valid
open InclinedFrameSource InclinedFrameReal

/-- Rigid-frame virtual work in end-action form. Distributed loads already
enter the element end actions, leaving only the original point loads. -/
theorem rigid_work {data : Partition} (valid : PartitionValid data)
    {motion : Motion data} (solved : InclinedFrameReduced.Equilibrium data motion)
    (variation : Motion data) (allowed : InclinedFrameGlobalBasis.SourceAllows data variation) :
    (∑ i, InclinedFrameIntervalReactionsSound.actualPieceWork data motion variation i) =
      ∑ i, pointLoadWork data i variation := by
  rw [InclinedFrameIntervalReactionsSound.total_piece_work valid, solved.2 variation allowed]
  unfold externalWork
  ring

theorem rotate_work (actions displacement : FrameInterfaces.LocalDofs) (c s : ℝ) :
    (∑ i, FrameTransform.toLocal6 c s displacement i * actions i) =
      displacement 0 * forceX c s (actions 0) (actions 1) +
      displacement 1 * forceY c s (actions 0) (actions 1) + displacement 2 * actions 2 +
      displacement 3 * forceX c s (actions 3) (actions 4) +
      displacement 4 * forceY c s (actions 3) (actions 4) + displacement 5 * actions 5 := by
  simp [Fin.sum_univ_succ,FrameTransform.toLocal6,FrameTransform.toLocal,forceX,forceY]
  ring

#print axioms rigid_work
#print axioms rotate_work
#print axioms insert_preserves
#print axioms element_balance
end
end InclinedDiagram.Statics.Sound
