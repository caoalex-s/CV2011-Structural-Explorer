import InclinedDiagramSound

namespace InclinedDiagram.Sound
open FrameIntervalOps Set
open FrameEnclosure (Contains)
noncomputable section

def slope (p : Piece) (s : State) (m : Bool) (t : ℝ) :=
  if m then span p s * shear p s t else (p.linear:ℝ)+2*p.quadratic*t

theorem field_derivative (p : Piece) (s : State) (m : Bool) (t : ℝ) :
    HasDerivAt (field p s m) (slope p s m t) t := by
  cases m with
  | false =>
    have linear := ((hasDerivAt_id t).mul_const (p.quadratic:ℝ)).const_add (p.linear:ℝ)
    have derivative := ((hasDerivAt_id t).mul linear).const_add s.V
    convert derivative using 1 <;> simp [field,slope,shear,id] <;> ring
  | true =>
    have linear := ((hasDerivAt_id t).mul_const ((p.quadratic:ℝ)/3)).const_add ((p.linear:ℝ)/2)
    have quadratic := ((hasDerivAt_id t).mul linear).const_add s.V
    have derivative := (((hasDerivAt_id t).const_mul (span p s)).mul quadratic).const_add s.M
    convert derivative using 1 <;> simp [field,slope,moment,shear,id] <;> ring

theorem two_roots {p : Piece} {s : State} {t : ℝ} (curved : p.quadratic ≠ 0)
    (root : shear p s t = 0) :
    stationValue p s (.quadraticRoot false) = t ∨ stationValue p s (.quadraticRoot true) = t := by
  have nc : (p.quadratic : ℝ) ≠ 0 := by exact_mod_cast curved
  have square : (2*(p.quadratic:ℝ)*t+p.linear)^2 = disc p s := by
    unfold shear at root
    unfold disc
    linear_combination 4*(p.quadratic:ℝ)*root
  have squareRoot := Real.sq_sqrt (square ▸ sq_nonneg _)
  have factors : (2*(p.quadratic:ℝ)*t+p.linear-Real.sqrt (disc p s))*
      (2*(p.quadratic:ℝ)*t+p.linear+Real.sqrt (disc p s)) = 0 := by
    nlinarith only [square,squareRoot]
  let d := 2*(p.quadratic:ℝ)
  have hd : d ≠ 0 := mul_ne_zero (by norm_num) nc
  rcases mul_eq_zero.mp factors with positive | negative
  · right
    change -(p.linear:ℝ)/d + (1/d)*Real.sqrt (disc p s) = t
    calc
      _ = (-(p.linear:ℝ)+Real.sqrt (disc p s))/d := by ring
      _ = t := (div_eq_iff hd).mpr (by dsimp [d]; linarith)
  · left
    change -(p.linear:ℝ)/d + (-1/d)*Real.sqrt (disc p s) = t
    calc
      _ = (-(p.linear:ℝ)-Real.sqrt (disc p s))/d := by ring
      _ = t := (div_eq_iff hd).mpr (by dsimp [d]; linarith)

theorem singleton_value {b : Bounds} {x : ℝ} {a : Rat} (h : Contains b x)
    (eq : b = singleton a) : x = a := by
  subst b
  exact le_antisymm h.2 h.1

/-- A classified nonflat piece lists every stationary point of the real
field, including a repeated quadratic root exactly once. -/
theorem stationary_complete {p s m roots t} (h : fits p s) (nonflat : flat p m = false)
    (listed : stationary p m = some roots) (critical : slope p s m t = 0) :
    ∃ r ∈ roots, stationValue p s r = t := by
  have width : 0 < span p s := by
    apply mul_pos h.2.2.2.1
    exact_mod_cast sub_pos.mpr h.2.2.2.2
  cases m with
  | false =>
    simp [slope] at critical
    by_cases hc : p.quadratic = 0
    · simp [hc] at critical
      simp_all [flat]
    · simp [stationary,hc] at listed
      subst roots
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      have hc' : (p.quadratic:ℝ) ≠ 0 := by exact_mod_cast hc
      simp [stationValue]
      field_simp
      linarith
  | true =>
    have zero : shear p s t = 0 := (mul_eq_zero.mp critical).resolve_left (ne_of_gt width)
    by_cases hc : p.quadratic = 0
    · by_cases hb : p.linear = 0
      · have hv : s.V = 0 := by simpa [shear,hb,hc] using zero
        have bounds := h.2.1
        rw [hv] at bounds
        have lo : p.shearStart.lower ≤ 0 := by exact_mod_cast bounds.1
        have hi : 0 ≤ p.shearStart.upper := by exact_mod_cast bounds.2
        have neq : p.shearStart ≠ singleton 0 := by intro e; simp [flat,hb,hc,e] at nonflat
        simp [stationary,hb,hc,not_lt.mpr lo,not_lt.mpr hi,neq] at listed
      · simp [stationary,hc,hb] at listed
        subst roots
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        have hb' : (p.linear:ℝ) ≠ 0 := by exact_mod_cast hb
        simp [shear,hc] at zero
        simp [stationValue]
        field_simp
        linarith
    · let d := discriminant p
      have bound := disc_fits h
      have square : (2*(p.quadratic:ℝ)*t+p.linear)^2 = disc p s := by
        unfold shear at zero
        unfold disc
        linear_combination 4*(p.quadratic:ℝ)*zero
      have sign : 0 ≤ disc p s := square ▸ sq_nonneg _
      have nonneg : 0 ≤ d.upper := by exact_mod_cast le_trans sign bound.2
      by_cases eq : d = singleton 0
      · have discZero := singleton_value bound eq
        have value : 2*(p.quadratic:ℝ)*t+p.linear = 0 := by
          rw [discZero] at square
          norm_num at square
          exact square
        simp [stationary,hc,← show d = discriminant p from rfl,not_lt.mpr nonneg,eq,singleton] at listed
        subst roots
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        have hc' : (p.quadratic:ℝ) ≠ 0 := by exact_mod_cast hc
        simp [stationValue]
        field_simp
        linarith
      · by_cases positive : 0 < d.lower
        · simp [stationary,hc,← show d = discriminant p from rfl,not_lt.mpr nonneg,eq,positive] at listed
          subst roots
          rcases two_roots hc zero with neg | pos
          · exact ⟨_,by simp,neg⟩
          · exact ⟨_,by simp,pos⟩
        · simp [stationary,hc,← show d = discriminant p from rfl,not_lt.mpr nonneg,eq,positive] at listed

theorem row_bounds {bits i p s m side r out} (h : fits p s)
    (done : row bits i p m side r = some out) :
    Contains out.t (stationValue p s r) ∧ Contains out.x (position p s (stationValue p s r)) ∧
    Contains out.y (field p s m (stationValue p s r)) ∧ out.station = r ∧ out.piece = i := by
  obtain ⟨t,ht,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨x,hx,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨y,hy,rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨_,_,eq⟩ := Option.bind_eq_some.mp rest
  cases eq
  have parameter := station_fits h ht
  have fraction := shifted p.left (scaled (p.right-p.left) parameter)
  have positionBound := FrameEnclosure.executable_multiply_contains hx h.1 fraction
  exact ⟨parameter,by simpa [position] using positionBound,evaluate_fits h parameter hy,rfl,rfl⟩

theorem constant_field {p s m} (h : fits p s) (isFlat : flat p m = true) (t : ℝ) :
    field p s m t = field p s m 0 := by
  cases m with
  | false =>
    simp [flat] at isFlat
    simp [field,shear,isFlat.1,isFlat.2]
  | true =>
    simp [flat] at isFlat
    have zero := singleton_value h.2.1 isFlat.2
    simp [field,moment,isFlat.1.1,isFlat.1.2,zero]

theorem interior_kept {bits i p s m r out} (h : fits p s)
    (strict : stationValue p s r ∈ Ioo 0 1) (done : interior bits i p m r = some out) :
    ∃ v, out = some v ∧ row bits i p m "interior" r = some v := by
  obtain ⟨t,ht,rest⟩ := Option.bind_eq_some.mp done
  obtain ⟨lo,hi⟩ := station_fits h ht
  have a : ¬t.upper ≤ 0 := by exact_mod_cast (show ¬(t.upper:ℝ) ≤ 0 by linarith [strict.1])
  have b : ¬1 ≤ t.lower := by exact_mod_cast (show ¬(1:ℝ) ≤ t.lower by linarith [strict.2])
  change (if t.upper ≤ 0 ∨ 1 ≤ t.lower then some none else _) = some out at rest
  rw [if_neg (not_or.mpr ⟨a,b⟩)] at rest
  split at rest
  · obtain ⟨v,hv,result⟩ := Option.bind_eq_some.mp rest
    cases result
    exact ⟨v,rfl,hv⟩
  · cases rest

theorem collected {entry : Station → Option (Option Candidate)} {roots : List Station} {rows : List Candidate}
    (computed : collectStations entry roots = some rows) :
    (∀ r ∈ roots, ∃ out, entry r = some out ∧ ∀ z ∈ out.toList, z ∈ rows) ∧
    (∀ z ∈ rows, ∃ r ∈ roots, entry r = some (some z)) := by
  induction roots generalizing rows with
  | nil => simp [collectStations] at computed; subst rows; simp
  | cons r tail ih =>
    obtain ⟨out, h, rest⟩ := Option.bind_eq_some.mp computed
    obtain ⟨others, ho, result⟩ := Option.bind_eq_some.mp rest
    cases result
    obtain ⟨all, only⟩ := ih ho
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨out,h,fun _ hz => List.mem_append_left _ hz⟩
      · obtain ⟨v, hv, inc⟩ := all x hx
        exact ⟨v,hv,fun z hz => List.mem_append_right _ (inc z hz)⟩
    · intro z hz
      rcases List.mem_append.mp hz with first | later
      · cases out with
        | none => simp at first
        | some w => simp at first; subst w; exact ⟨r, List.mem_cons_self, h⟩
      · obtain ⟨x,hx,hit⟩ := only z later
        exact ⟨x,List.mem_cons_of_mem _ hx,hit⟩


#print axioms row_bounds
#print axioms stationary_complete
end
end InclinedDiagram.Sound
