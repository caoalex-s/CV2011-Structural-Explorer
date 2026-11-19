import InclinedDiagramExtrema

namespace InclinedDiagram.Sound
open FrameEnclosure (Contains)
open Set
noncomputable section

def represents (p : Piece) (s : State) (m : Bool) (r : Candidate) (t : ℝ) :=
  Contains r.t t ∧ Contains r.x (position p s t) ∧ Contains r.y (field p s m t) ∧
  field p s m (stationValue p s r.station) = field p s m t

theorem row_represents {bits i p s m side station r} (h : fits p s)
    (made : row bits i p m side station = some r) :
    represents p s m r (stationValue p s station) := by
  obtain ⟨ht,hx,hy,eq,_⟩ := row_bounds h made
  exact ⟨ht,hx,hy,by rw [eq]⟩

/-- Each real extremum has a row at its own location, including every
point of a constant piece. Endpoints of adjacent pieces remain distinct. -/
theorem critical_covered {bits i p s m candidates} (h : fits p s)
    (made : rows bits i p m = some candidates) (t : ℝ) (domain : t ∈ Icc 0 1)
    (critical : t = 0 ∨ t = 1 ∨ slope p s m t = 0) :
    ∃ r ∈ candidates, represents p s m r t := by
  obtain ⟨a,ha,rest⟩ := Option.bind_eq_some.mp made
  obtain ⟨b,hb,rest⟩ := Option.bind_eq_some.mp rest
  have start : represents p s m a 0 := by simpa [stationValue] using row_represents h ha
  have finish : represents p s m b 1 := by simpa [stationValue] using row_represents h hb
  by_cases flatPiece : flat p m = true
  · simp [flatPiece] at rest
    subst candidates
    let plateau : Candidate := {a with side := "flat",t := ⟨0,1⟩,x := ⟨a.x.lower,b.x.upper⟩}
    refine ⟨plateau,by simp [plateau],?_,?_,?_,?_⟩
    · simpa [plateau,Contains] using domain
    · have width : 0 < span p s := mul_pos h.2.2.2.1 (by exact_mod_cast sub_pos.mpr h.2.2.2.2)
      have lower := start.2.1.1
      have upper := finish.2.1.2
      change (a.x.lower:ℝ) ≤ position p s t ∧ position p s t ≤ b.x.upper
      unfold position at *
      unfold span at width
      constructor
      · nlinarith only [lower,mul_nonneg width.le domain.1]
      · nlinarith only [upper,mul_nonneg width.le (sub_nonneg.mpr domain.2)]
    · change Contains a.y (field p s m t)
      rw [constant_field h flatPiece t]
      exact start.2.2.1
    · exact start.2.2.2.trans (constant_field h flatPiece t).symm
  · simp only [flatPiece,↓reduceIte] at rest
    obtain ⟨stations,hs,rest⟩ := Option.bind_eq_some.mp rest
    obtain ⟨mid,hm,eq⟩ := Option.bind_eq_some.mp rest
    cases eq
    by_cases left : t = 0
    · exact ⟨a,by simp,left ▸ start⟩
    by_cases right : t = 1
    · exact ⟨b,by simp,right ▸ finish⟩
    obtain ⟨r,hr,positionEq⟩ := stationary_complete h (Bool.eq_false_iff.mpr flatPiece) hs
      ((critical.resolve_left left).resolve_left right)
    obtain ⟨out,ho,kept⟩ := (collected hm).1 r hr
    have strict : stationValue p s r ∈ Ioo 0 1 := positionEq ▸
      ⟨lt_of_le_of_ne domain.1 (Ne.symm left), lt_of_le_of_ne domain.2 right⟩
    obtain ⟨z,rfl,hz⟩ := interior_kept h strict ho
    have member := kept z (by simp)
    exact ⟨z,by simp [member],positionEq ▸ row_represents h hz⟩

theorem extremum_covered {bits i p s m candidates} (h : fits p s)
    (made : rows bits i p m = some candidates) {t : ℝ} (domain : t ∈ Icc 0 1)
    (extreme : IsMaxOn (field p s m) (Icc 0 1) t ∨ IsMinOn (field p s m) (Icc 0 1) t) :
    ∃ r ∈ candidates, represents p s m r t := by
  apply critical_covered h made t domain
  by_cases left : t = 0
  · exact Or.inl left
  by_cases right : t = 1
  · exact Or.inr (Or.inl right)
  have near := Icc_mem_nhds (lt_of_le_of_ne domain.1 (Ne.symm left)) (lt_of_le_of_ne domain.2 right)
  have deriv := field_derivative p s m t
  exact Or.inr (Or.inr (extreme.elim (fun mx => (mx.isLocalMax near).hasDerivAt_eq_zero deriv)
    (fun mn => (mn.isLocalMin near).hasDerivAt_eq_zero deriv)))

#print axioms extremum_covered
end
end InclinedDiagram.Sound
