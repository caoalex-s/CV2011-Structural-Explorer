import InclinedDiagramWire
import MemberDiagramSound
import FrameIntervalExpressionSound
import FrameSpringSound

namespace InclinedDiagram.Sound
open FrameIntervalOps FrameEnclosure Set
noncomputable section

structure State where
  L : ℝ
  V : ℝ
  M : ℝ

def fits (p : Piece) (s : State) :=
  Contains p.memberLength s.L ∧ Contains p.shearStart s.V ∧ Contains p.momentStart s.M ∧
    0 < s.L ∧ p.left < p.right

def span (p : Piece) (s : State) := s.L*((p.right:ℝ)-p.left)
def shear (p : Piece) (s : State) (t : ℝ) := s.V + t*(p.linear+t*p.quadratic)
def moment (p : Piece) (s : State) (t : ℝ) :=
  s.M + span p s*t*(s.V+t*((p.linear:ℝ)/2+t*((p.quadratic:ℝ)/3)))
def field (p : Piece) (s : State) (m : Bool) := if m then moment p s else shear p s
def position (p : Piece) (s : State) (t : ℝ) := s.L*((p.left:ℝ)+((p.right:ℝ)-p.left)*t)

theorem singleton_fits (v : Rat) : Contains (singleton v) (v : ℝ) := ⟨le_rfl,le_rfl⟩
theorem scaled {b : Bounds} {x : ℝ} (k : Rat) (h : Contains b x) : Contains (scale k b) ((k:ℝ)*x) := by
  unfold scale
  split
  next hpos =>
    have hk : 0 ≤ (k:ℝ) := by exact_mod_cast hpos
    simpa [Contains] using And.intro (mul_le_mul_of_nonneg_left h.1 hk) (mul_le_mul_of_nonneg_left h.2 hk)
  next hneg =>
    have hk : (k:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hneg))
    simpa [Contains] using And.intro (mul_le_mul_of_nonpos_left h.2 hk) (mul_le_mul_of_nonpos_left h.1 hk)

theorem shifted {b : Bounds} {x : ℝ} (a : Rat) (h : Contains b x) : Contains (shift a b) ((a:ℝ)+x) := by
  simpa [Contains,shift] using And.intro (add_le_add_left h.1 (a:ℝ)) (add_le_add_left h.2 (a:ℝ))

def disc (p : Piece) (s : State) := (p.linear:ℝ)*p.linear-4*p.quadratic*s.V

theorem disc_fits {p s} (h : fits p s) : Contains (discriminant p) (disc p s) := by
  simpa [discriminant,disc,sub_eq_add_neg] using shifted (p.linear*p.linear) (scaled (-4*p.quadratic) h.2.1)

theorem sqrt_fits {b out} {x : ℝ} (computed : rootBox b = some out) (h : Contains b x) :
    Contains out (Real.sqrt x) := by
  obtain ⟨l,hl,rest⟩ := Option.bind_eq_some.mp computed
  obtain ⟨u,hu,eq⟩ := Option.bind_eq_some.mp rest
  cases eq
  exact ⟨le_trans (MemberDiagram.Sound.sqrt_checked hl).2.1 (Real.sqrt_le_sqrt h.1),
    le_trans (Real.sqrt_le_sqrt h.2) (MemberDiagram.Sound.sqrt_checked hu).2.2⟩

def stationValue (p : Piece) (s : State) : Station → ℝ
  | .fixed t => t
  | .linearRoot => (-1/(p.linear:ℝ))*s.V
  | .quadraticRoot plus => -(p.linear:ℝ)/(2*p.quadratic) +
      ((if plus then 1 else -1)/(2*(p.quadratic:ℝ))) * Real.sqrt (disc p s)

theorem station_fits {p s r box} (h : fits p s) (computed : stationBox p r = some box) :
    Contains box (stationValue p s r) := by
  cases r with
  | fixed t => cases computed; exact singleton_fits t
  | linearRoot => cases computed; simpa [stationValue] using scaled (-1/p.linear) h.2.1
  | quadraticRoot plus =>
    obtain ⟨d,hd,eq⟩ := Option.bind_eq_some.mp computed
    cases eq
    have root := sqrt_fits hd (disc_fits h)
    cases plus
    · simpa [stationValue] using shifted (-p.linear/(2*p.quadratic)) (scaled (-1/(2*p.quadratic)) root)
    · simpa [stationValue] using shifted (-p.linear/(2*p.quadratic)) (scaled (1/(2*p.quadratic)) root)

theorem evaluate_fits {bits p s m t box out} (h : fits p s) (ht : Contains box t)
    (computed : evaluate bits p m box = some out) : Contains out (field p s m t) := by
  let state : Fin 4 → ℝ := ![s.V,s.M,s.L,t]
  have inputs : ∀ i, Contains (values p box i) (state i) := by
    intro i
    fin_cases i
    · exact h.2.1
    · exact h.2.2.1
    · exact h.1
    · exact ht
  have enclosed := FrameIntervalExpressionSound.enclose_contains (quantity p m) computed inputs
  cases m <;> simpa [quantity,FrameIntervalExpressionSound.evaluate,state,field,moment,shear,span] using enclosed

#print axioms station_fits
#print axioms evaluate_fits
end
end InclinedDiagram.Sound
