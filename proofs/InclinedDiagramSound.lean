import InclinedDiagramWire
import MemberDiagramSound
import FrameIntervalExpressionSound
import FrameSpringSound
import InclinedReleaseFields

namespace InclinedDiagram.Sound
open FrameIntervalOps Set
open FrameEnclosure (Contains)
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

open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly

/-- The initial forces are the physical element end actions. Rotations may
be independent at a release or coupled by a spring; the premise only asks
for enclosures of the solved point motion on the actual assembly. -/
def physicalState (data : Partition) (motion : InclinedFrameReal.Motion data)
    (index : Fin data.pieces.size) : State :=
  let segment := data.pieces[index.val]!
  let member := data.source.members[segment.member]!
  let direction := InclinedFrameReal.memberDirection data segment.member
  let actions := LocalFrameFields.endActions (InclinedFrameReal.pieceMotion data segment motion)
    (InclinedFrameReal.pieceLength data segment) member.EA member.EI
    (direction.sine*segment.vertical) (direction.sine*segment.verticalEnd)
    (direction.cosine*segment.vertical) (direction.cosine*segment.verticalEnd)
  ⟨InclinedFrameReal.memberLength data segment.member, actions 1, -(actions 2)⟩

theorem fromSource_fits {data : Partition} {basis : GlobalBasis} {bits : Nat}
    {cert : Certificate data basis} {index : Fin data.pieces.size}
    {p : InclinedDiagram.Piece} (physical : InclinedFrameReal.Motion data)
    (partition : PartitionValid data) (geometry : GeometryChecks bits cert)
    (loads : LoadChecks bits cert) (nodes : InclinedRelease.Fields.NodeEnclosures bits cert physical)
    (computed : fromSource bits cert index = some p) : fits p (physicalState data physical index) := by
  unfold fromSource at computed
  dsimp only at computed

  obtain ⟨motionBox, hl, rest⟩ := Option.bind_eq_some.mp computed
  obtain ⟨v, hv, rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨negM, hn, rest⟩ := Option.bind_eq_some.mp rest
  obtain ⟨root, hr, eq⟩ := Option.bind_eq_some.mp rest
  cases eq
  have motion := InclinedRelease.Fields.localMotion_contains physical geometry nodes hl
  have shearBound := InclinedRelease.Fields.endAction_contains partition physical geometry loads motion hv
  have momentBound := InclinedRelease.Fields.endAction_contains partition physical geometry loads motion hn
  rcases partition with ⟨hsource, _, _, _, _, _, _, pieces, _, _, _, _⟩
  have segment := pieces index
  refine ⟨(InclinedFrameIntervalGeometrySound.member_contains hr).1,shearBound,?_,
    InclinedFrameReal.member_positive data hsource ⟨_,segment.1.1⟩,segment.2.2.2.1⟩
  simpa [physicalState] using scaled (-1) momentBound

/-- Integrate the actual local affine load through the piece. The two
variable shear coefficients use the horizontal source projection because
the physical member length times its direction cosine is exactly ΔX. -/
theorem normalized_fields (motion : FrameInterfaces.LocalDofs)
    (L fraction EA EI c sn dx f₀ f₁ t : ℝ) (length : L*fraction ≠ 0)
    (axial : EA ≠ 0) (bending : EI ≠ 0) (horizontal : L*c = dx) :
    let ell := L*fraction
    let B := dx*fraction*f₀
    let C := dx*fraction*(f₁-f₀)/2
    let actions := LocalFrameFields.endActions motion ell EA EI (sn*f₀) (sn*f₁) (c*f₀) (c*f₁)
    (LocalFrameFields.shear motion ell EI (c*f₀) (c*f₁)).eval (ell*t) = actions 1+t*(B+t*C) ∧
    (LocalFrameFields.moment motion ell EI (c*f₀) (c*f₁)).eval (ell*t) =
      -(actions 2)+ell*t*(actions 1+t*(B/2+t*(C/3))) := by
  subst dx
  have h := RationalFrame.Fields.affine_recovery motion (L*fraction) EA EI
    (sn*f₀) (sn*f₁) (c*f₀) (c*f₁) (L*fraction*t) length axial bending
  dsimp only
  constructor
  · rw [h.2.1]
    field_simp [length]
    ring
  · rw [h.2.2.1]
    field_simp [length]
    ring

#print axioms normalized_fields
#print axioms fromSource_fits
#print axioms station_fits
#print axioms evaluate_fits
end
end InclinedDiagram.Sound
