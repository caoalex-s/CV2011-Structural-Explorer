import FrameIntervalElement
import FrameEnclosure

/-! Local stiffness containment targets the established physical field matrix,
    rather than a stiffness evaluated at rounded geometric inputs. -/
namespace FrameIntervalElementSound
open FrameIntervalOps FrameIntervalElement FrameEnclosure
noncomputable section

def ContainsCoefficients (values : Coefficients) (L EA EI : ℝ) : Prop :=
  Contains values.axial (EA/L) ∧ Contains values.bending (12*EI/L^3) ∧
  Contains values.coupling (6*EI/L^2) ∧ Contains values.rotation (4*EI/L) ∧
  Contains values.crossRotation (2*EI/L)

theorem coefficients_contains {bits : Nat} {length : FrameIntervalOps.Bounds} {EA EI : Rat}
    {out : Coefficients} {L : ℝ}
    (h : coefficients bits length EA EI = some out) (hL : Contains length L) :
    ContainsCoefficients out L EA EI := by
  -- Expose each checked arithmetic step once, avoiding repeated simplification
  -- of the entire long bind chain and its dependent intermediate expressions.
  unfold coefficients at h
  obtain ⟨axialRigidity, hEA, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨bendingRigidity, hEI, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨twelve, h12, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨six, h6, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨four, h4, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨two, h2, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨squared, hsquared, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨cubed, hcubed, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨bendingNumerator, hbendingNumerator, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨couplingNumerator, hcouplingNumerator, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨rotationNumerator, hrotationNumerator, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨axial, haxial, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨bending, hbending, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨coupling, hcoupling, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨rotation, hrotation, h⟩ := Option.bind_eq_some.mp h
  obtain ⟨crossRotation, hcrossRotation, h⟩ := Option.bind_eq_some.mp h
  have hout := Option.some.inj h
  subst out
  have hEAContains := executable_point_contains hEA
  have hEIContains := executable_point_contains hEI
  have htwelve : Contains twelve (12 : ℝ) := by simpa using executable_point_contains h12
  have hsix : Contains six (6 : ℝ) := by simpa using executable_point_contains h6
  have hfour : Contains four (4 : ℝ) := by simpa using executable_point_contains h4
  have htwo : Contains two (2 : ℝ) := by simpa using executable_point_contains h2
  have hlengthSquared := executable_multiply_contains hsquared hL hL
  have hlengthCubed := executable_multiply_contains hcubed hlengthSquared hL
  have ha := executable_divide_contains haxial hEAContains hL
  have hb := executable_divide_contains hbending
    (executable_multiply_contains hbendingNumerator htwelve hEIContains) hlengthCubed
  have hc := executable_divide_contains hcoupling
    (executable_multiply_contains hcouplingNumerator hsix hEIContains) hlengthSquared
  have hd := executable_divide_contains hrotation
    (executable_multiply_contains hrotationNumerator hfour hEIContains) hL
  have he := executable_divide_contains hcrossRotation hd htwo
  have hcrossIdentity : (4*(EI : ℝ)/L)/2 = 2*(EI : ℝ)/L := by ring
  rw [hcrossIdentity] at he
  exact ⟨ha, by simpa [pow_succ, pow_two] using hb,
    by simpa [pow_two] using hc, hd, he⟩

theorem negative_contains {a : FrameIntervalOps.Bounds} {x : ℝ} (h : Contains a x) : Contains (negative a) (-x) := by
  constructor <;> dsimp [Contains, negative] at * <;> push_cast <;> linarith

theorem entry_contains {values : Coefficients} {L EA EI : ℝ}
    (h : ContainsCoefficients values L EA EI) (i j : Fin 6) :
    Contains (entry values i j) (LocalFrameFields.stiffness L EA EI i j) := by
  rcases h with ⟨ha, hb, hc, hd, he⟩
  have hna := negative_contains ha
  have hnb := negative_contains hb
  have hnc := negative_contains hc
  fin_cases i <;> fin_cases j <;>
    simp [entry, LocalFrameFields.stiffness, Contains, zero, neg_div] at * <;> assumption

end
end FrameIntervalElementSound
