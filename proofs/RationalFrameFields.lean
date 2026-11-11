import RationalFrameModel
import LocalFrameFields

/-! Exact rational element coefficients and the uniform loaded recovery
    formulas used by the executable checker, connected to the existing
    Euler–Bernoulli polynomial fields. This is a local bridge, not the global
    source/coordinate/constraint acceptance theorem. -/
namespace RationalFrame.Fields
noncomputable section

set_option maxHeartbeats 2000000 in
theorem stiffness_cast (segment : Segment) (i j : Fin 6) :
    (localStiffness segment i j : ℝ) = LocalFrameFields.stiffness
      (segment.length : ℝ) (segment.EA : ℝ) (segment.EI : ℝ) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [localStiffness, LocalFrameFields.stiffness, pow_succ] <;> ring

theorem force_cast (segment : Segment) (i : Fin 6) :
    (localForce segment i : ℝ) = LocalFrameFields.consistentLoad (segment.length : ℝ)
      ((segment.sine * segment.vertical : Rat) : ℝ) ((segment.sine * segment.vertical : Rat) : ℝ)
      ((segment.cosine * segment.vertical : Rat) : ℝ) ((segment.cosine * segment.vertical : Rat) : ℝ) i := by
  fin_cases i <;> norm_num [localForce, LocalFrameFields.consistentLoad, pow_two] <;> ring

set_option maxHeartbeats 4000000 in
/-- All six loaded readouts follow from the actual field-derived end actions.
    The particular terms remain even when every nodal motion is restrained. -/
theorem uniform_recovery (d : FrameInterfaces.LocalDofs) (L EA EI p q x : ℝ)
    (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0) :
    let action := LocalFrameFields.endActions d L EA EI p p q q
    (LocalFrameFields.normal d L EA p p).eval x = -action 0 - p*x ∧
    (LocalFrameFields.shear d L EI q q).eval x = action 1 + q*x ∧
    (LocalFrameFields.moment d L EI q q).eval x = -action 2 + action 1*x + q*x^2/2 ∧
    (LocalFrameFields.rotation d L EI q q).eval x = d 2 + (-action 2*x + action 1*x^2/2 + q*x^3/6)/EI ∧
    (LocalFrameFields.axialDisplacement d L EA p p).eval x = d 0 + (-action 0*x - p*x^2/2)/EA ∧
    (LocalFrameFields.transverseDisplacement d L EI q q).eval x =
      d 1 + d 2*x + (-action 2*x^2/2 + action 1*x^3/6 + q*x^4/24)/EI := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [LocalFrameFields.endActions, LocalFrameFields.normal, LocalFrameFields.shear,
      LocalFrameFields.moment, LocalFrameFields.rotation, LocalFrameFields.axialDisplacement,
      LocalFrameFields.transverseDisplacement, LocalFrameFields.coordinate,
      Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.C_eq_natCast]
    field_simp [hL, hEA, hEI]
    ring

end
end RationalFrame.Fields
