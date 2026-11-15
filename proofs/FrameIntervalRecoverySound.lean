import FrameIntervalRecovery
import FrameIntervalExpressionSound
import RationalFrameFields

/-! Reuse the established affine field identity. This module does not replace
    a physical length by a rational approximation or drop particular fields. -/
namespace FrameIntervalRecoverySound
open FrameIntervalRecovery FrameIntervalExpressionSound FrameEnclosure
noncomputable section

def inputs (d : FrameInterfaces.LocalDofs) (L EA EI p pEnd q qEnd x c s : ℝ) : Fin 15 → ℝ :=
  let action := LocalFrameFields.endActions d L EA EI p pEnd q qEnd
  ![action 0, action 1, action 2, d 0, d 1, d 2, p, (pEnd-p)/L, q, (qEnd-q)/L, x, EA, EI, c, s]

def actualFields (d : FrameInterfaces.LocalDofs) (L EA EI p pEnd q qEnd x c s : ℝ) : Fin 6 → ℝ :=
  let axial := (LocalFrameFields.axialDisplacement d L EA p pEnd).eval x
  let transverse := (LocalFrameFields.transverseDisplacement d L EI q qEnd).eval x
  ![(LocalFrameFields.normal d L EA p pEnd).eval x,
    (LocalFrameFields.shear d L EI q qEnd).eval x,
    (LocalFrameFields.moment d L EI q qEnd).eval x,
    (LocalFrameFields.rotation d L EI q qEnd).eval x,
    c*axial-s*transverse, s*axial+c*transverse]

theorem expression_fields (d : FrameInterfaces.LocalDofs) (L EA EI p pEnd q qEnd x c s : ℝ)
    (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0) (component : Fin 6) :
    evaluate (inputs d L EA EI p pEnd q qEnd x c s) (expressions component) =
      actualFields d L EA EI p pEnd q qEnd x c s component := by
  obtain ⟨normal, shear, moment, rotation, axial, transverse⟩ :=
    RationalFrame.Fields.affine_recovery d L EA EI p pEnd q qEnd x hL hEA hEI
  fin_cases component <;>
    simp [expressions, evaluate, inputs, actualFields, normal, shear, moment, rotation, axial, transverse] <;> ring

theorem field_contains {bits : Nat} {bounds : Fin 15 → FrameIntervalOps.Bounds}
    {d : FrameInterfaces.LocalDofs} {L EA EI p pEnd q qEnd x c s : ℝ}
    (hL : L ≠ 0) (hEA : EA ≠ 0) (hEI : EI ≠ 0)
    (hinputs : ∀ i, Contains (bounds i) (inputs d L EA EI p pEnd q qEnd x c s i))
    {component : Fin 6} {out : FrameIntervalOps.Bounds}
    (h : field bits bounds component = some out) :
    Contains out (actualFields d L EA EI p pEnd q qEnd x c s component) := by
  rw [← expression_fields d L EA EI p pEnd q qEnd x c s hL hEA hEI component]
  exact enclose_contains (expressions component) h hinputs

end
end FrameIntervalRecoverySound
