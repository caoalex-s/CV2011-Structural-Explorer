import FrameIntervalExpression
import FrameEnclosure

namespace FrameIntervalExpressionSound
open FrameIntervalExpression FrameEnclosure
noncomputable section

def evaluate {inputs : Nat} (values : Fin inputs → ℝ) : Expression inputs → ℝ
  | .input index => values index
  | .constant value => value
  | .add left right => evaluate values left + evaluate values right
  | .subtract left right => evaluate values left - evaluate values right
  | .multiply left right => evaluate values left * evaluate values right
  | .divide left right => evaluate values left / evaluate values right

theorem enclose_contains {inputs bits : Nat} {bounds : Fin inputs → FrameIntervalOps.Bounds}
    {values : Fin inputs → ℝ} (expression : Expression inputs) {out : FrameIntervalOps.Bounds}
    (h : enclose bits bounds expression = some out) (hvalues : ∀ i, Contains (bounds i) (values i)) :
    Contains out (evaluate values expression) := by
  induction expression generalizing out with
  | input index =>
    have hout := Option.some.inj h
    subst out
    exact hvalues index
  | constant value => exact executable_point_contains h
  | add left right ihleft ihright =>
    obtain ⟨a, ha, b, hb, hout⟩ := by
      simpa only [enclose, Option.bind_eq_bind, Option.bind_eq_some] using h
    exact executable_add_contains hout (ihleft ha) (ihright hb)
  | subtract left right ihleft ihright =>
    obtain ⟨a, ha, b, hb, hout⟩ := by
      simpa only [enclose, Option.bind_eq_bind, Option.bind_eq_some] using h
    exact executable_subtract_contains hout (ihleft ha) (ihright hb)
  | multiply left right ihleft ihright =>
    obtain ⟨a, ha, b, hb, hout⟩ := by
      simpa only [enclose, Option.bind_eq_bind, Option.bind_eq_some] using h
    exact executable_multiply_contains hout (ihleft ha) (ihright hb)
  | divide left right ihleft ihright =>
    obtain ⟨a, ha, b, hb, hout⟩ := by
      simpa only [enclose, Option.bind_eq_bind, Option.bind_eq_some] using h
    exact executable_divide_contains hout (ihleft ha) (ihright hb)

end
end FrameIntervalExpressionSound
