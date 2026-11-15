import FrameIntervalAccuracy
import FrameEnclosure

namespace FrameIntervalAccuracySound
open FrameIntervalAccuracy FrameEnclosure
noncomputable section

theorem check_error {quantity : Fin 9} {bounds : FrameIntervalOps.Bounds} {actual : ℝ}
    (hcheck : check quantity bounds = true) (hcontains : Contains bounds actual) :
    |actual - (midpoint bounds : ℝ)| ≤ (absoluteTolerance quantity : ℝ) +
      (relativeTolerance : ℝ) * |actual| := by
  have hchecks : FrameIntervalOps.valid bounds = true ∧ radius bounds ≤
      absoluteTolerance quantity + relativeTolerance *
        FrameIntervalOps.upperOf 0 (FrameIntervalOps.upperOf (-midpoint bounds) (midpoint bounds) - radius bounds) :=
    of_decide_eq_true hcheck
  have habsolute : FrameIntervalOps.upperOf (-midpoint bounds) (midpoint bounds) = |midpoint bounds| := by
    rw [upperOf_eq_max, max_comm, ← abs_eq_max_neg]
  have hgate := hchecks.2
  rw [habsolute, upperOf_eq_max] at hgate
  have hgateReal : (radius bounds : ℝ) ≤ (absoluteTolerance quantity : ℝ) +
      (relativeTolerance : ℝ) * max 0 (|(midpoint bounds : ℝ)| - (radius bounds : ℝ)) := by
    exact_mod_cast hgate
  have herror : |actual - (midpoint bounds : ℝ)| ≤ (radius bounds : ℝ) := by
    simpa [FrameIntervalAccuracy.midpoint, radius] using midpoint_error hcontains
  exact accuracy_gate herror (by norm_num [relativeTolerance]) hgateReal

end
end FrameIntervalAccuracySound
