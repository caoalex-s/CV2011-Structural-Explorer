import InclinedFrameIntervalReport
import InclinedFrameIntervalWireSound

/-! Successful report bytes come from the same source-bound checked outputs.
    A browser must decode these exact bytes and retain the input snapshot binding. -/
namespace InclinedFrameIntervalReportSound
open InclinedFrameIntervalWire InclinedFrameIntervalReport InclinedFrameIntervalWireSound
noncomputable section

theorem checkReport_sound {input report : String} (h : checkReport input = some report) :
    ∃ value result, decode input = some value ∧ checkPacket value = some result ∧
      Correct value result ∧ report = encode value result := by
  unfold checkReport at h
  obtain ⟨value, hdecode, remainder⟩ := Option.bind_eq_some.mp h
  obtain ⟨result, hchecked, remainder⟩ := Option.bind_eq_some.mp remainder
  dsimp only at remainder
  split at remainder
  · have equality := Option.some.inj remainder
    exact ⟨value, result, hdecode, hchecked, checkPacket_sound hchecked, equality.symm⟩
  · cases remainder

end
end InclinedFrameIntervalReportSound
