import InclinedFrameIntervalWire
import InclinedFrameIntervalBuildSound

/-! Bind successful compact packets to their original decoded source and query.
    Browser snapshot identity and exact readout serialization are outer duties. -/
namespace InclinedFrameIntervalWireSound
open InclinedFrameIntervalWire InclinedFrameIntervalOutputsSound
noncomputable section

def Correct (value : Packet) (result : Result) : Prop :=
  result.data.source = value.source ∧ ∃ motion : InclinedFrameReal.Motion result.data,
    InclinedFrameReduced.Equilibrium result.data motion ∧
    (∀ other, InclinedFrameReduced.Equilibrium result.data other → other = motion) ∧
    FieldReadouts result.data value.query result.outputs motion ∧
    ReactionReadouts result.data result.outputs motion ∧
    ∀ variation, InclinedFrameGlobalBasis.SourceAllows result.data variation → variation ≠ 0 →
      0 < InclinedFrameReal.stiffnessWork result.data variation variation

theorem checkPacket_sound {value : Packet} {result : Result}
    (h : checkPacket value = some result) : Correct value result := by
  unfold checkPacket at h
  obtain ⟨data, hsource, remainder⟩ := Option.bind_eq_some.mp h
  obtain ⟨basis, _, remainder⟩ := Option.bind_eq_some.mp remainder
  split at remainder
  · cases remainder
  · obtain ⟨outputs, hchecked, hresult⟩ := Option.bind_eq_some.mp remainder
    have equality := Option.some.inj hresult
    subst result
    exact InclinedFrameIntervalBuildSound.checked_source_sound value.source hsource hchecked

theorem decodeAndCheck_sound {input : String} {result : Result}
    (h : decodeAndCheck input = some result) :
    ∃ value, decode input = some value ∧ Correct value result := by
  obtain ⟨value, hdecode, hchecked⟩ := Option.bind_eq_some.mp h
  exact ⟨value, hdecode, checkPacket_sound hchecked⟩

end
end InclinedFrameIntervalWireSound
