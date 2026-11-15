import InclinedFrameIntervalBuild
import InclinedFrameIntervalOutputsSound

/-! The reconstruction algorithm is only a proposal producer. This bridge
    exposes the acceptance check that dominates every successful return. -/
namespace InclinedFrameIntervalBuildSound
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalBuild
open InclinedFrameIntervalOutputs InclinedFrameIntervalOutputsSound
noncomputable section

theorem checked_certificate {data : Partition} {basis : GlobalBasis} {bits : Nat}
    {proposal : Proposal data basis} {query : RationalFrame.Query} {outputs : Outputs data}
    (h : checked bits proposal query = some outputs) :
    ∃ certificate : InclinedFrameIntervalAssembly.Certificate data basis,
      build bits proposal = some certificate ∧ accepts bits certificate query outputs = true := by
  unfold checked at h
  obtain ⟨certificate, hcertificate, remainder⟩ := Option.bind_eq_some.mp h
  obtain ⟨fields, _, remainder⟩ := Option.bind_eq_some.mp remainder
  obtain ⟨reactions, _, remainder⟩ := Option.bind_eq_some.mp remainder
  dsimp only at remainder
  split at remainder
  next accepted =>
    have equality := Option.some.inj remainder
    subst outputs
    exact ⟨certificate, hcertificate, accepted⟩
  · cases remainder

theorem checked_sound {data : Partition} {basis : GlobalBasis} {bits : Nat}
    {proposal : Proposal data basis} {query : RationalFrame.Query} {outputs : Outputs data}
    (h : checked bits proposal query = some outputs) :
    ∃ motion : InclinedFrameReal.Motion data,
      InclinedFrameReduced.Equilibrium data motion ∧
      (∀ other, InclinedFrameReduced.Equilibrium data other → other = motion) ∧
      FieldReadouts data query outputs motion ∧ ReactionReadouts data outputs motion ∧
      ∀ variation, InclinedFrameGlobalBasis.SourceAllows data variation → variation ≠ 0 →
        0 < InclinedFrameReal.stiffnessWork data variation variation := by
  obtain ⟨certificate, _, accepted⟩ := checked_certificate h
  exact accepts_sound accepted

/-- The outer decoder must use this original source and query unchanged.
    No producer-created partition or displayed substitute is covered here. -/
theorem checked_source_sound {data : Partition} {basis : GlobalBasis} {bits : Nat}
    (source : RationalFrame.Source) (hsource : checkedPartition source = some data)
    {proposal : Proposal data basis} {query : RationalFrame.Query} {outputs : Outputs data}
    (h : checked bits proposal query = some outputs) :
    data.source = source ∧ ∃ motion : InclinedFrameReal.Motion data,
      InclinedFrameReduced.Equilibrium data motion ∧
      (∀ other, InclinedFrameReduced.Equilibrium data other → other = motion) ∧
      FieldReadouts data query outputs motion ∧ ReactionReadouts data outputs motion ∧
      ∀ variation, InclinedFrameGlobalBasis.SourceAllows data variation → variation ≠ 0 →
        0 < InclinedFrameReal.stiffnessWork data variation variation :=
  ⟨(checkedPartition_source hsource).1, checked_sound h⟩

end
end InclinedFrameIntervalBuildSound
