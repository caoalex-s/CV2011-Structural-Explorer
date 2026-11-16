import InclinedFrameIntervalOutputs
import InclinedFrameIntervalReactionsSound
import FrameIntervalAccuracySound

/-! Output acceptance binds every returned interval to one unique physical
    equilibrium and to the fixed accuracy policy for that same real value. -/
namespace InclinedFrameIntervalOutputsSound
open InclinedFrameSource InclinedFrameBasis InclinedFrameGlobalBasis
open InclinedFrameIntervalAssembly InclinedFrameIntervalEquilibrium InclinedFrameIntervalOutputs FrameEnclosure
noncomputable section

def Accurate (quantity : Fin 9) (bounds : FrameIntervalOps.Bounds) (actual : ℝ) : Prop :=
  Contains bounds actual ∧ |actual - (FrameIntervalAccuracy.midpoint bounds : ℝ)| ≤
    (FrameIntervalAccuracy.absoluteTolerance quantity : ℝ) +
      (FrameIntervalAccuracy.relativeTolerance : ℝ) * |actual|

def FieldReadouts (data : Partition) (query : RationalFrame.Query) (outputs : Outputs data)
    (motion : InclinedFrameReal.Motion data) : Prop :=
  ∃ index : Fin data.pieces.size,
    InclinedFrameIntervalRecovery.selectedPiece data query = some index ∧
    InclinedFrameIntervalRecovery.SideContains data.pieces[index.val]! query ∧
    ∀ component, Accurate (fieldQuantity component) (outputs.fields component)
      (InclinedFrameReal.fieldValues data data.pieces[index.val]! motion query.t component)

def ReactionReadouts (data : Partition) (outputs : Outputs data) (motion : InclinedFrameReal.Motion data) : Prop :=
  ∀ point direction, Accurate (reactionQuantity direction) (outputs.reactions point direction)
    (InclinedFrameReal.groupedReaction data motion point direction)

theorem accepts_sound {bits : Nat} {data : Partition} {basis : GlobalBasis}
    {certificate : Certificate data basis} {query : RationalFrame.Query} {outputs : Outputs data}
    (h : accepts bits certificate query outputs = true) :
    ∃ motion : InclinedFrameReal.Motion data,
      InclinedFrameReduced.Equilibrium data motion ∧
      (∀ other, InclinedFrameReduced.Equilibrium data other → other = motion) ∧
      FieldReadouts data query outputs motion ∧ ReactionReadouts data outputs motion ∧
      ∀ variation, SourceAllows data variation → variation ≠ 0 →
        0 < InclinedFrameReal.stiffnessWork data variation variation := by
  have hsplit : check bits certificate = true ∧ decide (OutputChecks bits certificate query outputs) = true := by
    simpa only [accepts, Bool.and_eq_true] using h
  have houtputs : OutputChecks bits certificate query outputs := of_decide_eq_true hsplit.2
  have hchecks : Checks bits certificate := of_decide_eq_true hsplit.1
  obtain ⟨hpartition, _, hgeometry, hprojection, hload, _, _⟩ := hchecks
  obtain ⟨hbasis, values, hequilibrium, hunique, hbounds⟩ := check_physical_equilibrium hsplit.1
  have hvalues : ∀ column, Contains (certificate.solve.solution column) (values column) := by
    intro column
    simpa only [lift_at_column] using hbounds column
  let motion := embed data basis (liftCoordinates hbasis values)
  refine ⟨motion, hequilibrium, hunique, ?_, ?_, ?_⟩
  · obtain ⟨index, hselected, hside, _⟩ := InclinedFrameIntervalRecoverySound.field_contains
      hpartition hbasis hgeometry hprojection hload hvalues (houtputs.1 0).1
    refine ⟨index, hselected, hside, ?_⟩
    intro component
    obtain ⟨other, hother, _, hcontains⟩ := InclinedFrameIntervalRecoverySound.field_contains
      hpartition hbasis hgeometry hprojection hload hvalues (houtputs.1 component).1
    have hequal : other = index := Option.some.inj (hother.symm.trans hselected)
    subst other
    exact ⟨hcontains, FrameIntervalAccuracySound.check_error (houtputs.1 component).2 hcontains⟩
  · intro point direction
    have hcontains := InclinedFrameIntervalReactionsSound.reaction_contains
      hpartition hbasis hgeometry hprojection hload hvalues (houtputs.2 point direction).1
    exact ⟨hcontains, FrameIntervalAccuracySound.check_error (houtputs.2 point direction).2 hcontains⟩
  · exact check_positive_stiffness hsplit.1

/-- The outer decoder/compiler must supply this successful original-source
    compilation, rather than accepting a producer-created alternative graph. -/
theorem checked_source_outputs {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (source : RationalFrame.Source) (hcompile : checkedPartition source = some data)
    {certificate : Certificate data basis} {query : RationalFrame.Query} {outputs : Outputs data}
    (h : accepts bits certificate query outputs = true) :
    data.source = source ∧ ∃ motion : InclinedFrameReal.Motion data,
      InclinedFrameReduced.Equilibrium data motion ∧
      (∀ other, InclinedFrameReduced.Equilibrium data other → other = motion) ∧
      FieldReadouts data query outputs motion ∧ ReactionReadouts data outputs motion := by
  obtain ⟨motion, hequilibrium, hunique, hfields, hreactions, _⟩ := accepts_sound h
  exact ⟨(checkedPartition_source hcompile).1, motion, hequilibrium, hunique, hfields, hreactions⟩

end
end InclinedFrameIntervalOutputsSound
