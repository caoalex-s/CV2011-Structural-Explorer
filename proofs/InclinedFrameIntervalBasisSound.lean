import InclinedFrameIntervalBasis
import FrameIntervalTrigSound
import InclinedFrameAssemblySound

/-! Unit-column correspondence with the checked source basis. Point and slot
    equality are exact; the only nonrational entries are the source tangent. -/
namespace InclinedFrameIntervalBasisSound
open InclinedFrameSource InclinedFrameBasis FrameEnclosure
noncomputable section

def synthesizedValues (basis : PointBasis) (amplitudes : Fin 3 → Rat) : FrameTransform.Triple :=
  ![if basis.translation = 0 then (amplitudes 0 : ℝ)
      else if basis.translation = 1 then -ExactGeometry.degreeSin basis.normal * (amplitudes 0 : ℝ) else 0,
    if basis.translation = 0 then (amplitudes 1 : ℝ)
      else if basis.translation = 1 then ExactGeometry.degreeCos basis.normal * (amplitudes 0 : ℝ) else 0,
    (amplitudes 2 : ℝ)]

theorem synthesize_contains {bits : Nat} {basis : PointBasis} {amplitudes : Fin 3 → Rat}
    {out : Fin 3 → FrameIntervalOps.Bounds}
    (h : InclinedFrameIntervalBasis.synthesize bits basis amplitudes = some out) :
    ∀ i, Contains (out i) (synthesizedValues basis amplitudes i) := by
  unfold InclinedFrameIntervalBasis.synthesize at h
  obtain ⟨first, hfirst, remainder⟩ := Option.bind_eq_some.mp h
  obtain ⟨second, hsecond, remainder⟩ := Option.bind_eq_some.mp remainder
  obtain ⟨rotation, hrotation, remainder⟩ := Option.bind_eq_some.mp remainder
  have hf := executable_point_contains hfirst
  have hs := executable_point_contains hsecond
  have hr := executable_point_contains hrotation
  split at remainder
  next hfree =>
    have hout := Option.some.inj remainder
    subst out
    intro i
    fin_cases i <;> simp only [synthesizedValues, hfree, if_true]
    · simpa using hf
    · simpa using hs
    · simpa using hr
  next hnotFree =>
    split at remainder
    next htangent =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at remainder
      obtain ⟨axes, haxes, zero, hzero, negativeSine, hnegative,
        horizontal, hhorizontal, vertical, hvertical, hout⟩ := remainder
      subst out
      obtain ⟨hsine, hcosine⟩ := FrameIntervalTrigSound.degreeAxesGeneral_contains haxes
      have hz : Contains zero (0 : ℝ) := by simpa using executable_point_contains hzero
      have hn : Contains negativeSine (-ExactGeometry.degreeSin basis.normal) := by
        simpa [ExactGeometry.degreeSin] using executable_subtract_contains hnegative hz hsine
      have hx := executable_multiply_contains hhorizontal hn hf
      have hy := executable_multiply_contains hvertical hcosine hf
      intro i
      fin_cases i
      · simpa [synthesizedValues, hnotFree, htangent] using hx
      · simpa [synthesizedValues, hnotFree, htangent, ExactGeometry.degreeCos] using hy
      · simpa [synthesizedValues] using hr
    next hnotTangent =>
      obtain ⟨zero, hzero, hout⟩ := Option.bind_eq_some.mp remainder
      have hout' := Option.some.inj hout
      subst out
      have hz : Contains zero (0 : ℝ) := by simpa using executable_point_contains hzero
      intro i
      fin_cases i
      · simpa [synthesizedValues, hnotFree, hnotTangent] using hz
      · simpa [synthesizedValues, hnotFree, hnotTangent] using hz
      · simpa [synthesizedValues] using hr

theorem pointAmplitude_source {data : Partition} {basis : GlobalBasis}
    (h : GlobalBasisValid data basis) (column : Fin basis.columns.size)
    (point : Fin data.points.size) (slot : Fin 3) :
    (InclinedFrameIntervalBasis.pointAmplitude data basis column point.val slot : ℝ) =
      InclinedFrameGlobalBasis.amplitude basis.points[point.val]!
        (fun localIndex => InclinedFrameReduced.unit data basis (InclinedFrameGlobalBasis.columnIndex h column)
          ⟨(point, localIndex.val), localIndex.property⟩) slot := by
  by_cases hactive : Active basis.points[point.val]! slot
  · simp [InclinedFrameIntervalBasis.pointAmplitude, InclinedFrameGlobalBasis.amplitude,
      InclinedFrameReduced.unit, InclinedFrameGlobalBasis.columnIndex, hactive, point.isLt,
      Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff, and_assoc, and_left_comm, and_comm]
    split_ifs <;> norm_num
  · simp [InclinedFrameIntervalBasis.pointAmplitude, InclinedFrameGlobalBasis.amplitude, hactive]

theorem pointColumn_contains {bits : Nat} {data : Partition} {basis : GlobalBasis}
    (h : GlobalBasisValid data basis) {column : Fin basis.columns.size}
    {point : Fin data.points.size} {out : Fin 3 → FrameIntervalOps.Bounds}
    (hcolumn : InclinedFrameIntervalBasis.pointColumn bits data basis column point.val = some out) :
    ∀ i, Contains (out i)
      (InclinedFrameGlobalBasis.embed data basis
        (InclinedFrameReduced.unit data basis (InclinedFrameGlobalBasis.columnIndex h column)) point i) := by
  have hvalues := synthesize_contains hcolumn
  intro i
  simpa only [synthesizedValues, InclinedFrameGlobalBasis.embed, InclinedFrameGlobalBasis.synthesize,
    pointAmplitude_source h] using hvalues i

end
end InclinedFrameIntervalBasisSound
