import InclinedFrameBasis
import FrameAdmissiblePoint

/-! Every owned source restraint participates in the local translation kernel.
    Global column allocation and assembly remain separate obligations. -/
namespace InclinedFrameBasisSound
open InclinedFrameSource InclinedFrameBasis FrameAdmissiblePoint
noncomputable section

def sourceNormalWork (angle : Rat) (x y : ℝ) : ℝ :=
  normalWork (ExactGeometry.degreeCos (angle : ℝ)) (ExactGeometry.degreeSin (angle : ℝ)) x y

def TranslationAllows (data : Partition) (point : Nat) (x y : ℝ) : Prop :=
  ∀ i : Fin data.source.supports.size, owned data point i →
    if data.source.supports[i.val]!.kind = 2 then sourceNormalWork data.source.supports[i.val]!.angle x y = 0
    else x = 0 ∧ y = 0

theorem canonical_row {angle : Rat} {value : AngleClass} (h : ClassValid angle value) (x y : ℝ) :
    sourceNormalWork angle x y = 0 ↔ sourceNormalWork value.angle x y = 0 := by
  have halias : (angle : ℝ) = (value.angle : ℝ) + 180*(value.turns : ℝ) := by
    exact_mod_cast h.2.2
  exact degree_alias_kernel _ _ x y value.turns halias

theorem free_translation {data : Partition} {point : Nat} {basis : PointBasis}
    (h : BasisValid data point basis) (hmode : basis.translation = 0) (x y : ℝ) :
    TranslationAllows data point x y := by
  have hnone : ∀ i : Fin data.source.supports.size, ¬owned data point i := by
    simpa [hmode] using h.2.2.2
  intro i hi
  exact False.elim (hnone i hi)

theorem tangent_translation {data : Partition} {point : Nat} {basis : PointBasis}
    (h : BasisValid data point basis) (hmode : basis.translation = 1) (x y : ℝ) :
    TranslationAllows data point x y ↔
    ∃ alpha, x = -ExactGeometry.degreeSin (basis.normal : ℝ)*alpha ∧
      y = ExactGeometry.degreeCos (basis.normal : ℝ)*alpha := by
  have hc : 0 ≤ basis.normal ∧ basis.normal < 180 ∧
      (∃ i : Fin data.source.supports.size, owned data point i) ∧
      (∀ i : Fin data.source.supports.size, owned data point i →
        data.source.supports[i.val]!.kind = 2 ∧
        (canonical data.source.supports[i.val]!.angle).angle = basis.normal) := by
    simpa [hmode] using h.2.2.2
  constructor
  · intro hall
    obtain ⟨i, hi⟩ := hc.2.2.1
    have hkind := (hc.2.2.2 i hi).1
    have hwork : sourceNormalWork data.source.supports[i.val]!.angle x y = 0 := by
      simpa [hkind] using hall i hi
    have hcanonical := (canonical_row (h.2.1 i hi).2 x y).mp hwork
    rw [(hc.2.2.2 i hi).2] at hcanonical
    exact ⟨tangentCoordinate (ExactGeometry.degreeCos (basis.normal : ℝ))
      (ExactGeometry.degreeSin (basis.normal : ℝ)) x y,
      single_normal_kernel (ExactGeometry.degree_axis_normalized _) hcanonical⟩
  · rintro ⟨alpha, hx, hy⟩ i hi
    have hkind := (hc.2.2.2 i hi).1
    simp only [hkind, if_pos rfl]
    apply (canonical_row (h.2.1 i hi).2 x y).mpr
    rw [(hc.2.2.2 i hi).2, hx, hy]
    exact tangent_admissible _ _ alpha

theorem blocked_translation {data : Partition} {point : Nat} {basis : PointBasis}
    (h : BasisValid data point basis) (hmode : basis.translation = 2) (x y : ℝ) :
    TranslationAllows data point x y ↔ x = 0 ∧ y = 0 := by
  have hc :
      (∃ i : Fin data.source.supports.size, owned data point i ∧ data.source.supports[i.val]!.kind ≤ 1) ∨
      (∃ i j : Fin data.source.supports.size, owned data point i ∧ owned data point j ∧
        data.source.supports[i.val]!.kind = 2 ∧ data.source.supports[j.val]!.kind = 2 ∧
        (canonical data.source.supports[i.val]!.angle).angle ≠
          (canonical data.source.supports[j.val]!.angle).angle) := by
    simpa [hmode] using h.2.2.2
  constructor
  · intro hall
    rcases hc with ⟨i, hi, hkind⟩ | ⟨i, j, hi, hj, hki, hkj, hdistinct⟩
    · have hn : data.source.supports[i.val]!.kind ≠ 2 := by omega
      simpa [hn] using hall i hi
    · have hfirst := (h.2.1 i hi).2
      have hsecond := (h.2.1 j hj).2
      have hwi : sourceNormalWork data.source.supports[i.val]!.angle x y = 0 := by
        simpa [hki] using hall i hi
      have hwj : sourceNormalWork data.source.supports[j.val]!.angle x y = 0 := by
        simpa [hkj] using hall j hj
      apply two_normals_kernel ((canonical_row hfirst x y).mp hwi)
        ((canonical_row hsecond x y).mp hwj)
      apply canonical_normals_independent
      · constructor
        · exact_mod_cast hfirst.1
        · exact_mod_cast hfirst.2.1
      · constructor
        · exact_mod_cast hsecond.1
        · exact_mod_cast hsecond.2.1
      · exact_mod_cast hdistinct
  · rintro ⟨rfl, rfl⟩ i hi
    split <;> simp [sourceNormalWork, normalWork]

def RotationAllows (data : Partition) (point : Nat) (rotation : ℝ) : Prop :=
  ∀ i : Fin data.source.supports.size, owned data point i →
    data.source.supports[i.val]!.kind = 1 → rotation = 0

theorem rotation_kernel {data : Partition} {point : Nat} {basis : PointBasis}
    (h : BasisValid data point basis) (rotation : ℝ) :
    RotationAllows data point rotation ↔ basis.rotationFree = true ∨ rotation = 0 := by
  constructor
  · intro hall
    by_cases hr : basis.rotationFree = true
    · exact Or.inl hr
    · have hnot : ¬∀ i : Fin data.source.supports.size,
          owned data point i → data.source.supports[i.val]!.kind ≠ 1 := by
        intro hnone
        exact hr (h.2.2.1.mpr hnone)
      push_neg at hnot
      obtain ⟨i, hi, hkind⟩ := hnot
      exact Or.inr (hall i hi hkind)
  · rintro (hfree | hz) i hi hkind
    · exact False.elim ((h.2.2.1.mp hfree i hi) hkind)
    · exact hz

end
end InclinedFrameBasisSound
