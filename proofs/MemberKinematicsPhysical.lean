import MemberKinematicsExtrema

namespace MemberKinematics.Sound
open Set FrameEnclosure
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly
noncomputable section

/-- All quantities refer to the selected side of the original source piece. -/
structure PhysicalPiece where
  dofs : FrameInterfaces.LocalDofs
  length : ℝ
  axial : ℝ
  flexural : ℝ
  p : ℝ
  pEnd : ℝ
  q : ℝ
  qEnd : ℝ
  cosine : ℝ
  sine : ℝ

def physicalPiece (data : Partition) (motion : InclinedFrameReal.Motion data) (i : Fin data.pieces.size) :
    PhysicalPiece :=
  let seg := data.pieces[i.val]!
  let member := data.source.members[seg.member]!
  let dir := InclinedFrameReal.memberDirection data seg.member
  ⟨InclinedFrameReal.pieceMotion data seg motion, InclinedFrameReal.pieceLength data seg,
   member.EA, member.EI, dir.sine*seg.vertical, dir.sine*seg.verticalEnd,
   dir.cosine*seg.vertical, dir.cosine*seg.verticalEnd, dir.cosine, dir.sine⟩

def PhysicalPiece.inputs (h : PhysicalPiece) (x : ℝ) :=
  FrameIntervalRecoverySound.inputs h.dofs h.length h.axial h.flexural h.p h.pEnd h.q h.qEnd x h.cosine h.sine

def PhysicalPiece.field (h : PhysicalPiece) (f : Field) : RealBeamFields.Field :=
  match f with
  | .displacement => LocalFrameFields.transverseDisplacement h.dofs h.length h.flexural h.q h.qEnd
  | .slope => LocalFrameFields.rotation h.dofs h.length h.flexural h.q h.qEnd

def PhysicalPiece.positive (h : PhysicalPiece) := 0 < h.length ∧ 0 < h.axial ∧ 0 < h.flexural

theorem positive_source {data : Partition} (valid : PartitionValid data) (motion : InclinedFrameReal.Motion data)
    (i : Fin data.pieces.size) : (physicalPiece data motion i).positive :=
  InclinedFrameReal.piece_properties data valid i

theorem input_shift (h : PhysicalPiece) (t : ℝ) :
    atStation (h.inputs 0) h.length t = h.inputs (h.length*t) := by
  funext i
  fin_cases i <;> rfl

theorem physical_recovery (h : PhysicalPiece) (pos : h.positive) (f : Field) (t : ℝ) :
    functionAt (h.inputs 0) h.length (quantity f) t = (h.field f).eval (h.length*t) := by
  unfold functionAt
  rw [input_shift]
  cases f with
  | displacement => exact local_transverse _ _ _ _ _ _ _ _ _ _ _ pos.1.ne' pos.2.1.ne' pos.2.2.ne'
  | slope => exact FrameIntervalRecoverySound.expression_fields _ _ _ _ _ _ _ _ _ _ _
      pos.1.ne' pos.2.1.ne' pos.2.2.ne' 3

theorem physical_derivative (h : PhysicalPiece) (pos : h.positive) (f : Field) (t : ℝ) :
    HasDerivAt (fun r : ℝ => (h.field f).eval (h.length*r))
      ((if f = .slope then h.length/h.flexural else h.length) *
        functionAt (h.inputs 0) h.length (derivativeSign f) t) t := by
  let x := h.length*t
  have chain := (RealBeamFields.real_derivative (h.field f) x).comp t ((hasDerivAt_id t).const_mul h.length)
  unfold functionAt
  rw [input_shift]
  cases f with
  | displacement =>
    have eq := FrameIntervalRecoverySound.expression_fields h.dofs h.length h.axial h.flexural h.p h.pEnd
      h.q h.qEnd x h.cosine h.sine pos.1.ne' pos.2.1.ne' pos.2.2.ne' 3
    change FrameIntervalExpressionSound.evaluate (h.inputs x) _ =
      (LocalFrameFields.rotation h.dofs h.length h.flexural h.q h.qEnd).eval x at eq
    simpa [Function.comp_def,id,PhysicalPiece.field,derivativeSign,x,eq,mul_comm,LocalFrameFields.rotation] using chain
  | slope =>
    have eq := FrameIntervalRecoverySound.expression_fields h.dofs h.length h.axial h.flexural h.p h.pEnd
      h.q h.qEnd x h.cosine h.sine pos.1.ne' pos.2.1.ne' pos.2.2.ne' 2
    change FrameIntervalExpressionSound.evaluate (h.inputs x) _ =
      (LocalFrameFields.moment h.dofs h.length h.flexural h.q h.qEnd).eval x at eq
    simp only [derivativeSign,if_true,eq,LocalFrameFields.moment,Polynomial.eval_mul,Polynomial.eval_C]
    convert chain using 1 <;> simp [Function.comp_def,id,PhysicalPiece.field,x] <;> field_simp [pos.2.2.ne'] <;> ring

theorem physical_extreme_covered {bits p f rows} (h : PhysicalPiece) (pos : h.positive)
    (fits : Fits p (h.inputs 0) h.length) (done : candidates bits p f = some rows)
    {t : ℝ} (domain : t ∈ Icc 0 1)
    (extreme : IsMaxOn (fun r => (h.field f).eval (h.length*r)) (Icc 0 1) t ∨
      IsMinOn (fun r => (h.field f).eval (h.length*r)) (Icc 0 1) t) :
    ∃ r ∈ rows, Contains r.t t ∧ Contains r.value ((h.field f).eval (h.length*t)) := by
  rw [← physical_recovery h pos]
  apply candidates_cover fits done domain
  by_cases left : t = 0
  · exact Or.inl left
  by_cases right : t = 1
  · exact Or.inr (Or.inl right)
  have near := Icc_mem_nhds (lt_of_le_of_ne domain.1 (Ne.symm left)) (lt_of_le_of_ne domain.2 right)
  have d := physical_derivative h pos f t
  have zero := extreme.elim (fun mx => (mx.isLocalMax near).hasDerivAt_eq_zero d)
    (fun mn => (mn.isLocalMin near).hasDerivAt_eq_zero d)
  have scale : (if f = .slope then h.length/h.flexural else h.length) ≠ 0 := by
    split
    · exact div_ne_zero pos.1.ne' pos.2.2.ne'
    · exact pos.1.ne'
  exact Or.inr (Or.inr ((mul_eq_zero.mp zero).resolve_left scale))

#print axioms physical_recovery
#print axioms physical_extreme_covered
end
end MemberKinematics.Sound
