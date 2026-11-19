import InclinedDiagramAssemblySound

namespace InclinedDiagram.Sound
open InclinedDiagram.Statics
open InclinedDiagram.Statics.Sound
open InclinedFrameSource InclinedFrameReal InclinedFrameBasis InclinedFrameIntervalAssembly
open FrameEnclosure (Contains)
noncomputable section

theorem singleton_form {n} (state : Fin n → ℝ) {r : Row} {i : Fin n} {v : Rat}
    (width : r.size = n) (pureForm : onlyCoefficient r i.val = some v) :
    value state r = (v:ℝ)*state i := by
  unfold onlyCoefficient at pureForm
  split at pureForm
  next check =>
    cases pureForm
    have eq := eq_of_beq check
    unfold value
    apply Finset.sum_eq_single i
    · intro j _ ne
      have ji : j.val ≠ i.val := fun h => ne (Fin.ext h)
      have hi : i.val < r.size := by simpa only [width] using i.isLt
      have hj : j.val < r.size := by simpa only [width] using j.isLt
      have atJ := congrArg (fun x : Row => x[j.val]!) eq
      have zero : r[j.val]! = 0 := by simpa [getElem!_pos,Array.set!,hi,hj,ji,Ne.symm ji] using atJ
      simp [zero]
    · simp
  next => cases pureForm

theorem start_projection (data : Partition) (h : PartitionValid data) (motion : Motion data)
    (i : Fin data.pieces.size) :
    let seg := data.pieces[i.val]!
    let member := data.source.members[seg.member]!
    let a := data.source.nodes[member.a]!
    let b := data.source.nodes[member.b]!
    ((a.y:ℝ)-b.y)*globalActions data motion i 0 + ((b.x:ℝ)-a.x)*globalActions data motion i 1 =
      (physicalState data motion i).L*(physicalState data motion i).V := by
  rcases h with ⟨src,_,_,_,_,_,_,pieces,_,_,_,_⟩
  let seg := data.pieces[i.val]!
  let owner : Fin data.source.members.size := ⟨seg.member,(pieces i).1.1⟩
  let orientation := memberDirection data seg.member
  let L := memberLength data seg.member
  have eq := ExactGeometry.direction_components _ _ (endpoints_distinct data src owner)
  have hx : L*orientation.cosine =
      (data.source.nodes[data.source.members[seg.member]!.b]!.x:ℝ)-
      data.source.nodes[data.source.members[seg.member]!.a]!.x := by
    simpa [L,orientation,owner,endpoints,memberLength,memberDirection,ExactGeometry.dx] using eq.1
  have hy : L*orientation.sine =
      (data.source.nodes[data.source.members[seg.member]!.b]!.y:ℝ)-
      data.source.nodes[data.source.members[seg.member]!.a]!.y := by
    simpa [L,orientation,owner,endpoints,memberLength,memberDirection,ExactGeometry.dy] using eq.2
  have unit : orientation.cosine^2+orientation.sine^2=1 := member_normalized data src owner
  let v := (physicalState data motion i).V
  dsimp only
  rw [←show -((data.source.nodes[data.source.members[seg.member]!.b]!.y:ℝ)-
    data.source.nodes[data.source.members[seg.member]!.a]!.y) = _ from neg_sub _ _,←hy,←hx]
  change -(L*orientation.sine)*(_-orientation.sine*v)+(L*orientation.cosine)*(_+orientation.cosine*v) = L*v
  linear_combination L*v*unit

structure Forms {n} (state : Fin n → ℝ) (p : InclinedDiagram.Piece) (s : State) : Prop where
  shear_width : p.scaledShear.size = n
  moment_width : p.initialMoment.size = n
  length_slot : ∃ i : Fin n, i.val = p.lengthColumn ∧ state i = s.L
  shear_value : value state p.scaledShear = s.L*s.V
  moment_value : value state p.initialMoment = s.M

theorem refined_forms {data : Partition} {basis : GlobalBasis} {cert : Certificate data basis}
    {motion : Motion data} {springs : Array (Fin basis.columns.size → Rat)} {torque : Fin springs.size → ℝ}
    (partition : PartitionValid data) (work : WorkColumns cert motion springs torque)
    (i : Fin data.pieces.size) (p : InclinedDiagram.Piece) (base : fits p (physicalState data motion i)) :
    let out := withStatics data (assemble cert springs) i p
    fits out (physicalState data motion i) ∧ Forms (frameState motion torque) out (physicalState data motion i) := by
  let sys := assemble cert springs
  let state := frameState motion torque
  let physical := physicalState data motion i
  let seg := data.pieces[i.val]!
  let member := data.source.members[seg.member]!
  let a := data.source.nodes[member.a]!
  let b := data.source.nodes[member.b]!
  let n := Statics.width data springs.size
  let k := 6*i.val
  have dimensions := system_dimensions n (seedTerms cert springs)
    (⟨6*data.pieces.size+springs.size,n,#[]⟩ : System)
  have size : sys.width = n := dimensions.1
  have pivots : sys.unknowns = 6*data.pieces.size+springs.size := dimensions.2
  have valid := all_rows_valid partition work
  let vterms : List (Nat × Rat) := [(k,a.y-b.y),(k+1,b.x-a.x)]
  let mterms : List (Nat × Rat) := [(k+2,-1)]
  let v := reduce sys (equation sys.width vterms)
  let m := reduce sys (equation sys.width mterms)
  have reduced (xs : List (Nat × Rat)) : (reduce sys (equation sys.width xs)).size = n ∧
      value state (reduce sys (equation sys.width xs)) = termsValue state xs := by
    rw [size]
    have represented := pivots_preserve state sys.pivots.toList valid (equation n xs) (by simp [equation])
    exact ⟨represented.1,represented.2.trans (equation_value state xs)⟩
  have at0 : atSlot state k = globalActions data motion i 0 := end_slot motion torque i 0
  have at1 : atSlot state (k+1) = globalActions data motion i 1 := end_slot motion torque i 1
  have at2 : atSlot state (k+2) = globalActions data motion i 2 := end_slot motion torque i 2
  have vValue : value state v = physical.L*physical.V := (reduced vterms).2.trans (by
    simpa [termsValue,vterms,at0,at1,physical,a,b,member,seg] using start_projection data partition motion i)
  have mValue : value state m = physical.M := (reduced mterms).2.trans (by
    simp [termsValue,mterms,at2,globalActions,FrameTransform.toGlobal6,physical,physicalState])
  have own : seg.member < data.source.members.size := by
    rcases partition with ⟨_,_,_,_,_,_,_,pieces,_,_,_,_⟩
    exact (pieces i).1.1
  let lengthIndex := sys.unknowns+seg.member
  have lenBound : lengthIndex < n := by dsimp [lengthIndex,n,Statics.width]; rw [pivots]; omega
  let li : Fin n := ⟨lengthIndex,lenBound⟩
  let one : Fin n := ⟨n-1,by dsimp [n,Statics.width]; omega⟩
  have lengthValue : state li = physical.L := by
    have actual := length_slot motion torque (⟨seg.member,own⟩ : Fin data.source.members.size)
    have extension : atSlot state lengthIndex = state li := by simp [atSlot,li,lenBound]
    rw [←extension]
    simpa [lengthIndex,pivots,physical,physicalState,seg,state] using actual
  have oneValue : state one = 1 := by
    have actual := constant_slot motion torque
    simpa [one,atSlot,n,Statics.width,state] using actual
  have vBound : Contains (((onlyCoefficient v lengthIndex).map singleton).getD p.shearStart) physical.V := by
    cases e : onlyCoefficient v lengthIndex with
    | none => exact base.2.1
    | some x =>
      have equal := singleton_form state (i := li) (reduced vterms).1 e
      rw [vValue,lengthValue] at equal
      have positive := base.2.2.2.1
      have eq : physical.V = (x:ℝ) := by nlinarith
      exact eq ▸ singleton_fits x
  have mBound : Contains (((onlyCoefficient m (sys.width-1)).map singleton).getD p.momentStart) physical.M := by
    rw [size]
    cases e : onlyCoefficient m (n-1) with
    | none => exact base.2.2.1
    | some x =>
      have equal := singleton_form state (i := one) (reduced mterms).1 e
      rw [mValue,oneValue,mul_one] at equal
      exact equal ▸ singleton_fits x
  exact ⟨⟨base.1,vBound,mBound,base.2.2.2⟩,
    ⟨(reduced vterms).1,(reduced mterms).1,⟨li,rfl,lengthValue⟩,vValue,mValue⟩⟩

theorem modify_value {n} (state : Fin n → ℝ) (row : Row) (index : Fin n) (k : Rat)
    (width : row.size = n) :
    value state (row.modify index.val (· + k)) = value state row + (k:ℝ)*state index := by
  have hi : index.val < row.size := by simpa only [width] using index.isLt
  have get (j : Fin n) : ((row.modify index.val (· + k))[j.val]! : Rat) =
      row[j.val]! + (if j = index then k else 0) := by
    have hj : j.val < row.size := by simpa only [width] using j.isLt
    by_cases eq : j = index
    · subst j; simp [Array.modify,getElem!_pos,hi]
    · have ne : j.val ≠ index.val := fun h => eq (Fin.ext h)
      simp [Array.modify,getElem!_pos,hj,hi,ne,Ne.symm ne,eq]
  unfold value
  simp_rw [get,Rat.cast_add,add_mul,Finset.sum_add_distrib]
  simp [apply_ite,ite_mul]

theorem signature_value {n} {state : Fin n → ℝ} {p s} (forms : Forms state p s)
    (m : Bool) (t : Rat) (nonempty : p.scaledShear.isEmpty = false) :
    value state (fieldSignature p m t) = if m then moment p s t else s.L*shear p s t := by
  obtain ⟨li,hli,hL⟩ := forms.length_slot
  cases m with
  | false =>
    simp only [fieldSignature,nonempty,Bool.false_eq_true,↓reduceIte,Id.run_pure,pure]
    rw [←hli,modify_value state _ li _ forms.shear_width,forms.shear_value,hL]
    simp [shear]; ring
  | true =>
    let k := (p.right-p.left)*t
    let linear := p.initialMoment.mapIdx fun i a => a + k*p.scaledShear[i]!
    have width : linear.size = n := by simp [linear,forms.moment_width]
    have linearValue : value state linear = value state p.initialMoment+(k:ℝ)*value state p.scaledShear := by
      unfold value
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have bounded : i.val < p.initialMoment.size := by simpa only [forms.moment_width] using i.isLt
      simp [linear,getElem!_pos,bounded]
      ring
    change value state (if p.scaledShear.isEmpty then #[] else
      linear.modify p.lengthColumn (· + k*t*(p.linear/2+t*p.quadratic/3))) = _
    simp only [nonempty,Bool.false_eq_true,↓reduceIte]
    rw [←hli,modify_value state _ li _ width,linearValue,forms.shear_value,forms.moment_value,hL]
    simp [moment,span,k]
    ring

#print axioms signature_value
#print axioms refined_forms
#print axioms start_projection
end
end InclinedDiagram.Sound
