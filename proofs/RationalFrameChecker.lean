import RationalFrameModel

/-! Executable generic witness checking. An accepted record concerns the
    source-derived model, never matrices or support masks supplied by a caller. -/
namespace RationalFrame

structure Certificate where
  /-- false is a stable solution, true is a proposed mechanism. -/
  mechanism : Bool
  motion : Array Rat
  reactions : Array Rat
  lower : Array (Array Rat)
  diagonal : Array Rat
  readouts : Array Rat
  loadWork : Rat
  deriving Inhabited, Repr

def arrayDot (a b : Array Rat) : Rat :=
  ((List.range a.size).map (fun i => a[i]! * b[i]!)).foldr (· + ·) 0

def residual (matrix : Array (Array Rat)) (force motion : Array Rat) : Array Rat :=
  matrix.mapIdx fun i row => arrayDot row motion - force[i]!

/-- The finite decidable proposition is both the executable factor check and
    the theorem's arithmetic premise. There is no second specification checker. -/
def FactorValid (matrix : Array (Array Rat)) (free : Array Nat) (certificate : Certificate) : Prop :=
  certificate.lower.size = free.size ∧ certificate.diagonal.size = free.size ∧
  (∀ i : Fin free.size, certificate.lower[i.val]!.size = free.size) ∧
  (∀ i : Fin free.size, 0 < certificate.diagonal[i.val]! ∧ certificate.lower[i.val]![i.val]! = 1) ∧
  (∀ i j : Fin free.size, i.val < j.val → certificate.lower[i.val]![j.val]! = 0) ∧
  (∀ i j : Fin free.size,
    sumFin free.size (fun k => certificate.lower[i.val]![k.val]! *
      certificate.diagonal[k.val]! * certificate.lower[j.val]![k.val]!) = matrix[free[i.val]!]![free[j.val]!]!)

instance (matrix : Array (Array Rat)) (free : Array Nat) (certificate : Certificate) :
    Decidable (FactorValid matrix free certificate) := by unfold FactorValid; infer_instance

def factorValid (matrix : Array (Array Rat)) (free : Array Nat) (certificate : Certificate) : Bool :=
  decide (FactorValid matrix free certificate)

def Admissible (model : Compiled) (motion : Array Rat) : Prop :=
  motion.size = model.dofs ∧ ∀ i : Fin model.dofs, blocked model i.val = true → motion[i.val]! = 0

def SolutionValid (model : Compiled) (query : Query) (certificate : Certificate) : Prop :=
  let matrix := stiffnessMatrix model
  let force := forceVector model
  FactorValid matrix (freeIndices model) certificate ∧
  certificate.reactions = residual matrix force certificate.motion ∧
  certificate.readouts = recover model query certificate.motion ∧ certificate.loadWork = 0 ∧
  (∀ i : Fin model.dofs, blocked model i.val = false → certificate.reactions[i.val]! = 0)

def MechanismValid (model : Compiled) (certificate : Certificate) : Prop :=
  let matrix := stiffnessMatrix model
  let force := forceVector model
  (¬ ∀ i : Fin model.dofs, certificate.motion[i.val]! = 0) ∧
  (∀ i : Fin model.dofs, arrayDot matrix[i.val]! certificate.motion = 0) ∧
  certificate.loadWork = arrayDot force certificate.motion ∧
  certificate.reactions = #[] ∧ certificate.lower = #[] ∧ certificate.diagonal = #[] ∧ certificate.readouts = #[]

instance (model : Compiled) (motion : Array Rat) : Decidable (Admissible model motion) :=
  by unfold Admissible; infer_instance
instance (model : Compiled) (query : Query) (certificate : Certificate) : Decidable (SolutionValid model query certificate) :=
  by unfold SolutionValid; infer_instance
instance (model : Compiled) (certificate : Certificate) : Decidable (MechanismValid model certificate) :=
  by unfold MechanismValid; infer_instance

/-- Finite source/certificate validation, with no floating acceptance flags. -/
def acceptsCompiled (model : Compiled) (query : Query) (certificate : Certificate) : Bool :=
  queryValid model query && decide (Admissible model certificate.motion) &&
    if certificate.mechanism then decide (MechanismValid model certificate)
    else decide (SolutionValid model query certificate)

def accepts (source : Source) (query : Query) (certificate : Certificate) : Bool :=
  match compileModel source with
  | none => false
  | some model => acceptsCompiled model query certificate

/-- The public source-level entry cannot bypass source compilation. This is
    an executable-boundary lemma, not yet the actual structural-model theorem. -/
theorem acceptance_source (source : Source) (query : Query) (certificate : Certificate)
    (h : accepts source query certificate = true) :
    ∃ model, compileModel source = some model ∧ queryValid model query = true ∧
      Admissible model certificate.motion ∧
      (if certificate.mechanism then MechanismValid model certificate else SolutionValid model query certificate) := by
  unfold accepts at h
  cases hc : compileModel source with
  | none => simp [hc] at h
  | some model =>
    refine ⟨model, rfl, ?_⟩
    cases hm : certificate.mechanism <;>
      simpa [hc, acceptsCompiled, hm, Bool.and_eq_true, and_assoc] using h

end RationalFrame
