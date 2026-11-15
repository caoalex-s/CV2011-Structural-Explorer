import FrameIntervalVector

/-! Executable inverse-residual certificate checks. Matrix and load enclosures
    must come from the source assembly checker. The proposed inverse and estimate
    are merely rational data; every defect and residual entry is recomputed. -/
namespace FrameIntervalSolve
open FrameIntervalOps FrameIntervalVector

def singletonBounds (value : Rat) : Bounds := ⟨value, value⟩

structure Certificate (size : Nat) where
  inverse : Fin size → Fin size → Rat
  estimate : Fin size → Rat
  defect : Fin size → Fin size → Bounds
  residual : Fin size → Bounds
  transformedResidual : Fin size → Bounds
  contraction : Rat
  residualBound : Rat
  solution : Fin size → Bounds

def defectEntry {size : Nat} (bits : Nat) (matrix : Fin size → Fin size → Bounds)
    (inverse : Fin size → Fin size → Rat) (row column : Fin size) : Option Bounds := do
  let product ← dot bits (fun index => singletonBounds (inverse row index)) (fun index => matrix index column)
  subtract bits (singletonBounds (if row = column then 1 else 0)) product

def residualEntry {size : Nat} (bits : Nat) (matrix : Fin size → Fin size → Bounds)
    (force : Fin size → Bounds) (estimate : Fin size → Rat) (row : Fin size) : Option Bounds := do
  let product ← dot bits (matrix row) (fun index => singletonBounds (estimate index))
  subtract bits (force row) product

def transformedEntry {size : Nat} (bits : Nat) (inverse : Fin size → Fin size → Rat)
    (residual : Fin size → Bounds) (row : Fin size) : Option Bounds :=
  dot bits (fun index => singletonBounds (inverse row index)) residual

def ScalarChecks {size : Nat} (bits : Nat) (certificate : Certificate size) : Prop :=
  precisionValid bits = true ∧ size ≤ 48 ∧
  0 ≤ certificate.contraction ∧ certificate.contraction < 1 ∧ 0 ≤ certificate.residualBound ∧
  bounded certificate.contraction = true ∧ bounded certificate.residualBound = true

def InputChecks {size : Nat} (matrix : Fin size → Fin size → Bounds)
    (force : Fin size → Bounds) (certificate : Certificate size) : Prop :=
  (∀ row column, valid (matrix row column) = true ∧ bounded (certificate.inverse row column) = true) ∧
  (∀ row, valid (force row) = true ∧ bounded (certificate.estimate row) = true)

def ArithmeticChecks {size : Nat} (bits : Nat) (matrix : Fin size → Fin size → Bounds)
    (force : Fin size → Bounds) (certificate : Certificate size) : Prop :=
  (∀ row column, defectEntry bits matrix certificate.inverse row column = some (certificate.defect row column)) ∧
  (∀ row, residualEntry bits matrix force certificate.estimate row = some (certificate.residual row)) ∧
  (∀ row, transformedEntry bits certificate.inverse certificate.residual row =
    some (certificate.transformedResidual row))

def NormChecks {size : Nat} (certificate : Certificate size) : Prop :=
  (∀ row, magnitudeSum (certificate.defect row) ≤ certificate.contraction) ∧
  (∀ row, magnitude (certificate.transformedResidual row) ≤ certificate.residualBound)

def OutputChecks {size : Nat} (certificate : Certificate size) : Prop :=
  ∀ row, valid (certificate.solution row) = true ∧
    (certificate.solution row).lower ≤
      certificate.estimate row - certificate.residualBound/(1-certificate.contraction) ∧
    certificate.estimate row + certificate.residualBound/(1-certificate.contraction) ≤
      (certificate.solution row).upper

def Checks {size : Nat} (bits : Nat) (matrix : Fin size → Fin size → Bounds)
    (force : Fin size → Bounds) (certificate : Certificate size) : Prop :=
  ScalarChecks bits certificate ∧ InputChecks matrix force certificate ∧
  ArithmeticChecks bits matrix force certificate ∧ NormChecks certificate ∧ OutputChecks certificate

instance {size : Nat} (bits : Nat) (matrix : Fin size → Fin size → Bounds)
    (force : Fin size → Bounds) (certificate : Certificate size) :
    Decidable (Checks bits matrix force certificate) := by
  unfold Checks ScalarChecks InputChecks ArithmeticChecks NormChecks OutputChecks
  infer_instance

/-- Failure is inconclusive. This predicate never asserts a mechanism. -/
def check {size : Nat} (bits : Nat) (matrix : Fin size → Fin size → Bounds)
    (force : Fin size → Bounds) (certificate : Certificate size) : Bool :=
  decide (Checks bits matrix force certificate)

end FrameIntervalSolve
