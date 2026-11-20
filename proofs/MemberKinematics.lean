import InclinedDiagramWire

/-! Certified recovery uses the member's drawn local axes. The coordinate t
runs from 0 to 1 on each source piece, and x is physical distance from its
left endpoint. Both faces of a cut retain their own source motion. -/
namespace MemberKinematics
open FrameIntervalOps InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly
open FrameIntervalExpression

/-- The two derivatives are respectively θ and EI⁻¹ M. The strictly positive
flexural rigidity lets the slope search use the sign of M directly. -/
inductive Field where | displacement | slope
  deriving Inhabited, DecidableEq

def transverse : Expression 15 :=
  let x := Expression.input 10
  let moment := -(Expression.input 2 : Expression 15)
  let shear := Expression.input 1
  let q := Expression.input 8
  let dq := Expression.input 9
  let stiffness := Expression.input 12
  let v := Expression.input 4
  let θ := Expression.input 5
  v + x*(θ + x*(moment/2 + x*(shear/6 + x*(q/24 + x*dq/120)))/stiffness)

def quantity : Field → Expression 15
  | .displacement => transverse
  | .slope => FrameIntervalRecovery.expressions 3

def derivativeSign : Field → Expression 15
  | .displacement => FrameIntervalRecovery.expressions 3
  | .slope => FrameIntervalRecovery.expressions 2

structure Segment where
  left : Rat
  right : Rat
  length : Bounds
  inputs : Fin 15 → Bounds
  deriving Inhabited

def recover {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (cert : Certificate data basis) (i : Fin data.pieces.size) : Option Segment := do
  let source := data.pieces[i.val]!
  let inputs ← InclinedFrameIntervalRecovery.fieldInputs bits cert i source.left
  return ⟨source.left, source.right, (cert.geometry i).length, inputs⟩

def evaluate (bits : Nat) (p : Segment) (expr : Expression 15) (t : Bounds) : Option Bounds := do
  let x ← multiply bits p.length t
  enclose bits (fun i => if i.val = 10 then x else p.inputs i) expr

/-- Expand the derivative about the cell midpoint. A near-double root can
otherwise keep many cells alive because powers of x share the same x. Inputs
10 and 15 are the physical midpoint and the signed offset from that point. -/
def centered : Field → Expression 16 := fun f =>
  let x := Expression.input 10
  let d := Expression.input 15
  let m := -(Expression.input 2 : Expression 16)
  let v := Expression.input 1
  let q := Expression.input 8
  let dq := Expression.input 9
  let ei := Expression.input 12
  let θ := Expression.input 5
  let intensity := q + x*dq
  let shear := v + x*(q+x*dq/2)
  let moment := m + x*(v+x*(q/2+x*dq/6))
  match f with
  | .slope => moment + d*(shear+d*(intensity/2+d*dq/6))
  | .displacement =>
    let rotation := θ + x*(m+x*(v/2+x*(q/6+x*dq/24)))/ei
    rotation + d*(moment+d*(shear/2+d*(intensity/6+d*dq/24)))/ei

def centeredInputs {α : Type} (original : Fin 15 → α) (middle offset : α) (i : Fin 16) : α :=
  if i.val = 10 then middle else if h : i.val < 15 then original ⟨i.val,h⟩ else offset

def derivativeBounds (bits : Nat) (p : Segment) (f : Field) (t : Bounds) : Option Bounds := do
  let mid := (t.lower+t.upper)/2
  let x ← multiply bits p.length ⟨mid,mid⟩
  let dx ← multiply bits p.length ⟨t.lower-mid,t.upper-mid⟩
  enclose bits (centeredInputs p.inputs x dx) (centered f)

structure Candidate where
  t : Bounds
  value : Bounds
  deriving Inhabited

def candidate (bits : Nat) (p : Segment) (field : Field) (t : Bounds) : Option Candidate := do
  return ⟨t, ← evaluate bits p (quantity field) t⟩

inductive Cell where
  | excluded
  | enclosing (row : Candidate)
  | subdivide

/-- Discard cells only after excluding zero from the derivative. A cell
with a small field range may be retained in full for near-flat data. -/
def classify (bits : Nat) (p : Segment) (field : Field) (t : Bounds) : Option Cell := do
  let derivative ← derivativeBounds bits p field t
  if derivative.upper < 0 || 0 < derivative.lower then return .excluded
  let nearlyFlat := derivative.upper-derivative.lower ≤ (1:Rat)/1000000000000000
  if nearlyFlat || (t.upper-t.lower)*p.length.upper ≤ (1:Rat)/1000000 then
    let row ← candidate bits p field t
    if row.value.upper-row.value.lower ≤ (1:Rat)/100000000 then return .enclosing row
  return .subdivide

/-- The two closed children share the midpoint, so a stationary point at the
split is retained. Each visited cell consumes one unit of the shared budget. -/
def stationary (bits : Nat) (p : Segment) (field : Field) (t : Bounds) :
    Nat → Nat → Option (List Candidate × Nat)
  | 0, _ => none
  | _+1, 0 => none
  | fuel+1, budget+1 => do
    match ← classify bits p field t with
    | .excluded => return ([], budget)
    | .enclosing row => return ([row], budget)
    | .subdivide =>
      let mid := (t.lower+t.upper)/2
      let (left, remaining) ← stationary bits p field ⟨t.lower, mid⟩ fuel budget
      let (right, remaining) ← stationary bits p field ⟨mid, t.upper⟩ fuel remaining
      return (left ++ right, remaining)

def candidates (bits : Nat) (p : Segment) (field : Field) : Option (List Candidate) := do
  let first ← candidate bits p field ⟨0,0⟩
  let last ← candidate bits p field ⟨1,1⟩
  let (inside, _) ← stationary bits p field ⟨0,1⟩ 35 4096
  return first :: last :: inside

end MemberKinematics
