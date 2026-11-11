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

/-- Triangular/unit diagonal, strictly positive pivots and every factor entry
    are checked against the reduced source-derived stiffness. -/
def factorValid (matrix : Array (Array Rat)) (free : Array Nat) (certificate : Certificate) : Bool := Id.run do
  let n := free.size
  if certificate.lower.size != n || certificate.diagonal.size != n then return false
  if !(certificate.lower.all (fun row => row.size == n)) then return false
  for i in [:n] do
    if certificate.diagonal[i]! ≤ 0 || certificate.lower[i]![i]! != 1 then return false
    for j in [:n] do
      if i < j && certificate.lower[i]![j]! != 0 then return false
      let product := ((List.range n).map fun k =>
        certificate.lower[i]![k]! * certificate.diagonal[k]! * certificate.lower[j]![k]!).foldr (· + ·) 0
      if product != matrix[free[i]!]![free[j]!]! then return false
  return true

/-- Finite source/certificate validation, with no floating acceptance flags. -/
def acceptsCompiled (model : Compiled) (query : Query) (certificate : Certificate) : Bool := Id.run do
  if !queryValid model query || certificate.motion.size != model.dofs then return false
  let matrix := stiffnessMatrix model
  let force := forceVector model
  for i in [:model.dofs] do
    if blocked model i && certificate.motion[i]! != 0 then return false
  if certificate.mechanism then
    if !certificate.motion.any (fun value => value != 0) then return false
    if !(matrix.all fun row => arrayDot row certificate.motion == 0) then return false
    return certificate.loadWork == arrayDot force certificate.motion &&
      certificate.reactions.isEmpty && certificate.lower.isEmpty &&
      certificate.diagonal.isEmpty && certificate.readouts.isEmpty
  else
    if !factorValid matrix (freeIndices model) certificate then return false
    let imbalance := residual matrix force certificate.motion
    if certificate.reactions != imbalance || certificate.readouts != recover model query certificate.motion then return false
    if certificate.loadWork != 0 then return false
    for i in [:model.dofs] do
      if !blocked model i && imbalance[i]! != 0 then return false
    return true

def accepts (source : Source) (query : Query) (certificate : Certificate) : Bool :=
  match compileModel source with
  | none => false
  | some model => acceptsCompiled model query certificate

end RationalFrame
