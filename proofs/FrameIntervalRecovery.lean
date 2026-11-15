import FrameIntervalExpression

/-! Fixed source-authored recovery expressions. Input order is left endpoint
    actions (0..2), left local motion (3..5), p, dp, q, dq, x, EA, EI, cosine,
    sine. Load slopes are per physical length. Output order is N,V,M,θ,ux,uy. -/
namespace FrameIntervalRecovery
open FrameIntervalExpression

def expressions : Fin 6 → Expression 15 :=
  let actionX := Expression.input 0
  let actionY := Expression.input 1
  let actionMoment := Expression.input 2
  let axialStart := Expression.input 3
  let transverseStart := Expression.input 4
  let rotationStart := Expression.input 5
  let p := Expression.input 6
  let dp := Expression.input 7
  let q := Expression.input 8
  let dq := Expression.input 9
  let x := Expression.input 10
  let EA := Expression.input 11
  let EI := Expression.input 12
  let cosine := Expression.input 13
  let sine := Expression.input 14
  let x2 := x*x
  let x3 := x2*x
  let x4 := x2*x2
  let x5 := x4*x
  let normal := -actionX - p*x - dp*x2/2
  let shear := actionY + q*x + dq*x2/2
  let moment := -actionMoment + actionY*x + q*x2/2 + dq*x3/6
  let rotation := rotationStart + (-actionMoment*x + actionY*x2/2 + q*x3/6 + dq*x4/24)/EI
  let axial := axialStart + (-actionX*x - p*x2/2 - dp*x3/6)/EA
  let transverse := transverseStart + rotationStart*x +
    (-actionMoment*x2/2 + actionY*x3/6 + q*x4/24 + dq*x5/120)/EI
  ![normal, shear, moment, rotation, cosine*axial-sine*transverse, sine*axial+cosine*transverse]

def field (bits : Nat) (inputs : Fin 15 → FrameIntervalOps.Bounds) (component : Fin 6) :
    Option FrameIntervalOps.Bounds := enclose bits inputs (expressions component)

end FrameIntervalRecovery
