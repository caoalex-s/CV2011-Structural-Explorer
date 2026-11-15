import FrameIntervalOps

/-! Fixed output policy in kN, kN m, radians and metres. Quantities 0..5 are
    N,V,M,rotation,ux,uy; 6..8 are grouped Rx,Ry,Mz. Every displayed field and
    reaction must pass its gate after containment has been established. -/
namespace FrameIntervalAccuracy
open FrameIntervalOps

def relativeTolerance : Rat := 1 / 100000000

def absoluteTolerance (quantity : Fin 9) : Rat :=
  if quantity = 3 then 1 / 10000000000
  else if quantity = 4 ∨ quantity = 5 then 1 / 1000000000
  else 1 / 1000000

def midpoint (bounds : Bounds) : Rat := (bounds.lower+bounds.upper)/2
def radius (bounds : Bounds) : Rat := (bounds.upper-bounds.lower)/2

def check (quantity : Fin 9) (bounds : Bounds) : Bool :=
  decide (valid bounds = true ∧ radius bounds ≤ absoluteTolerance quantity + relativeTolerance *
    upperOf 0 (upperOf (-midpoint bounds) (midpoint bounds) - radius bounds))

end FrameIntervalAccuracy
