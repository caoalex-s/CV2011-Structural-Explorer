import InclinedFrameIntervalWire

/-! Linux-only native exercise of the compact decoder and reconstructed checker.
    Run after the complete source/axiom checks. The workflow supplies a process
    deadline; elapsed time and exact returned intervals are retained as evidence. -/
open InclinedFrameIntervalWire

def showBounds (bounds : FrameIntervalOps.Bounds) : String :=
  s!"{bounds.lower.num}/{bounds.lower.den},{bounds.upper.num}/{bounds.upper.den}"

def main (arguments : List String) : IO UInt32 := do
  let directory := arguments.headD "../.data/inclined-frame-packets"
  let cases : List (String × Bool) := [
    ("irrational-cantilever", true), ("affine-zero-resultant", true),
    ("reversed-cantilever", true), ("shared-rigid-joint", true),
    ("roller-interior-left", true), ("roller-interior-right", true),
    ("invalid-root", false), ("noncontracting-inverse", false),
    ("wrong-header", false), ("trailing-field", false),
    ("invalid-precision", false), ("zero-denominator", false),
    ("too-many-lines", false), ("too-many-bytes", false)]
  let mut failed := false
  for (name, expected) in cases do
    let input ← IO.FS.readFile (System.FilePath.mk directory / (name ++ ".txt"))
    let started ← IO.monoMsNow
    let result := decodeAndCheck input
    let accepted := result.isSome
    let elapsed := (← IO.monoMsNow) - started
    IO.println s!"case={name} accepted={accepted} expected={expected} elapsed_ms={elapsed}"
    if accepted != expected then failed := true
    match result with
    | none => pure ()
    | some checked =>
      for component in List.finRange 6 do
        IO.println s!"field={component.val} interval={showBounds (checked.outputs.fields component)}"
      for point in List.finRange checked.data.points.size do
        for direction in List.finRange 3 do
          IO.println s!"point={point.val} direction={direction.val} interval={showBounds (checked.outputs.reactions point direction)}"
  return if failed then 1 else 0
