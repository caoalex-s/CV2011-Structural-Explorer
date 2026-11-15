import InclinedFrameIntervalReport

/-! Exercise the exact report API independently of the native interval log.
    Linux CI supplies the process deadline. Output files are consumed by the
    browser-side representation parser and compared with the native intervals. -/
def main (arguments : List String) : IO UInt32 := do
  let directory := System.FilePath.mk (arguments.headD "../.data/inclined-frame-packets")
  let cases : List (String × Bool) := [
    ("irrational-cantilever", true), ("affine-zero-resultant", true),
    ("reversed-cantilever", true), ("shared-rigid-joint", true),
    ("cantilever-interior", true), ("reversed-interior", true),
    ("roller-interior-left", true), ("roller-interior-right", true),
    ("invalid-root", false), ("noncontracting-inverse", false),
    ("wrong-header", false), ("trailing-field", false),
    ("invalid-precision", false), ("zero-denominator", false),
    ("too-many-lines", false), ("too-many-bytes", false)]
  let mut failed := false
  for (name, expected) in cases do
    let input ← IO.FS.readFile (directory / (name ++ ".txt"))
    let started ← IO.monoMsNow
    let result := InclinedFrameIntervalReport.checkReport input
    let elapsed := (← IO.monoMsNow) - started
    IO.println s!"report={name} accepted={result.isSome} expected={expected} elapsed_ms={elapsed}"
    if result.isSome != expected then failed := true
    match result with
    | none => pure ()
    | some report => IO.FS.writeFile (directory / (name ++ ".report")) report
  return if failed then 1 else 0
