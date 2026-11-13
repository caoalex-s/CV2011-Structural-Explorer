import RationalFrameWire

/-- Run only on Linux CI. This tests the decoded executable predicate; it is
    separate from the soundness theorem and from actual WASM/browser testing. -/
def main (args : List String) : IO UInt32 := do
  -- Test the finite partition postcondition independently of the compiler.
  -- A malformed segment that straddles either endpoint must be rejected even
  -- when its whole-coverage intensity sum would silently omit the load.
  let load : RationalFrame.Load := { default with member := 0, kind := 2, t := 1/4, ending := 3/4, fy := -5, qEnd := 5 }
  let source : RationalFrame.Source := { default with loads := #[load] }
  for (left, right, expected) in ([(0, 1, false), (0, 1/2, false), (1/2, 1, false),
      (0, 1/4, true), (1/4, 3/4, true), (3/4, 1, true)] : List (Rat × Rat × Bool)) do
    let segment : RationalFrame.Segment := { default with member := 0, left := left, right := right }
    if decide (RationalFrame.LoadPartitioned source segment) != expected then
      throw (IO.userError "Affine source-boundary exclusion failed")
  IO.println "PASS affine partition straddling/endpoint postconditions"
  let some folder := args.head? | throw (IO.userError "Expected packet folder")
  let entries ← (System.FilePath.mk folder).readDir
  let mut count := 0
  for entry in entries do
    if entry.path.extension == some "packet" then
      let some expected := (entry.fileName.take 1).toNat? | throw (IO.userError "Missing expected code")
      let input ← IO.FS.readFile entry.path
      let actual := (RationalFrame.Wire.checkString input).toNat
      if actual != expected then
        throw (IO.userError s!"{entry.fileName}: expected {expected}, got {actual}")
      IO.println s!"PASS {entry.fileName}"
      count := count + 1
  if count == 0 then throw (IO.userError "No packets found")
  IO.println s!"{count} native decoded-packet checks passed"
  return 0
