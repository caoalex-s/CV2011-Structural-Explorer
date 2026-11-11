import RationalFrameWire

/-- Run only on Linux CI. This tests the decoded executable predicate; it is
    separate from the soundness theorem and from actual WASM/browser testing. -/
def main (args : List String) : IO UInt32 := do
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
