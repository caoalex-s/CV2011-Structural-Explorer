import RationalFrameWire

/-- Native Linux timing only. Same 128-digit wire decoder and source-level
    checker; candidate intermediates were measured in isolated copied modules. -/
def main (args : List String) : IO UInt32 := do
  let some folder := args.head? | throw (IO.userError "Expected measurement folder")
  let entries ← (System.FilePath.mk folder).readDir
  for entry in entries do
    if entry.path.extension == some "packet" then
      let input ← IO.FS.readFile entry.path
      let started ← IO.monoMsNow
      let result := RationalFrame.Wire.checkString input
      if result != 1 then throw (IO.userError s!"{entry.fileName}: code {result}")
      let finished ← IO.monoMsNow
      IO.println s!"{entry.fileName}: accepted; native checker {finished-started} ms; {input.utf8ByteSize} bytes"
  return 0
