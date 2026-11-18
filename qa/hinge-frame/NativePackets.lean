import HingeFrameWire

def main (args : List String) : IO UInt32 := do
  let some directory := args.head? | throw (IO.userError "Expected synthetic packet directory")
  let entries ← (System.FilePath.mk directory).readDir
  let mut count := 0
  for entry in entries do
    if entry.path.extension == some "packet" then
      let some expected := (entry.fileName.take 1).toNat? | throw (IO.userError "Missing expected return code")
      let actual := (HingeFrame.Wire.checkString (← IO.FS.readFile entry.path)).toNat
      if actual != expected then throw (IO.userError s!"{entry.fileName}: expected {expected}, received {actual}")
      IO.println s!"PASS {entry.fileName}"
      count := count + 1
  if count < 5 then throw (IO.userError "Incomplete hinge fixture inventory")
  return 0
