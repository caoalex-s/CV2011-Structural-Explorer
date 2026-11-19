import InclinedReleaseWire

def main (args : List String) : IO UInt32 := do
  for name in args do
    let some result := InclinedRelease.Wire.checkReport (← IO.FS.readFile name)
      | throw (IO.userError s!"Rejected {name}")
    IO.FS.writeFile (name ++ ".report") result
    IO.println s!"Accepted {name}"
  return 0
