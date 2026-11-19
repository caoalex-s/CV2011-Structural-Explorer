import MemberDiagram

def main (args : List String) : IO UInt32 := do
  for name in args do
    let report := MemberDiagram.checkReport (← IO.FS.readFile name)
    if name.endsWith ".reject" then
      if report.isSome then throw (IO.userError s!"Accepted an invalid inverse in {name}")
      IO.println s!"Rejected invalid inverse in {name}"
    else
      let some result := report | throw (IO.userError s!"Rejected {name}")
      IO.FS.writeFile (name ++ ".report") result
      IO.println s!"Accepted {name}"
  return 0
