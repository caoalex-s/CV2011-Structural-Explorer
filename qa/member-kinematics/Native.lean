import MemberKinematicsWire

def main (args : List String) : IO UInt32 := do
  let mut failed := false
  for name in args do
    let report := MemberKinematics.checkReport (← IO.FS.readFile name)
    if name.endsWith ".reject" then
      if report.isSome then throw (IO.userError s!"Accepted an inconsistent frame certificate in {name}")
      IO.println s!"Rejected inconsistent frame certificate in {name}"
    else
      let some result := report | do
        IO.eprintln s!"Rejected {name}"
        failed := true
        continue
      IO.FS.writeFile (name ++ ".report") result
      IO.println s!"Accepted {name}"
  return if failed then 1 else 0
