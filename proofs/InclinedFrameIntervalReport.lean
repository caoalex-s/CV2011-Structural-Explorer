import InclinedFrameIntervalWire

/-! Exact result serialization. There is no floating conversion at this boundary.
    Only the successful compact packet check can produce a report. Native ABI
    exports and browser integration are deliberately outside this module. -/
namespace InclinedFrameIntervalReport
open InclinedFrameIntervalWire

def rationalFields (value : Rat) : List String := [toString value.num, toString value.den]

/-- Endpoints and the exact midpoint share the same accepted interval. -/
def intervalFields (bounds : FrameIntervalOps.Bounds) : List String :=
  rationalFields bounds.lower ++ rationalFields bounds.upper ++
    rationalFields (FrameIntervalAccuracy.midpoint bounds)

def pointFields (result : Result) (index : Fin result.data.points.size) : List String :=
  let point := result.data.points[index.val]!
  let owner := if point.owner.isSome then "1" else "0"
  let identity := match point.owner with
    | none => result.data.source.nodes[point.index]!.id
    | some member => result.data.source.members[member]!.id
  [owner, toString point.index, identity] ++ rationalFields point.t ++
    (List.finRange 3).flatMap (fun direction => intervalFields (result.outputs.reactions index direction))

/-- Point indices and UTF-16 hexadecimal identifiers are read from the checked
    source partition, never from an independent presentation-side point map. -/
def encode (value : Packet) (result : Result) : String :=
  let header := ["CV2011_INCLINED_RESULT_1", result.data.source.members[value.query.member]!.id] ++
    rationalFields value.query.t ++ [if value.query.right then "1" else "0",
      toString value.query.convention, toString result.data.points.size]
  let fields := (List.finRange 6).flatMap (fun component => intervalFields (result.outputs.fields component))
  let points := (List.finRange result.data.points.size).flatMap (pointFields result)
  String.intercalate "\n" (header ++ fields ++ points)

/-- A result over the output byte budget is inconclusive, just like any other
    failed check. The ABI must also cap its destination buffer before copying. -/
def checkReport (input : String) : Option String := do
  let value ← decode input
  let result ← checkPacket value
  let report := encode value result
  if report.utf8ByteSize ≤ 262144 then some report else none

end InclinedFrameIntervalReport
