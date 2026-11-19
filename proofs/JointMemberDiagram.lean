import MemberDiagram
import HingeFrameWire
import CardinalSpring

namespace JointMemberDiagram
open RationalFrame MemberDiagram

/-- At the same geometric node, the two members can have different rotations.
Select the two face rotations of each piece before recovering its fields. -/
def rotations (assembly : HingeFrame.Assembly) (motion : Array Rat) (piece : Segment) :=
  HingeFrame.segmentMotion assembly piece motion

def hingeReport (input : String) : Option String := do
  let p ← HingeFrame.Wire.decode input
  let a ← HingeFrame.compile p.source p.rules
  if !p.certificate.mechanism && HingeFrame.Wire.checkValue p then
    let sheet ← buildSheet a.mesh p.query.member (rotations a p.certificate.motion)
    if ranked (allRows sheet false) && ranked (allRows sheet true) && (encode sheet).utf8ByteSize ≤ 262144 then
      some (encode sheet)
    else none
  else none

def springReport (input : String) : Option String := do
  let p ← FrameSpring.Wire.decode input
  let s ← CardinalSpring.compile p
  let _ ← FrameSpring.Wire.report p
  let k := CardinalSpring.matrix s
  let w ← CardinalSpring.solve s k
  if CardinalSpring.Equilibrium s k w then
    let sheet ← buildSheet s.beam.mesh p.query.member (rotations s.beam w.motion)
    if ranked (allRows sheet false) && ranked (allRows sheet true) && (encode sheet).utf8ByteSize ≤ 262144 then
      some (encode sheet)
    else none
  else none

@[export joint_diagram_report]
def checkReport (input : String) :=
  if input.startsWith "CV2011_HINGE_1\n" then hingeReport input
  else springReport input

end JointMemberDiagram
