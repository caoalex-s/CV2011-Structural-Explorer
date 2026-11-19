import MemberDiagram
import HingeFrameWire
import CardinalSpring

namespace JointMemberDiagram
open RationalFrame MemberDiagram

/-- At the same geometric node, the two members can have different rotations.
Select the two face rotations of each piece before recovering its fields. -/
def rotations (assembly : HingeFrame.Assembly) (motion : Array Rat) (piece : Segment) :=
  HingeFrame.segmentMotion assembly piece motion

/-- A sheet describes a single drawn member. Its endpoint rotations may
therefore be copied into the two endpoint slots without changing any of its
interior motions. Check both recovered actions independently on every piece. -/
def memberMotion (a : HingeFrame.Assembly) (m : Nat) (u : Array Rat) :=
  let first := locationIndex a.mesh m 0
  let last := locationIndex a.mesh m 1
  (u.set! (3*first+2) u[HingeFrame.pointIndex a m 0 2]!).set!
    (3*last+2) u[HingeFrame.pointIndex a m 1 2]!

def SameActions (a : HingeFrame.Assembly) (m : Nat) (u : Array Rat) : Prop :=
  ∀ i : Index a.mesh m, let s := segmentAt a.mesh m i
    endAction s (memberMotion a m u) 1 = endAction s (rotations a u s) 1 ∧
    endAction s (memberMotion a m u) 2 = endAction s (rotations a u s) 2

instance (a : HingeFrame.Assembly) (m : Nat) (u : Array Rat) : Decidable (SameActions a m u) := by
  unfold SameActions; infer_instance

def evalRat (f : Cubic) (x : Rat) := f.f0 + x*(f.f1+x*(f.f2+x*f.f3))

/-- Bind the first and last polynomial ordinates to the signed one-sided
section moments used in the original connection balance. -/
def EndValues (a : HingeFrame.Assembly) (m : Nat) (u : Array Rat) : Prop :=
  ∀ i : Index a.mesh m, let s := segmentAt a.mesh m i
    let f := polynomial s (memberMotion a m u) true
    (s.left = 0 → evalRat f 0 = (HingeFrame.sectionValues a (HingeFrame.faceQuery (2*m)) u)[2]!) ∧
    (s.right = 1 → evalRat f s.length = (HingeFrame.sectionValues a (HingeFrame.faceQuery (2*m+1)) u)[2]!)

instance (a : HingeFrame.Assembly) (m : Nat) (u : Array Rat) : Decidable (EndValues a m u) := by
  unfold EndValues; infer_instance

def render (a : HingeFrame.Assembly) (m : Nat) (u : Array Rat) : Option String := do
  if SameActions a m u ∧ EndValues a m u then
    let sheet ← buildSheet a.mesh m (memberMotion a m u)
    if ranked (allRows sheet false) && ranked (allRows sheet true) && (encode sheet).utf8ByteSize ≤ 262144 then
      some (encode sheet)
    else none
  else none

def hingeReport (input : String) : Option String := do
  let p ← HingeFrame.Wire.decode input
  let a ← HingeFrame.compile p.source p.rules
  if !p.certificate.mechanism && HingeFrame.Wire.checkValue p then
    render a p.query.member p.certificate.motion
  else none

def springReport (input : String) : Option String := do
  let p ← FrameSpring.Wire.decode input
  let s ← CardinalSpring.compile p
  let _ ← FrameSpring.Wire.report p
  let k := CardinalSpring.matrix s
  let w ← CardinalSpring.solve s k
  if CardinalSpring.Equilibrium s k w then
    render s.beam p.query.member w.motion
  else none

@[export joint_diagram_report]
def checkReport (input : String) :=
  if input.startsWith "CV2011_HINGE_1\n" then hingeReport input
  else springReport input

end JointMemberDiagram
