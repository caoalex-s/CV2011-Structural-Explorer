import MemberKinematics

namespace MemberKinematics
open InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly
open FrameIntervalOps
open InclinedDiagram (boxText)

/-- Store each row with its original piece and physical station. Cells from
opposite sides of a joint are never identified by a shared node number. -/
structure Located where
  piece : Nat
  station : Bounds
  value : Bounds

def locate (bits : Nat) (p : Segment) (piece : Nat) (whole : Bounds)
    (row : Candidate) : Option Located := do
  let fraction := InclinedDiagram.shift p.left (InclinedDiagram.scale (p.right-p.left) row.t)
  return ⟨piece, ← multiply bits whole fraction, row.value⟩

structure Extremes where
  minimum : Bounds
  maximum : Bounds

/-- The explicit checks state both halves of each enclosure. Every candidate
is bounded on the outer side, and an attained candidate bounds the other side. -/
def soundLimits (rows : List Located) (e : Extremes) : Prop :=
  (∀ r ∈ rows, e.minimum.lower ≤ r.value.lower ∧ r.value.upper ≤ e.maximum.upper) ∧
  (∃ r ∈ rows, r.value.upper ≤ e.minimum.upper) ∧
  (∃ r ∈ rows, e.maximum.lower ≤ r.value.lower)

instance (rows : List Located) (e : Extremes) : Decidable (soundLimits rows e) := by
  unfold soundLimits
  infer_instance

def summarize (rows : List Located) : Option Extremes := do
  let first :: _ := rows | none
  let minBox := rows.foldl (fun (b : Bounds) r =>
    ⟨lowerOf b.lower r.value.lower, lowerOf b.upper r.value.upper⟩) first.value
  let maxBox := rows.foldl (fun (b : Bounds) r =>
    ⟨upperOf b.lower r.value.lower, upperOf b.upper r.value.upper⟩) first.value
  let result := Extremes.mk minBox maxBox
  if soundLimits rows result && InclinedDiagram.narrow minBox && InclinedDiagram.narrow maxBox
    then some result else none

def fieldRows (bits : Nat) (pieces : List Segment) (whole : Bounds) (field : Field) :
    Option (List String) := do
  let groups ← pieces.zipIdx.mapM fun (p, i) => do
    let rows ← candidates bits p field
    rows.mapM (locate bits p i whole)
  let rows := groups.flatten
  let bounds ← summarize rows
  let minBox := bounds.minimum
  let maxBox := bounds.maximum


  let label := if field == .slope then "S" else "D"
  let extrema := String.intercalate " " ([label, "bounds"] ++ boxText minBox ++ boxText maxBox)
  let locations := rows.filterMap fun row =>
    let low := row.value.lower ≤ minBox.upper
    let high := maxBox.lower ≤ row.value.upper
    if low || high then some (String.intercalate " " ([label, "location", toString row.piece,
      if low then "1" else "0", if high then "1" else "0"] ++ boxText row.station)) else none
  return extrema :: locations

def sheet {data : Partition} {basis : GlobalBasis} (bits member : Nat)
    (cert : Certificate data basis) : Option String := do
  let indices := InclinedDiagram.selected data member
  let pieces ← indices.mapM (recover bits cert)
  let geometry ← InclinedFrameIntervalGeometry.member bits data member (rootAt cert member)
  let ends ← pieces.zipIdx.mapM fun (p,i) => do
    let a ← evaluate bits p (quantity .slope) ⟨0,0⟩
    let b ← evaluate bits p (quantity .slope) ⟨1,1⟩
    let u ← evaluate bits p transverse ⟨0,0⟩
    let v ← evaluate bits p transverse ⟨1,1⟩
    return String.intercalate " " (["P", toString i, MemberDiagram.number p.left, MemberDiagram.number p.right]
      ++ boxText a ++ boxText b ++ boxText u ++ boxText v)
  let slopes ← fieldRows bits pieces geometry.length .slope
  let displacements ← fieldRows bits pieces geometry.length .displacement
  let report := String.intercalate "\n" (["CV2011_MEMBER_KINEMATICS_1", data.source.members[member]!.id]
    ++ ends ++ slopes ++ displacements)
  if report.utf8ByteSize ≤ 262144 then some report else none

def rigid (input : String) : Option String := do
  let p ← InclinedFrameIntervalWire.decode input
  let _ ← InclinedFrameIntervalWire.checkPacket p
  let data ← checkedPartition p.source
  let basis ← checkedGlobalBasis data
  let proposal : InclinedFrameIntervalBuild.Proposal data basis := {
    roots := fun i => p.roots[i.val]!, inverse := fun i j => p.inverse[i.val]![j.val]!, estimate := fun i => p.estimate[i.val]! }
  let cert ← InclinedFrameIntervalBuild.build p.bits proposal
  if InclinedFrameIntervalAssembly.check p.bits cert then sheet p.bits p.query.member cert else none

def released (input : String) : Option String := do
  let p ← InclinedRelease.Wire.decode input
  let _ ← InclinedRelease.Wire.report p
  let l ← InclinedRelease.layout p.source p.rules
  let proposal ← InclinedRelease.Wire.proposalFor l p
  let cert ← InclinedRelease.build l p.bits proposal
  if InclinedRelease.verified l p.bits cert then sheet p.bits p.query.member cert else none

def spring (input : String) : Option String := do
  let p ← FrameSpring.Wire.decode input
  let _ ← FrameSpring.Wire.report p
  let (l,ks) ← FrameSpring.resolve p.source p.rules
  let proposal ← FrameSpring.Wire.proposalFor l p
  let cert ← FrameSpring.build l ks p.bits proposal
  if FrameSpring.verified l ks p.bits cert then sheet p.bits p.query.member cert else none

@[export member_kinematics_report]
def checkReport (input : String) : Option String :=
  if input.startsWith "CV2011_ROTATIONAL_SPRING_1\n" then spring input
  else if input.startsWith "CV2011_INCLINED_RELEASE_1\n" then released input
  else rigid input

end MemberKinematics
