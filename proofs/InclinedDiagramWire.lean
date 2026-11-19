import InclinedDiagram
import FrameSpringWire

namespace InclinedDiagram
open FrameIntervalOps InclinedFrameSource InclinedFrameBasis InclinedFrameIntervalAssembly
open InclinedFrameIntervalRecovery

/-- The horizontal span is taken from the original signed coordinates. The
length and local end actions use the checked geometry and equilibrium motion. -/
def fromSource {data : Partition} {basis : GlobalBasis} (bits : Nat)
    (cert : Certificate data basis) (i : Fin data.pieces.size) : Option InclinedDiagram.Piece := do
  let source := data.pieces[i.val]!
  let member := data.source.members[source.member]!
  let dx := data.source.nodes[member.b]!.x-data.source.nodes[member.a]!.x
  let span := source.right-source.left
  let memberIndex : Fin data.source.members.size ← if h : source.member < data.source.members.size then some ⟨source.member,h⟩ else none
  let motion ← localMotion bits cert i
  let v ← endAction bits cert i motion 1
  let negM ← endAction bits cert i motion 2
  let root ← InclinedFrameIntervalGeometry.member bits data source.member (cert.roots memberIndex)
  return ⟨source.left,source.right,root.length,v,scale (-1) negM,
    dx*span*source.vertical, dx*span*(source.verticalEnd-source.vertical)/2,#[],#[],0⟩

def boxText (b : Bounds) := [MemberDiagram.number b.lower,MemberDiagram.number b.upper]

def pieceText (p : InclinedDiagram.Piece) := String.intercalate " " (["P",MemberDiagram.number p.left,MemberDiagram.number p.right,
  MemberDiagram.number p.linear,MemberDiagram.number p.quadratic] ++ boxText p.memberLength ++
  boxText p.shearStart ++ boxText p.momentStart)

def candidateText (field : String) (all : List Candidate) (a : Candidate) : Option String := do
  let low ← isExtreme false a all
  let high ← isExtreme true a all
  return String.intercalate " " ([field,toString a.piece,a.side] ++ boxText a.t ++ boxText a.x ++ boxText a.y ++
    [if low then "1" else "0",if high then "1" else "0"])

def encode (bits : Nat) (identifier : String) (pieces : List InclinedDiagram.Piece) : Option String := do
  guard (!pieces.isEmpty)
  let group := fun (moment : Bool) => do
    let lists ← pieces.zipIdx.mapM fun (p,i) => rows bits i p moment
    let all := lists.flatten
    all.mapM (candidateText (if moment then "M" else "V") all)
  let shear ← group false
  let moment ← group true
  let output := String.intercalate "\n" (["CV2011_INCLINED_DIAGRAM_1",identifier] ++ pieces.map pieceText ++ shear ++ moment)
  if output.utf8ByteSize ≤ 262144 then some output else none

def selected (data : Partition) (m : Nat) :=
  (List.finRange data.pieces.size).filter fun i => data.pieces[i.val]!.member == m

/-- A form supported only on the length coordinate equals its coefficient
times L. A form supported only on the constant coordinate is rational. -/
def onlyCoefficient (row : Statics.Row) (i : Nat) : Option Rat :=
  if row.set! i 0 == Array.replicate row.size 0 then some row[i]! else none

def withStatics (data : Partition) (system : Statics.System) (i : Fin data.pieces.size)
    (p : InclinedDiagram.Piece) : InclinedDiagram.Piece := Id.run do
  let segment := data.pieces[i.val]!
  let member := data.source.members[segment.member]!
  let a := data.source.nodes[member.a]!
  let b := data.source.nodes[member.b]!
  let k := 6*i.val
  let lengthColumn := system.unknowns + segment.member
  let v := Statics.reduce system (Statics.equation system.width [(k,a.y-b.y),(k+1,b.x-a.x)])
  let m := Statics.reduce system (Statics.equation system.width [(k+2,-1)])
  return {p with scaledShear := v, initialMoment := m, lengthColumn,
    shearStart := ((onlyCoefficient v lengthColumn).map singleton).getD p.shearStart,
    momentStart := ((onlyCoefficient m (system.width-1)).map singleton).getD p.momentStart}

def sheet {data : Partition} {basis : GlobalBasis} (bits m : Nat) (cert : Certificate data basis)
    (torques : Array (Fin basis.columns.size → Rat) := #[]) : Option String := do
  let system := Statics.assemble cert torques
  let pieces ← (selected data m).mapM fun i => (fromSource bits cert i).map (withStatics data system i)
  encode bits data.source.members[m]!.id pieces

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
  let torques := (l.sides.filter (fun side => ks[side]! != 0)).map (FrameSpring.relativeColumn l)
  if FrameSpring.verified l ks p.bits cert then sheet p.bits p.query.member cert torques else none

@[export inclined_diagram_report]
def checkReport (input : String) : Option String :=
  if input.startsWith "CV2011_ROTATIONAL_SPRING_1\n" then spring input
  else if input.startsWith "CV2011_INCLINED_RELEASE_1\n" then released input
  else rigid input

end InclinedDiagram
