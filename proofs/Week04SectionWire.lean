import IdealTrussWire

/-! Executable check for the Week 04 example. A term (x,y,m) multiplies
    F / √(x²+y²), where F is positive in the assumed arrow direction.
    Reactions and applied loads use cardinal directions. -/
namespace Week04SectionWire
open IdealTrussWire

structure Term where
  name : String
  x : Int
  y : Int
  moment : Int
  component : Int
  deriving Inhabited

def term (name : String) (atJoint centre : Joint) (x y component : Int) : Term :=
  ⟨name,x,y,(atJoint.x-centre.x)*y - (atJoint.y-centre.y)*x,component⟩

def formatTerm (t : Term) : String := String.intercalate "," [
  t.name,toString t.x,toString t.y,toString t.moment,toString (t.x*t.x+t.y*t.y),toString t.component]

def layout : List (String × Int × Int × String) := [
  ("A",0,-2,"free"),("B",2,0,"free"),("G",2,-2,"free"),("C",4,0,"free"),
  ("F",4,-2,"free"),("D",6,0,"pin"),("E",6,-2,"roller")]

def topology : List (String × String) := [
  ("A","B"),("A","G"),("B","G"),("B","C"),("G","C"),("G","F"),
  ("C","F"),("C","D"),("F","D"),("F","E"),("D","E")]

def sameBar (a b : String × String) : Bool :=
  a == b || (a.1 == b.2 && a.2 == b.1)

def scaledForce (rows : Array String) (index : Nat) (scale : Int) : Option Int := do
  let row ← rows[index]?
  let ["F",top,bottom] := row.splitOn "," | none
  let n ← top.toInt?
  let d ← bottom.toInt?
  guard (d != 0 && (scale*n)%d == 0)
  return scale*n/d

@[export week04_section_report]
def report (packet : String) : Option String := do
  let "SECTION1" :: cutText :: side :: centreId :: source := packet.splitOn "\n" | none
  let cut ← small cutText
  guard (side == "left" || side == "right")
  let "TRUSS1" :: "7" :: body := source | none
  guard (body.length == 18)
  let joints ← (body.take 7).mapM parseJoint
  let lookup := fun id => joints.find? (fun j => j.id == id)
  for (id,x,y,support) in layout do
    let j ← lookup id
    guard (j.x == x && j.y == y && j.support == support && j.fx == 0 && (id == "A" || j.fy == 0))
    if id == "E" then guard (j.rx == 1 && j.ry == 0)
  let centre ← lookup centreId
  let load ← lookup "A"
  let p := -load.fy
  let mut bars : Array (String × String) := #[]
  for line in body.drop 7 do
    let [a,b] := line.splitOn "," | none
    guard (topology.any (sameBar (a,b)) && !bars.any (sameBar (a,b)))
    bars := bars.push (a,b)
  -- Derive signed force densities and reaction coefficients from every joint equation.
  let equilibrium ← IdealTrussWire.report (String.intercalate "\n" source)
  let "TRUSS1" :: "14" :: forces := equilibrium.splitOn "\n" | none
  guard (forces.length == 14)
  let rows := forces.toArray
  let retained := fun (j : Joint) => if side == "left" then j.x < cut else j.x > cut
  guard (joints.all fun j => j.x != cut)
  let mut terms := #[]
  for pair in [("B","C"),("G","C"),("G","F")] do
    let a ← lookup pair.1
    let b ← lookup pair.2
    guard (retained a != retained b)
    let i ← bars.findIdx? (sameBar pair)
    let start := if retained a then a else b
    let finish := if retained a then b else a
    let dx := finish.x-start.x
    let dy := finish.y-start.y
    let g : Int := Nat.gcd dx.natAbs dy.natAbs
    guard (g > 0)
    terms := terms.push (term (pair.1++pair.2) start centre (dx/g) (dy/g) (← scaledForce rows i g))
  let mut offset := bars.size
  let mut reactions := #[]
  for j in joints do
    let dirs : List (String × Int × Int) := if j.support == "pin" then [("Dx",1,0),("Dy",0,1)]
      else if j.support == "roller" then [("Ex",j.rx,j.ry)] else []
    for (name,x,y) in dirs do
      let value ← scaledForce rows offset 1
      offset := offset+1
      reactions := reactions.push (name++","++toString value)
      if retained j then terms := terms.push (term name j centre x y value)
  if retained load then terms := terms.push (term "P" load centre 0 (-1) p)
  let sums := terms.foldl (fun (s : Int × Int × Int) t =>
    (s.1+t.x*t.component,s.2.1+t.y*t.component,s.2.2+t.moment*t.component)) (0,0,0)
  guard (sums == (0,0,0))
  return String.intercalate "\n" (["SECTION1", String.intercalate "," [cutText,side,centreId,toString p]] ++
    (terms.map formatTerm).toList ++ reactions.toList ++ ["SUM,0,0,0"])

end Week04SectionWire
