import Init

/-! Exact equilibrium and virtual work for a drawing with integer coordinates.
    A bar column has its chord at its first end and the opposite chord at the
    other end. The corresponding unknown is the signed axial force per metre. -/
namespace IdealTrussWire

structure Joint where
  id : String
  x : Int
  y : Int
  support : String
  rx : Int
  ry : Int
  fx : Int
  fy : Int
  deriving Inhabited

def small (s : String) : Option Int := do
  let n ← s.toInt?
  guard (n.natAbs ≤ 1000 && toString n == s)
  return n

def parseJoint (s : String) : Option Joint := do
  let [id,x,y,support,rx,ry,fx,fy] := s.splitOn "," | none
  guard (id.length == 1 && id.toList.all (fun c => c ≥ 'A' && c ≤ 'Z'))
  guard (["free","pin","roller"].contains support)
  let j := Joint.mk id (← small x) (← small y) support (← small rx) (← small ry) (← small fx) (← small fy)
  guard (support != "roller" || j.rx != 0 || j.ry != 0)
  return j

abbrev Row := Array Int

def primitive (row : Row) : Row := Id.run do
  let divisor := row.foldl (fun d v => Nat.gcd d v.natAbs) 0
  if divisor ≤ 1 then return row
  return row.map (fun v => v / (divisor : Int))

def csv (row : Row) : String := String.intercalate "," (row.toList.map toString)

def eliminate (input : Array Row) (width : Nat) : String := Id.run do
  let mut rows := input
  let mut pivots : Array Nat := #[]
  for c in [:width] do
    let p := pivots.size
    let mut found := rows.size
    for k in [p:rows.size] do
      if rows[k]![c]! != 0 then
        found := k
        break
    if found < rows.size then
      let base := rows[found]!
      let old := rows[p]!
      rows := (rows.set! found old).set! p base
      for k in [:rows.size] do
        let row := rows[k]!
        if k != p && row[c]! != 0 then
          rows := rows.set! k (primitive ((Array.range row.size).map fun i => base[c]! * row[i]! - row[c]! * base[i]!))
      pivots := pivots.push c
  let rank := pivots.size
  let mut lines := ["TRUSS1",toString rank]
  for k in [rank:rows.size] do
    -- Zero equilibrium rows: virtual work (negative RHS) and a null motion.
    lines := lines ++ ["M," ++ csv ((rows[k]!).extract width (rows[k]!).size)]
  if rank == width && rank == rows.size then
    for k in [:rank] do
      let row := rows[k]!
      lines := lines ++ ["F," ++ toString row[width]! ++ "," ++ toString row[pivots[k]!]!]
  return String.intercalate "\n" lines

@[export ideal_truss_report]
def report (source : String) : Option String := do
  let "TRUSS1" :: count :: rest := source.splitOn "\n" | none
  let n ← count.toNat?
  guard (n > 0 && n ≤ 26 && rest.length ≥ n && rest.length ≤ n + 64)
  let joints := (← (rest.take n).mapM parseJoint).toArray
  for i in [:n] do
    for k in [:i] do
      let a := joints[i]!
      let b := joints[k]!
      guard (a.id != b.id && (a.x != b.x || a.y != b.y))
  let mut columns : Array Row := #[]
  let mut pairs : List (Nat × Nat) := []
  for bar in rest.drop n do
    let [first,last] := bar.splitOn "," | none
    let some i := joints.findIdx? (fun j => j.id == first) | none
    let some k := joints.findIdx? (fun j => j.id == last) | none
    guard (i != k && !(pairs.contains (min i k,max i k)))
    pairs := (min i k,max i k) :: pairs
    let dx := joints[k]!.x - joints[i]!.x
    let dy := joints[k]!.y - joints[i]!.y
    let col := Array.replicate (2*n) (0:Int)
    columns := columns.push ((((col.set! (2*i) dx).set! (2*i+1) dy).set! (2*k) (-dx)).set! (2*k+1) (-dy))
  for i in [:n] do
    let j := joints[i]!
    let dirs : List (Int × Int) := if j.support == "pin" then [(1,0),(0,1)] else if j.support == "roller" then [(j.rx,j.ry)] else []
    for (x,y) in dirs do
      let col := Array.replicate (2*n) (0:Int)
      columns := columns.push ((col.set! (2*i) x).set! (2*i+1) y)
  let rows := (Array.range (2*n)).map fun i =>
    let j := joints[i/2]!
    let load := if i%2 == 0 then j.fx else j.fy
    ((columns.map (fun col => col[i]!)).push (-load)) ++ ((Array.range (2*n)).map fun k => if k == i then 1 else 0)
  return eliminate rows columns.size

end IdealTrussWire
