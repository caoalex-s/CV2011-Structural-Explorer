import RationalFrameWire

/-! Cardinal frame with shared point translations and independent released-end
    rotations. The rigid geometry compiler supplies the original member cuts
    and local element laws. All assembly indices, point actions and restraints
    are derived again from the connection rules in the source. -/
namespace HingeFrame
open RationalFrame

structure Connections where
  /-- 0 rigid, 1 pinned, 2 custom. Ends use 0 inherit, 1 rigid, 2 free. -/
  joints : Array Nat
  ends : Array Nat
  deriving Inhabited, Repr

/-- Source order provides the default reference member at a shared node. -/
def reference (source : Source) (node : Nat) : Nat :=
  source.nodes[node]!.reference.getD <| ((List.range source.members.size).find? fun m =>
    source.members[m]!.a == node || source.members[m]!.b == node).getD source.members.size

def releases (source : Source) (rules : Connections) : List Nat :=
  (List.range (2 * source.members.size)).filter fun side =>
    let member := side / 2
    let node := if side % 2 == 0 then source.members[member]!.a else source.members[member]!.b
    let rule := rules.ends[side]!
    reference source node != member && (rule == 2 || (rule == 0 && rules.joints[node]! == 1))

structure Assembly where
  mesh : Compiled
  sides : List Nat

def Assembly.size (a : Assembly) := a.mesh.dofs + a.sides.length

/-- Every extra coordinate corresponds to one physical side. The base
    rotation belongs to an incident reference member even at a pinned node. -/
def rotation (a : Assembly) (member : Nat) (t : Rat) (point : Nat) : Nat :=
  let side := 2 * member + (if t == 1 then 1 else 0)
  let slot := a.sides.idxOf side
  if (t == 0 || t == 1) && slot < a.sides.length then a.mesh.dofs + slot else 3 * point + 2

def index (a : Assembly) (s : Segment) (i : Fin 6) : Nat :=
  if i.val == 2 then rotation a s.member s.left s.a
  else if i.val == 5 then rotation a s.member s.right s.b
  else globalIndex s i

def localIndex (a : Assembly) (s : Segment) (row : Nat) : Option (Fin 6) :=
  (List.finRange 6).find? fun i => index a s i == row

def stiffness (a : Assembly) (row column : Nat) : Rat :=
  sumSegments a.mesh fun s =>
    match localIndex a s row, localIndex a s column with
    | some i, some j => coordinateSign s i * localStiffness s i j * coordinateSign s j
    | _, _ => 0

def pointIndex (a : Assembly) (member : Nat) (t : Rat) (direction : Nat) : Nat :=
  let point := locationIndex a.mesh member t
  if direction == 2 then rotation a member t point else 3 * point + direction

def force (a : Assembly) (row : Nat) : Rat :=
  (sumSegments a.mesh fun s => match localIndex a s row with
    | none => 0
    | some i => coordinateSign s i * localForce s i) +
  (a.mesh.source.loads.toList.map fun load =>
    if load.kind == 1 then
      if pointIndex a load.member load.t 2 == row then load.mz else 0
    else if load.kind == 0 then
      if pointIndex a load.member load.t 0 == row then load.fx
      else if pointIndex a load.member load.t 1 == row then load.fy else 0
    else 0).foldr (· + ·) 0

def restrained (a : Assembly) (row : Nat) : Bool :=
  a.mesh.source.supports.any fun support => [0, 1, 2].any fun d =>
    blocksDirection support d && pointIndex a support.member support.t d == row

/-- Recover on the chosen member side with its absolute end rotations. -/
def sectionValues (a : Assembly) (q : Query) (u : Array Rat) : Array Rat :=
  match selectedSegment a.mesh q with
  | none => #[]
  | some s =>
    let motion := (u.set! (3 * s.a + 2) u[index a s 2]!).set! (3 * s.b + 2) u[index a s 5]!
    recoverSegment s q.t motion

def tabulate (n : Nat) (f : Nat → α) := ((List.range n).map f).toArray

def Checked (a : Assembly) (q : Query) (w : Certificate) : Prop :=
  let n := a.size
  let k := tabulate n fun i => tabulate n (stiffness a i)
  let f := tabulate n (force a)
  let free := ((List.range n).filter fun i => !restrained a i).toArray
  w.points = a.mesh.points ∧ w.motion.size = n ∧
  (∀ i : Fin n, restrained a i.val = true → w.motion[i.val]! = 0) ∧
  (if w.mechanism then
    (¬ ∀ i : Fin n, w.motion[i.val]! = 0) ∧
    (∀ i : Fin n, arrayDot k[i.val]! w.motion = 0) ∧
    w.loadWork = arrayDot f w.motion ∧ w.reactions = #[] ∧ w.readouts = #[] ∧ w.lower = #[] ∧ w.diagonal = #[]
  else FactorValid k free w ∧ w.reactions = residual k f w.motion ∧
    (∀ i : Fin n, restrained a i.val = false → w.reactions[i.val]! = 0) ∧
    w.readouts = sectionValues a q w.motion ∧ w.loadWork = 0)

instance (a : Assembly) (q : Query) (w : Certificate) : Decidable (Checked a q w) := by
  unfold Checked
  split <;> infer_instance

def compile (geometry : Source) (rules : Connections) : Option Assembly := do
  guard (rules.joints.size == geometry.nodes.size && rules.ends.size == 2 * geometry.members.size)
  guard (rules.joints.all (· ≤ 2) && rules.ends.all (· ≤ 2))
  guard (sourceValid geometry)
  let mesh ← compileModel geometry
  guard (decide (PartitionValid mesh))
  let sides := releases geometry rules
  guard (!sides.isEmpty && mesh.dofs + sides.length ≤ 48)
  return ⟨mesh, sides⟩

def accepts (geometry : Source) (rules : Connections) (q : Query) (w : Certificate) : Bool :=
  match compile geometry rules with
  | none => false
  | some a => queryValid a.mesh q && decide (Checked a q w)

theorem acceptance_source (geometry : Source) (rules : Connections) (q : Query) (w : Certificate)
    (accepted : accepts geometry rules q w = true) :
    ∃ a, compile geometry rules = some a ∧ queryValid a.mesh q = true ∧ Checked a q w := by
  cases h : compile geometry rules with
  | none => simp [accepts, h] at accepted
  | some a => exact ⟨a, rfl, by simpa [accepts, h] using accepted⟩

end HingeFrame
