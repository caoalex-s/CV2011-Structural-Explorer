import PortalTables

/-! Executable exact arithmetic only. The actual-model interpretation and
    stability proof are in PortalSoundness, outside the compiled import closure. -/
namespace PortalChecker

abbrev Motion := Fin 12 → Rat
abbrev Reactions := Fin 6 → Rat

def dotRow (q : Motion) (i : Fin 12) : Rat :=
  ((List.finRange 12).map fun j => stiffness i j * q j).foldl (· + ·) 0

def residual (a : Rat) (q : Motion) (i : Fin 12) : Rat := dotRow q i - a * force i

def baseIndex (i : Fin 6) : Fin 12 :=
  if h : i.val < 3 then ⟨i.val, by omega⟩ else ⟨i.val + 6, by omega⟩

def freeIndex (i : Fin 6) : Fin 12 := ⟨i.val + 3, by omega⟩

def midpointMoment (a : Rat) (q : Motion) : Rat :=
  (20000 / 6) * (q 8 - q 5) - (3 / 2) * a

def midpointDisplacement (a : Rat) (q : Motion) : Rat :=
  (q 4 + q 7) / 2 + (3 / 4) * (q 5 - q 8) + (27 / 160000) * a

/-- All 20 claimed outputs are checked. No floating solver status is an input.
    The two particular-load terms are essential even with exact nodal motion. -/
def Valid (a : Rat) (q : Motion) (r : Reactions) (moment displacement : Rat) : Prop :=
  (∀ i, q (baseIndex i) = 0) ∧
  (∀ i, residual a q (freeIndex i) = 0) ∧
  (∀ i, r i = residual a q (baseIndex i)) ∧
  moment = midpointMoment a q ∧ displacement = midpointDisplacement a q

instance (a : Rat) (q : Motion) (r : Reactions) (m u : Rat) : Decidable (Valid a q r m u) :=
  by unfold Valid; infer_instance

def accepts (a : Rat) (q : Motion) (r : Reactions) (m u : Rat) : Bool :=
  decide (Valid a q r m u)

/-- The C layer bounds ASCII, field count and decimal digits before allocation.
    This second decoder rejects failed conversions and nonpositive denominators. -/
def parseRational (n d : String) : Option Rat := do
  let numerator ← n.toInt?
  let denominator ← d.toNat?
  if denominator = 0 then none else some (mkRat numerator denominator)

@[export portal_check]
def checkString (input : String) : UInt32 := Id.run do
  let fields := (input.splitOn "\n").toArray
  if fields.size != 42 then return 2
  let mut values : Array Rat := #[]
  for i in [:21] do
    match parseRational (fields[i * 2]!) (fields[i * 2 + 1]!) with
    | none => return 2
    | some value => values := values.push value
  let a := values[0]!
  let q : Motion := fun i => values[i.val + 1]!
  let r : Reactions := fun i => values[i.val + 13]!
  return if accepts a q r values[19]! values[20]! then 1 else 0

end PortalChecker
