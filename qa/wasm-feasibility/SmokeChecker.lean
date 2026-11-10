import Batteries.Data.Rat.Basic

/-! Public synthetic runtime probe. No portal definitions or private input. -/
namespace WasmSmoke

/-- The executable acceptance predicate used by the separate soundness proof. -/
def accepts (a x : Rat) : Bool := decide (2 * x = a)

/-- The C wrapper validates the bounded canonical decimal format first.
    These additional checks reject failed conversions and zero denominators.
    `mkRat` normalizes fractions, including zero, using exact integer arithmetic. -/
@[export smoke_check]
def checkStrings (an ad xn xd : String) : UInt32 :=
  match an.toInt?, ad.toNat?, xn.toInt?, xd.toNat? with
  | some an, some ad, some xn, some xd =>
    if ad == 0 || xd == 0 then 2
    else if accepts (mkRat an ad) (mkRat xn xd) then 1 else 0
  | _, _, _, _ => 2

end WasmSmoke
