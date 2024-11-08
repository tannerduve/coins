-- import Coins.CoinSolution
-- Define a partial map from Nat to Nat (simplified for FFI)
structure PartialMapNat where
  get : Nat → Option Nat


-- Recursive helper function
def helper2ffi (n : Nat) (memo : PartialMapNat) : Nat :=
  match memo.get n with
  | some v =>  v
  | none =>
    if n ≤ 8 then
      n
    else
      let r1 := helper2ffi (n / 2) memo
      let r2 := helper2ffi (n / 3) memo
      let r3 := helper2ffi (n / 4) memo
      max n (r1 + r2 + r3)

-- Exported function for C to call directly
@[export helper2_c]
def helper2_c (n : UInt32) : UInt32 :=
  if n.toNat ≤ 8 then
    n
  else
    let empty: PartialMapNat := {get := fun _ => Option.none}
    let exchangeSum := (helper2ffi (n.toNat / 2) empty) + (helper2ffi (n.toNat / 3) empty) + (helper2ffi (n.toNat / 4) empty)
    max n (UInt32.ofNat exchangeSum)

-- Attempt to FFI the proven helper2 function - complicated types can't be converted to C.
-- @[export helper2_c]
-- def helper2_c (n : UInt32) : UInt32 :=
--   (helper n.toNat (Std.HashMap.empty)).1.1.toUInt32
