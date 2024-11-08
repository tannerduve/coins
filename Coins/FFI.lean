-- Define a partial map from Nat to Nat (simplified for FFI)
structure PartialMapNat where
  get : Nat → Option Nat

def exampleMap : PartialMapNat := {
  get := fun n => if n = 0 then some 1 else none
}

-- Recursive helper function
def helper2 (n : Nat) (memo : PartialMapNat) : Nat :=
  match memo.get n with
  | some v =>  v
  | none =>
    if n ≤ 8 then
      n
    else
      let r1 := helper2 (n / 2) memo
      let r2 := helper2 (n / 3) memo
      let r3 := helper2 (n / 4) memo
      max n (r1 + r2 + r3)

-- Exported function for C to call directly
@[export helper2_c]
def helper2_c (n : UInt32) : UInt32 :=
  if n.toNat ≤ 8 then
    n
  else
    let empty: PartialMapNat := {get := fun _ => Option.none}
    let exchangeSum := (helper2 (n.toNat / 2) empty) + (helper2 (n.toNat / 3) empty) + (helper2 (n.toNat / 4) empty)
    max n (UInt32.ofNat exchangeSum)
