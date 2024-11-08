-- Define a partial map from Nat to Nat (simplified for FFI)
structure PartialMapNat where
  get : Nat → Option Nat

-- Recursive helper function
def helper2 (n : Nat) (memo : PartialMapNat) : IO Nat :=
  match memo.get n with
  | some v => pure v
  | none =>
    if n ≤ 8 then
      pure n
    else do
      let r1 ← helper2 (n / 2) memo
      let r2 ← helper2 (n / 3) memo
      let r3 ← helper2 (n / 4) memo
      pure $ max n (r1 + r2 + r3)

-- Exported function for C to call directly
@[export helper2_c]
def helper2_c (n : UInt32) (m : PartialMapNat) : IO UInt32 :=
  if n.toNat ≤ 8 then
    pure n
  else do
    let r1 ← helper2 (n.toNat / 2) m
    let r2 ← helper2 (n.toNat / 3) m
    let r3 ← helper2 (n.toNat / 4) m
    let exchangeSum := r1 + r2 + r3
    pure $ max n (UInt32.ofNat exchangeSum)
