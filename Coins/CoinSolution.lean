import Std.Data.HashMap
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
open Std

/--
  Computes the maximum dollars obtainable from a Bytelandian gold coin of value `n`.
  Utilizes pure memoization with a `HashMap` to store intermediate results for efficiency.

  Problem Description:

  Each Bytelandian gold coin has an integer number written on it. A coin `n` can be exchanged in a bank into three coins: `n/2`, `n/3`, and `n/4`. These numbers are all rounded down (the banks have to make a profit).

  You can also sell Bytelandian coins for American dollars at an exchange rate of 1:1. However, you cannot buy Bytelandian coins.

  Given one gold coin of value `n`, where `0 ≤ n ≤ 1,000,000,000`, what is the maximum amount of American dollars you can get for it?

  Solution Overview:

  This is a dynamic programming problem. We use memoization to store intermediate results and avoid redundant computations.

  We define a recursive function `maxDollars_spec` as our specification, and then implement a memoized version that carries proofs of correctness using dependent types.
-/

-- Specification function defining the maximum dollars obtainable for a coin of value `n`.
def maxDollars_spec (n : Nat) : Nat :=
  if n ≤ 8 then
    n  -- Base case: for `n ≤ 8`, it's better to sell the coin directly.
  else
    max n (maxDollars_spec (n / 2) + maxDollars_spec (n / 3) + maxDollars_spec (n / 4))
    -- Recursive case: choose the maximum between selling the coin directly and exchanging it.

-- Define a memoization map (`WeakMHMap`) with proof-carrying values.
-- Each entry maps a `Nat` to a pair `(k, v)` along with a proof that `ftarget k = v`.
abbrev WeakMHMap (ftarget : Nat → Nat) :=
  HashMap Nat { c : Nat × Nat // ftarget c.fst = c.snd }

-- Implement `WeakMHMap_find?` to retrieve a value and its proof from the memoization map.
def WeakMHMap_find? (ft : Nat → Nat) (hm : WeakMHMap ft) (a : Nat) : Option { b : Nat // ft a = b } :=
  match hf : hm.get? a with  -- Attempt to get the value associated with `a` in the map.
  | none => none            -- If not found, return `none`.
  | some x =>
    if heq : a = x.val.fst then  -- Check if the key `a` matches `x.val.fst`.
      have : ft a = x.val.snd := by
        have hx := x.property       -- Extract the proof that `ft x.val.fst = x.val.snd`.
        rw [← heq] at hx            -- Replace `x.val.fst` with `a` using `heq`.
        exact hx                    -- Conclude that `ft a = x.val.snd`.
      some ⟨ x.val.snd, this ⟩     -- Return the value and proof as `some`.
    else
      none  -- If the keys don't match (shouldn't happen), return `none`.

-- Implement `WeakMHMap_insert` to insert a value and its proof into the memoization map.
def WeakMHMap_insert (ft : Nat → Nat) (hm : WeakMHMap ft) (k : Nat) (v : Nat) (h : ft k = v) : WeakMHMap ft :=
  let cell : { c : Nat × Nat // ft c.fst = c.snd } := ⟨(k, v), h⟩  -- Create the cell with proof.
  hm.insert k cell  -- Insert the cell into the map at key `k`.

-- Recursive helper function for `maxDollars` with proof-carrying values.
-- It returns a pair of the computed value and the updated memoization map.
def helper (n : Nat) (memo : WeakMHMap maxDollars_spec) :
  { v : Nat // maxDollars_spec n = v } × WeakMHMap maxDollars_spec :=
  match WeakMHMap_find? maxDollars_spec memo n with
  | some result =>
    -- If `n` is already in the memoization map, return the cached value and the memo.
    -- `result` has type `{ v : Nat // maxDollars_spec n = v }`.
    (result, memo)
  | none =>
    if h : n ≤ 8 then
      -- Base case: for `n ≤ 8`.
      let v := n
      let h_spec : maxDollars_spec n = v := by simp [maxDollars_spec, h]
      -- Prove that `maxDollars_spec n = n` using simplification.
      let memo' := WeakMHMap_insert maxDollars_spec memo n v h_spec
      -- Insert `(n, v)` with proof into the memoization map.
      (⟨v, h_spec⟩, memo')
    else
      -- Recursive case: compute the values for `n / 2`, `n / 3`, and `n / 4`.
      let (r1, memo1) := helper (n / 2) memo
      let (r2, memo2) := helper (n / 3) memo1
      let (r3, memo3) := helper (n / 4) memo2
      -- `r1`, `r2`, `r3` are of type `{ v : Nat // maxDollars_spec (n / x) = v }`.
      -- `memo3` is the updated memoization map after all recursive calls.
      let exchangeSum := r1.val + r2.val + r3.val  -- Sum the values obtained from recursion.
      let v := max n exchangeSum  -- Decide whether to sell `n` directly or exchange it.
      -- Construct the proof that `maxDollars_spec n = v`.
      have h_spec : maxDollars_spec n = v := by
        unfold maxDollars_spec         -- Expand `maxDollars_spec n`.
        rw [if_neg h]                  -- Since `n > 8`, use the recursive case.
        rw [r1.property, r2.property, r3.property]
        -- Replace recursive calls with their computed values using the proofs from `r1`, `r2`, `r3`.
      let memo' := WeakMHMap_insert maxDollars_spec memo3 n v h_spec
      -- Insert the computed value and its proof into the memoization map.
      (⟨v, h_spec⟩, memo')  -- Return the computed value with proof and the updated memo.

-- Main function that initializes the memoization map and retrieves the final result.
def maxDollars (n : Nat) : Nat :=
  (helper n (HashMap.empty)).1  -- Start with an empty memoization map.

-- Example evaluations to test the function.
#eval maxDollars 12  -- Expected output: 13
#eval maxDollars 2   -- Expected output: 2
#eval maxDollars 8   -- Expected output: 8
#eval maxDollars 25  -- Expected output: 27
#eval maxDollars 520 -- Expected output: 689

-- Theorem stating that `maxDollars n` equals `maxDollars_spec n`.
theorem maxDollars_spec_correct (n : Nat) : maxDollars n = maxDollars_spec n := by
  unfold maxDollars
  -- Let `⟨v, h_spec⟩` be the result from `helper n HashMap.empty`.
  let ⟨v, h_spec⟩ := (helper n HashMap.empty).1
  -- Since `maxDollars n = v` and `maxDollars_spec n = v`, we conclude they are equal.
  exact h_spec.symm
