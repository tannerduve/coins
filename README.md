# Bytelandian Coin Problem

This repository contains a Lean implementation of an efficient algorithm to solve the Bytelandian gold coin problem. The algorithm computes the maximum amount of American dollars obtainable from a Bytelandian gold coin of value n, using memoization with proof-carrying values to ensure correctness.

## Problem Description

In Byteland, each gold coin has an integer n written on it. You have two options:

Sell the Coin Directly: Sell the coin for n dollars (1:1 exchange rate).
Exchange the Coin: Exchange the coin in a bank for three smaller coins with values n/2, n/3, and n/4 (all rounded down).
Your goal is to determine the maximum amount of dollars obtainable from a coin of value n (where 0 ≤ n ≤ 1,000,000,000).

## Solution Overview

This problem is well-suited for a dynamic programming approach due to overlapping subproblems and optimal substructure. To compute the solution efficiently, we use memoization while also ensuring that each stored value is provably correct according to a specification.

## Proof-Carrying Memoization: Ensuring Correctness with Dependent Types

One challenge in proving the correctness of memoized algorithms is maintaining a proof of invariants on the cached values. In typical dynamic programming, we use memoization to avoid recomputing values, but proving correctness can be tricky when memoized results introduce state.

Using Dependent Types to Maintain Invariants

This solution uses dependent types and proof-carrying data structures to ensure correctness. The idea is to attach logical properties directly to the data in the memoization map. Instead of storing just values, we store each value with a proof that it meets the function’s specification.

Here’s the approach:

Specification Function: We start by defining a specification function maxDollars_spec that outlines the correct result for any input n. This function serves as the standard our computed values must meet.
Memoization with Proofs: Instead of a standard map, we use a specialized memoization map (WeakMHMap) where each entry is a pair (k, v) with a proof that maxDollars_spec k = v. This proof-carrying structure guarantees that all cached values satisfy the specification.
abbrev WeakMHMap (ftarget : Nat → Nat) := HashMap Nat { c : Nat × Nat // ftarget c.fst = c.snd }
Each entry { c : Nat × Nat // ftarget c.fst = c.snd } ensures that for every key k, the associated value v is correct as per ftarget (here, maxDollars_spec).
Enforcing the Invariant: Whenever we compute a new value for n, we also generate a proof that it satisfies maxDollars_spec n. We store this value and its proof in the map, preserving the invariant across all entries.
Why This Works: By attaching proofs to every entry, the memoization map becomes a proof-carrying structure. We no longer need to prove the correctness of the entire function at once; instead, we verify each computed result as it’s added. This modular approach simplifies correctness verification, as each part of the computation is proven independently.

## Implementation Details

### Language and Dependencies

Language: Lean 4

Dependencies:
Std.Data.HashMap: Provides the HashMap data structure for memoization.

Mathlib.Tactic.Cases, Mathlib.Tactic.Linarith: Tactics for case analysis and arithmetic proofs.
Key Functions

#### Specification Function (maxDollars_spec): 

Defines the maximum dollars obtainable for a coin of value n.

For n ≤ 8, returns n directly.

For n > 8, returns max(n, maxDollars_spec(n/2) + maxDollars_spec(n/3) + maxDollars_spec(n/4)).

#### Memoization Map with Proofs (WeakMHMap):

A custom map that stores both values and proofs that each entry is correct according to the specification.

#### Recursive Helper Function (helper): 

Computes the maximum dollars for a given n, carries proofs with each computed value, and updates the memoization map accordingly.

#### Main Function (maxDollars): 

Initializes the computation with an empty memoization map and retrieves the final result.

#### Proof-Carrying Memoization: 

Ensuring Correctness with Dependent Types

A challenge in proving correctness of memoized algorithms is maintaining invariants on cached values. This solution uses dependent types and proof-carrying data structures to ensure correctness by attaching proofs directly to each entry in the memoization map.

Specification Function: The function maxDollars_spec acts as the standard that each computed value must satisfy.

Memoization with Proofs: The custom map WeakMHMap stores pairs (k, v) with a proof that maxDollars_spec k = v, ensuring all cached values meet the specification.

Enforcing the Invariant: Each computed value is stored with a proof that it meets the specification, preserving the invariant throughout the computation.

Why This Works: By attaching proofs to every entry, the map becomes a proof-carrying structure. This approach modularizes correctness verification by verifying each computed result as it’s added.
