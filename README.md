# Bytelandian Coin Problem

This repository contains a Lean implementation of an efficient algorithm to solve the Bytelandian gold coin problem. The algorithm computes the maximum amount of American dollars obtainable from a Bytelandian gold coin of value n, using memoization with proof-carrying values to ensure correctness.

## Problem Description

In Byteland, each gold coin has an integer n written on it. You have two options:

Sell the Coin Directly: Sell the coin for n dollars (1:1 exchange rate).
Exchange the Coin: Exchange the coin in a bank for three smaller coins with values n/2, n/3, and n/4 (all rounded down).
Your goal is to determine the maximum amount of dollars obtainable from a coin of value n (where 0 ≤ n ≤ 1,000,000,000).

## Solution Overview

This problem is well-suited for a dynamic programming approach due to overlapping subproblems and optimal substructure. To compute the solution efficiently, we use memoization while also ensuring that each stored value is provably correct according to a specification.

## Implementation Details

### Language and Dependencies

Language: Lean 4

Dependencies:
Std.Data.HashMap: Provides the HashMap data structure for memoization.

Mathlib.Tactic.Cases, Mathlib.Tactic.Linarith: Tactics for case analysis and arithmetic proofs.
Key Functions

Specification Function (maxDollars_spec): Defines the maximum dollars obtainable for a coin of value n.
For n ≤ 8, returns n directly.
For n > 8, returns max(n, maxDollars_spec(n/2) + maxDollars_spec(n/3) + maxDollars_spec(n/4)).

Memoization Map with Proofs (WeakMHMap): A custom map that stores both values and proofs that each entry is correct according to the specification.

Recursive Helper Function (helper): Computes the maximum dollars for a given n, carries proofs with each computed value, and updates the memoization map accordingly.

Main Function (maxDollars): Initializes the computation with an empty memoization map and retrieves the final result.

Proof-Carrying Memoization: Ensuring Correctness with Dependent Types

One challenge in proving correctness of memoized algorithms is maintaining invariants on cached values. This solution uses dependent types and proof-carrying data structures to ensure correctness by attaching proofs directly to each entry in the memoization map.

Specification Function: The function maxDollars_spec acts as the standard that each computed value must satisfy.

Memoization with Proofs: The custom map WeakMHMap stores pairs (k, v) with a proof that maxDollars_spec k = v, ensuring all cached values meet the specification.
Enforcing the Invariant: Each computed value is stored with a proof that it meets the specification, preserving the invariant throughout the computation.
Why This Works: By attaching proofs to every entry, the map becomes a proof-carrying structure. This approach modularizes correctness verification by verifying each computed result as it’s added.
