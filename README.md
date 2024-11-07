# Bytelandian Gold Coin Problem Solver

This repository contains a Lean implementation of an efficient algorithm to solve the Bytelandian gold coin problem. The algorithm computes the maximum amount of American dollars obtainable from a Bytelandian gold coin of value n, using memoization with proof-carrying values to prove correctness.

## Problem Description

Each Bytelandian gold coin has an integer n written on it. You have two options:

Sell the Coin Directly: Sell the coin for n dollars (1:1 exchange rate).

Exchange the Coin: Exchange the coin in a bank for three smaller coins with values n/2, n/3, and n/4 (all rounded down).

Your goal is to determine the maximum dollars obtainable from a coin of value n (where 0 ≤ n ≤ 1,000,000,000).

## Solution Overview

This problem is well-suited for a dynamic programming approach due to overlapping subproblems and optimal substructure. To compute the solution efficiently, we use memoization while also ensuring each stored value is provably correct according to a specification.

## Proof-Carrying Memoization: Ensuring Correctness with Dependent Types

Proving correctness for memoized algorithms can be challenging when ensuring invariants on cached values. This solution uses dependent types and proof-carrying data structures to attach logical properties to cached values directly in the memoization map. The algorithm's proof of correctness is encoded into the algorithm itself.

Specification Function: The function maxDollars_spec serves as the standard that each computed value must satisfy.

Memoization with Proofs: The custom map WeakMHMap stores pairs (k, v) with a proof that maxDollars_spec k = v, ensuring all cached values meet the specification.

Enforcing the Invariant: Each computed value is stored with a proof that it meets the specification, preserving correctness across entries.

Why This Works: By attaching proofs to every entry, the map becomes a proof-carrying structure. This approach modularizes correctness verification by verifying each computed result as it’s added, simplifying the proof.
