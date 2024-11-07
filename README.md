# Bytelandian Gold Coin Problem Solver

This repository contains a Lean implementation and proof of correctness of a dynamic programming algorithm to solve the Bytelandian gold coin problem. The algorithm computes the maximum amount of American dollars obtainable from a Bytelandian gold coin of value n, using memoization with proof-carrying values to prove correctness.

## Problem Description

Each Bytelandian gold coin has an integer n written on it. You have two options:

Sell the Coin Directly: Sell the coin for n dollars (1:1 exchange rate).

Exchange the Coin: Exchange the coin in a bank for three smaller coins with values n/2, n/3, and n/4 (all rounded down).

Your goal is to determine the maximum dollars obtainable from a coin of value n (where 0 ≤ n ≤ 1,000,000,000).

## Solution Overview

This is a Dynamic programming problem. We can observe that for amount upto 8, we can’t get more money by dividing (into n/2, n/3 and n/4). We will create an array to memoize the values. For any value, the minimum amount we can get out of it is n. We will compare this value with the value we get after dividing n and select the bigger value.

## Proof-Carrying Memoization: Ensuring Correctness with Dependent Types

Proving correctness for memoized algorithms requires ensuring invariants of the data structure on cached values. This solution uses dependent types and proof-carrying data structures to attach logical properties to cached values directly in the memoization map. Each entry in the memoization map is paired with a proof that it was compited properly, proving the correctness of the algorithm within the algorithm itself.

Specification Function: The function `maxDollars_spec` is the condition that each computed value must satisfy, it defines the maximum dollars obtainable for a coin of value `n`.

Memoization with Proofs: The custom map `WeakMHMap` stores pairs `(k, v)` with a proof that `maxDollars_spec k = v`, ensuring all cached values meet the specification.

Enforcing the Invariant: Each computed value is stored with a proof that it meets the specification, preserving correctness across entries.

Why This Works: By attaching proofs to every entry, the map becomes a proof-carrying structure. This approach modularizes correctness verification by verifying each computed result as it’s added.

The entire implementation is in Coins/CoinSolution.lean
