# TASK: Find Covering Congruence System for K13

## Context

We need to prove K13 = {0,1,2,5,7,9,11,14,17,19,23,26,29} covers all Mordell-hard primes.

**Idea:** Find a finite set of congruence conditions that guarantee at least one k ∈ K13 works.

## The Covering Congruence Approach

A "covering system" for K13 would be:
- A modulus M
- For each residue class r mod M with p = 4r-3 Mordell-hard, identify which k ∈ K13 works

If we can show every Mordell-hard residue class mod M has at least one working k, we're done.

## What We Know

Mordell-hard primes: p mod 840 ∈ {1, 121, 169, 289, 361, 529}

These correspond to r = (p+3)/4 mod 210:
- p ≡ 1 (mod 840) → r ≡ 1 (mod 210)
- p ≡ 121 (mod 840) → r ≡ 31 (mod 210)
- p ≡ 169 (mod 840) → r ≡ 43 (mod 210)
- p ≡ 289 (mod 840) → r ≡ 73 (mod 210)
- p ≡ 361 (mod 840) → r ≡ 91 (mod 210)
- p ≡ 529 (mod 840) → r ≡ 133 (mod 210)

## The d=1 Sufficient Condition

For k with m = 4k+3, d=1 works iff x_k ≡ m-1 (mod m), i.e., r+k ≡ -1 (mod m).

This gives: r ≡ -k-1 (mod m) = -(4k+4) ≡ 4k+3-4k-4 = -1 (mod m)

So d=1 works for k iff r ≡ m-k-1 (mod m).

## YOUR TASK

1. **For each k ∈ K13, compute the residue classes of r (mod m_k) where d=1 works.**

2. **Check if these cover all 6 Mordell-hard residue classes mod 210** (or some larger modulus).

3. **If d=1 doesn't cover everything, extend to d>1:**
   - For small primes q | x_k, compute which residue classes of r allow a witness

4. **Find the minimal M** such that every Mordell-hard r mod M has at least one k ∈ K13 that works.

## Data: The m_k Values

| k | m_k | m_k - k - 1 (d=1 condition) |
|---|-----|---------------------------|
| 0 | 3 | 2 |
| 1 | 7 | 5 |
| 2 | 11 | 8 |
| 5 | 23 | 17 |
| 7 | 31 | 23 |
| 9 | 39 | 29 |
| 11 | 47 | 35 |
| 14 | 59 | 44 |
| 17 | 71 | 53 |
| 19 | 79 | 59 |
| 23 | 95 | 71 |
| 26 | 107 | 80 |
| 29 | 119 | 89 |

So d=1 works for:
- k=0 iff r ≡ 2 (mod 3)
- k=1 iff r ≡ 5 (mod 7)
- k=2 iff r ≡ 8 (mod 11)
- etc.

## The Question

Do the conditions "r ≡ 2 (mod 3) OR r ≡ 5 (mod 7) OR r ≡ 8 (mod 11) OR ..." cover all Mordell-hard residue classes?

If not for d=1 alone, what about including d=2, d=3, etc.?

## Deliverable

Either:
1. A proof that the covering conditions span all Mordell-hard r, OR
2. Identification of the "gap" residue classes that need special handling
