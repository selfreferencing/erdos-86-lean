# TASK: Prove K10 Covers All Hard10 Primes

## Context (Critical Updates)

We discovered that the original theorem "K10 covers all Mordell-hard primes" is **FALSE**.

**Verified facts:**
- K10 = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29} fails for 18 Mordell-hard primes ≤ 10^7
- k ∈ {0, 1, 2} (m = 3, 7, 11) handles 86.7% of Mordell-hard primes
- K10 handles the remaining 13.3% (the "Hard10" primes)

## The Corrected Theorem

**Definition (Hard10):** A prime p is Hard10 iff:
1. p is Mordell-hard (p mod 840 ∈ {1, 121, 169, 289, 361, 529})
2. k=0 (m=3) does NOT provide a Type II witness
3. k=1 (m=7) does NOT provide a Type II witness
4. k=2 (m=11) does NOT provide a Type II witness

**Theorem (k10_covers_hard10):** For every Hard10 prime p, at least one k ∈ K10 provides a Type II witness.

**Type II witness condition:** ∃ d | x_k², d ≤ x_k, d ≡ -x_k (mod m_k)

where x_k = (p + m_k)/4 and m_k = 4k + 3.

## What We Know About Hard10 Primes

1. **Distribution:** 2,725 Hard10 primes among 20,513 Mordell-hard primes ≤ 10^7
2. **All verified:** Every Hard10 prime ≤ 10^7 has a K10 witness (computationally verified)
3. **Cascade pattern:** k=5 catches most, then k=7, k=9, etc.

## Characterizing When Small k Fails

k=0 (m=3) fails when: x_0 = (p+3)/4 has no divisor d with d ≡ -x_0 (mod 3)
- d=1 works iff x_0 ≡ 2 (mod 3), i.e., p ≡ 5 (mod 12)
- For Mordell-hard p ≡ 1 (mod 12), d=1 fails

k=1 (m=7) fails when: x_1 = (p+7)/4 has no divisor d with d ≡ -x_1 (mod 7)

k=2 (m=11) fails when: x_2 = (p+11)/4 has no divisor d with d ≡ -x_2 (mod 11)

## YOUR TASK

Prove that **every Hard10 prime has a K10 witness**.

### Approach 1: Algebraic Characterization

Characterize Hard10 primes algebraically:
- What congruence conditions on p make k=0,1,2 ALL fail?
- Show these conditions force some k ∈ K10 to succeed

### Approach 2: Covering Argument

Show the 10 moduli m_k (for k ∈ K10) cover all residue classes that Hard10 creates:
- m_5 = 23, m_7 = 31, m_9 = 39, m_11 = 47, m_14 = 59
- m_17 = 71, m_19 = 79, m_23 = 95, m_26 = 107, m_29 = 119

### Approach 3: Asymptotic + Finite

1. Prove: For p > N (some explicit bound), Hard10 primes have a K10 witness
2. Verify computationally for p ≤ N

## Key Insight from GPT Analysis

The "Legendre witness" condition (∃ factor q with (p/q) = -1) is NECESSARY but NOT SUFFICIENT.

Even when x_k has a "bad" factor q with (q/m_k) = -1, there might be no divisor d ≤ x_k that reaches the target -x_k mod m_k.

So the proof must address the actual divisor existence, not just the Legendre condition.

## Deliverable

Provide a rigorous proof (or proof strategy with explicit lemmas) that k10_covers_hard10 holds for ALL Hard10 primes, not just those ≤ 10^7.
