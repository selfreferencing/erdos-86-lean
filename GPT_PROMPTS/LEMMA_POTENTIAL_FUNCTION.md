# GPT Prompt: Potential Function for Zeroless Run Bounds

## Context

This is part of the proof of the Erdos 86 Conjecture: the set {n >= 1 : 2^n has no digit 0 in base 10} is finite, with maximum element 86.

A previous GPT consultation verified the core lemmas but showed that the naive "count 5's" approach fails. This prompt asks for a sharper potential function that can actually bound zeroless runs.

## Verified Results (from Previous Consultation)

### Zero-Creation Lemma (VERIFIED)

When doubling digit d with incoming carry c:
- Output digit d' = (2d + c) mod 10
- Output carry c' = floor((2d + c) / 10)

**Result:** d' = 0 if and only if (c = 0 AND d ∈ {0, 5}).

In words: The ONLY way to create a 0 digit when doubling is from digit 5 with incoming carry 0.

### Carry Propagation Lemma (VERIFIED)

**Result:** c' = 1 if and only if d >= 5.

The outgoing carry depends ONLY on the digit, not on the incoming carry. This is because:
- If d <= 4: max(2d + c) = 2(4) + 1 = 9 < 10, so c' = 0
- If d >= 5: min(2d + c) = 2(5) + 0 = 10 >= 10, so c' = 1

### 5-Production Lemma (CORRECTED)

A digit 5 is produced if and only if (c = 1 AND d ∈ {2, 7}).

Proof: Need (2d + 1) mod 10 = 5, i.e., 2d ≡ 4 (mod 10), i.e., d ≡ 2 (mod 5).
With d ∈ {0,...,9}: d ∈ {2, 7}.

**Critical asymmetry in 5-production:**
- From d = 2 with c = 1: 2(2) + 1 = 5 < 10, so outgoing carry = 0 (chain BREAKS)
- From d = 7 with c = 1: 2(7) + 1 = 15 >= 10, so outgoing carry = 1 (chain CONTINUES)

### Carry Source Classification

Digits split into three categories by their ability to protect 5's (i.e., produce carry 1):

**One-shot protectors (5, 6):** Always become < 5 after doubling.
- 5 → 0 (if c=0) or 1 (if c=1)
- 6 → 2 (if c=0) or 3 (if c=1)
- Can only protect once, then "used up"

**Stable protectors (8, 9):** Remain >= 5 after doubling.
- 8 → 6 (if c=0) or 7 (if c=1)
- 9 → 8 (if c=0) or 9 (if c=1)
- Can protect repeatedly across multiple doublings

**Conditional protector (7):** Stays >= 5 only with incoming carry 1.
- 7 with c=0 → 4 (becomes non-protector)
- 7 with c=1 → 5 (stays protector but becomes one-shot)

### Why the Naive Bound Fails

The proposed theorem "after at most k+1 doublings (where k = number of 5's), a 0 must appear" is FALSE.

**Counterexample 1:** A = 11 (k = 0).
Orbit: 11 → 22 → 44 → 88 → 176 → 352 → 704
Survives 6 doublings (not the predicted 1).

**Counterexample 2:** A = 5583 (k = 2).
Survives 19 doublings before hitting a zero (not the predicted 3).

**Why it fails:**
1. Numbers without 5's can double many times zerolessly (5-free stretches)
2. Stable protectors (8, 9) can protect 5's repeatedly without being "used up"
3. New 5's can be created from 2's and 7's, so the 5-count isn't monotone

## The Challenge

A valid bound on zeroless runs requires controlling TWO quantities:
- **f(m):** Bound on "protected-5 events" (times a 5 survives via protection)
- **h(m):** Max length of zeroless run with NO 5 in the prefix

Then: # zeroless visits ≤ (f(m) + 1) × (h(m) + 1)

But we want something stronger: a potential function Phi that:
1. Is non-negative
2. Decreases (or stays bounded) under doubling while the prefix stays zeroless
3. Eventually forces either a 0 or termination

## Questions for GPT

### Q1: Design a Potential Function

Using the verified lemmas and the carry source classification, design a potential function Phi(A) for m-digit zeroless integers A such that:

(a) Phi(A) >= 0 for all zeroless A
(b) If doubling A produces a zeroless result A', then Phi(A') <= Phi(A) + C for some absolute constant C
(c) Either Phi(A') < Phi(A) - epsilon for some epsilon > 0, OR the number of "neutral" steps (where Phi doesn't decrease) is bounded

The potential should account for:
- The number and positions of 5's
- The number and positions of stable protectors (8, 9)
- The number and positions of 5-producers (2, 7 with high neighbor)
- The carry landscape

### Q2: Bound 5-Free Stretches

Consider an m-digit zeroless integer A with NO digit 5 anywhere.

(a) What is the maximum number of consecutive doublings that can keep the prefix zeroless?

(b) Must a 5 eventually appear? If so, after how many steps?

(c) How does the digit composition constrain this? (E.g., if A has many 2's and 7's with high neighbors, 5's will be produced quickly.)

### Q3: Bound Protected-5 Events

Suppose the m-digit prefix has a 5 at some position, and this 5 is protected (its right neighbor is >= 5).

(a) After the 5 turns into 1, what happens to the protector? Track the cascade.

(b) How many times can this protection mechanism repeat before either:
   - A 0 is created, or
   - The prefix exits some bounded region of configuration space?

### Q4: Synthesize into a Finiteness Argument

Combine Q1-Q3 into an argument that for any m-digit zeroless prefix A:
- The orbit A → 2A → 4A → ... (taking m-digit prefixes) can visit the zeroless set at most g(m) times for some explicit function g(m).

### Q5: Apply to Powers of 2 Specifically

The above analysis applies to arbitrary integers. But we care specifically about prefixes of 2^n.

(a) What additional constraints does this impose? (E.g., the fractional part of n*log10(2) determines the prefix.)

(b) Can the specific structure of powers of 2 strengthen the bounds?

(c) The computational fact is: N_m = 0 for all m >= 36 (verified to m = 3000). Can your potential function explain why this threshold occurs around m ~ 36?

## Computational Data

- N_m = 0 for all m >= 36 (verified through m = 3000)
- Maximum N_m = 9 (at m = 9)
- The last zeroless power of 2 is 2^86

## What Would Constitute Success

- A well-defined potential function Phi with the properties in Q1
- A proof that 5-free zeroless stretches are bounded (Q2)
- A proof that protected-5 events are bounded (Q3)
- A synthesis showing g(m) = O(1) or at least g(m) = o(L_m) where L_m ~ 3.3m (Q4)
- Insight into why powers of 2 specifically behave as observed (Q5)

## Notation Summary

- m: number of digits in the prefix
- d: a single digit (0-9)
- c: incoming carry (0 or 1)
- d': output digit = (2d + c) mod 10
- c': output carry = floor((2d + c) / 10)
- "Protected 5": a digit 5 whose right neighbor is >= 5 (so it receives carry 1)
- "Unprotected 5": a digit 5 whose right neighbor is < 5 (so it receives carry 0 and becomes 0)
- L_m = ceil(m / log10(2)) ~ 3.32m: length of transition zone
- N_m: count of zeroless m-digit prefixes among 2^m, 2^{m+1}, ..., 2^{m+L_m-1}
