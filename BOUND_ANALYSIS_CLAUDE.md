# Bound Analysis: Attempting to Prove K ≤ 20

**Analyst**: Claude (working 3.2 prompt independently)
**Goal**: Prove explicit bound K such that for all p ≡ 1 (mod 4), Type I or Type II succeeds at some k ≤ K

---

## The Core Challenge

The reciprocity trap argument shows Type II "eventually" succeeds, but converting this to an explicit bound requires quantifying:

1. How many primes q ≡ 3 (mod 4) divide at least one m_k for k ≤ K?
2. For a given p, how many of these have (p/q) = -1?
3. When (p/q) = -1, does this guarantee G(n_k, m_k) > 0?

---

## Approach 1: Direct Prime Counting

### Setup

For k ≤ K, the values m_k = 4k + 3 range from 3 to 4K + 3.

**Claim**: Every prime q ≡ 3 (mod 4) with q ≤ 4K + 3 equals m_k for exactly one k ≤ K.

*Proof*: If q = 4k + 3, then k = (q - 3)/4. Since q ≡ 3 (mod 4), we have q - 3 ≡ 0 (mod 4), so k is an integer. And k ≤ K iff q ≤ 4K + 3. ∎

### Counting Primes

Let π₃(x) = |{primes q ≤ x : q ≡ 3 (mod 4)}|.

By Dirichlet's theorem with effective bounds (e.g., Rosser-Schoenfeld):

$$\pi_3(x) > \frac{x}{2\log x} \left(1 - \frac{1}{\log x}\right) \text{ for } x \geq 17$$

For K = 12: x = 4K + 3 = 51

The primes q ≡ 3 (mod 4) with q ≤ 51 are: 3, 7, 11, 19, 23, 31, 43, 47

That's **8 primes**.

### The Equidistribution Question

For a fixed prime p ≡ 1 (mod 4), how are the Legendre symbols (q/p) distributed?

By quadratic reciprocity, for q ≡ 3 (mod 4):
$$(p/q) = (q/p) \cdot (-1)^{(p-1)/2 \cdot (q-1)/2} = (q/p) \cdot (-1)^{(q-1)/2} = (q/p) \cdot (-1)$$

Wait, let me recalculate. For p ≡ 1 (mod 4) and q ≡ 3 (mod 4):
- (p-1)/2 is even
- (q-1)/2 is odd
- So (-1)^{(p-1)/2 · (q-1)/2} = (-1)^{even · odd} = (-1)^{even} = 1

Therefore: **(p/q) = (q/p)**

This is the key fact from 3.1.

### Distribution of (q/p)

For a fixed prime p, the values (q/p) for q ranging over odd primes are equidistributed between +1 and -1 (by Chebotarev density theorem applied to Q(√p)).

More precisely: as X → ∞,
$$|\{q \leq X : q \text{ prime}, (q/p) = -1\}| \sim \frac{\pi(X)}{2}$$

For X = 51, there are 15 odd primes ≤ 51. About 7-8 of them should have (q/p) = -1 for any given p.

But we only care about the 8 primes q ≡ 3 (mod 4) in this range. About 4 of them should have (q/p) = -1.

**The Problem**: "About 4" is a heuristic, not a guarantee. Could all 8 have (q/p) = +1 for some specific p?

---

## Approach 2: The 57 Dangerous Primes as Evidence

### What We Know

For p < 800,000, exactly 57 primes are "dangerous" (Type II fails at all k ≤ 5).

These 57 primes all have p being QR mod each of {3, 7, 11, 19, 23}.

But ALL 57 are rescued by k ≤ 12. The hardest case is p = 532249, rescued at k = 12.

### What Breaks the Trap?

For p = 532249, let's check which primes q ≡ 3 (mod 4) have (q/p) = -1:

Computing (q/532249) for small q ≡ 3 (mod 4):

Actually, I need to compute this. Since 532249 is QR mod {3, 7, 11, 19, 23}, we have:
- (3/532249) = +1
- (7/532249) = +1
- (11/532249) = +1
- (19/532249) = +1
- (23/532249) = +1

What about 31, 43, 47?

For 532249: checking computationally would tell us which of these is -1.

The rescue at k = 12 is via Type I (witness d = 31463), not Type II. So Type II might not succeed until k = 13.

This suggests the reciprocity breaking happens slowly for this p.

---

## Approach 3: Explicit Covering

### The Finite Structure

There are exactly 2970 "dangerous" residue classes mod L = 504,735.

For each class, we can identify the minimal rescue (k, mechanism).

**Computational claim** (verifiable): For all 2970 classes, rescue occurs by k ≤ 12.

If we can verify this computationally for all classes (not just primes < 800K), we have a proof.

### The Argument

**Theorem (Conditional)**: If the 2970 classes mod 504,735 are all rescued by k ≤ K, then ALL primes p ≡ 1 (mod 4) are rescued by k ≤ K.

*Proof sketch*:
- Any p ≡ 1 (mod 4) with Type II failing at k ≤ 5 lies in one of the 2970 classes
- If that class is rescued by k ≤ K, so is p
- If p is NOT in these classes, Type II already succeeded at some k ≤ 5 ∎

This reduces the infinite problem to a finite verification.

---

## Approach 4: The Pigeonhole via Larger Modulus

### Extending the Modulus

Let L' = lcm(m_0, m_1, ..., m_K) for K = 12.

L' = lcm(3, 7, 11, 15, 19, 23, 27, 31, 35, 39, 43, 47, 51)
   = lcm(3, 7, 11, 5, 19, 23, 31, 13, 43, 47, 17)
   = 3 × 5 × 7 × 11 × 13 × 17 × 19 × 23 × 31 × 43 × 47

This is a huge number (~10^14).

The "dangerous mod L'" classes (where Type II fails at ALL k ≤ 12) would be a much smaller set.

**Key Question**: Is this set empty? If so, K = 12 suffices.

### Heuristic Estimate

The probability of being QR mod all these primes is roughly:
$$\prod_{q \in S} \frac{1}{2} = \frac{1}{2^{|S|}}$$

For |S| = 11 primes (3, 5, 7, 11, 13, 17, 19, 23, 31, 43, 47... wait, 5 and 13 and 17 aren't ≡ 3 mod 4)

Actually, the QR condition mod composite m_k is more nuanced. Let me reconsider.

---

## Current Status: The Gap

### What We Can Prove

1. ✓ Type II cannot fail for ALL k (reciprocity argument)
2. ✓ The dangerous primes form a finite set of residue classes
3. ✓ Computationally, max k = 12 for p < 800K (and likely beyond)

### What We Cannot Yet Prove

1. ✗ An explicit formula for K in terms of p (or a universal K)
2. ✗ That the 2970 classes are ALL covered by k ≤ 12 (needs computation)
3. ✗ Why Type I succeeds as backup when Type II fails

### The Missing Ingredient

The gap is essentially: we don't have a theorem that says "if p is QR mod all of {q₁, ..., qₙ}, then p is NQR mod qₙ₊₁" for some structured sequence of primes.

The Chebotarev/equidistribution results give asymptotics, not absolute bounds for specific primes.

---

## Proposed Path Forward

### Option A: Computational Verification (Most Tractable)

1. Enumerate all 2970 classes mod 504,735
2. For each class, compute minimal rescue k (either Type I or Type II)
3. If max is ≤ K, we have a proof that K suffices

This is finite and automatable.

### Option B: Analytic Bound (More Elegant)

1. Prove that among primes q ≡ 3 (mod 4) with q ≤ 4K + 3, at least one has (q/p) = -1 for ANY p
2. This requires effective Chebotarev density bounds
3. Current best bounds (e.g., Lagarias-Odlyzko) may give K ~ O(log p), not a constant

### Option C: Structure of Type I (Alternative)

1. Prove that Type I alone succeeds by k ≤ K
2. This requires understanding when R_k = (Z/4kZ)* (full coverage)
3. The 2.4 analysis shows this happens for p = 532249 at k = 12

---

## Conclusion

**The bound K ≤ 12 is strongly supported but not yet proven.**

The most promising path is Option A: verify computationally that all 2970 residue classes are rescued by k ≤ 12. This would constitute a computer-assisted proof.

For a purely analytic proof, we would need sharper tools than currently available, or a clever algebraic insight connecting the QR conditions across different k values.

---

## Appendix: Key Computations Needed

1. For each of the 2970 classes mod 504,735, find minimal rescue k
2. Verify that max rescue k over all classes is ≤ 12
3. For the classes with max k, verify the rescue mechanism explicitly

This is the 3.3 prompt's task.
