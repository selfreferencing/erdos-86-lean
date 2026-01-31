# Prompt 65: Formalize Route C1 with k ≤ 15 Bound

## Context

From prompts 62-63, we established:

1. **Route C1 approach:** For hard primes p, find x = ⌈p/4⌉ + k with small k such that x² has a divisor e satisfying (4x-p) | (4e+1)

2. **k ≤ 7 works for 98.8%** of hard primes tested (247/250)

3. **k ≤ 15 covers ALL observed cases** including the three outliers

4. **The moduli for k ≤ 15:** m = 3+4k gives m ∈ {3, 7, 11, 15, 19, 23, 27, 31, 35, 39, 43, 47, 51, 55, 59, 63}

## Request: Formalize Route C1 with k ≤ 15

### Part 1: The Finite Modulus Covering Conjecture

State precisely:

**Conjecture (Route C1, k ≤ 15):** For every prime p in the 6 hard classes mod 840, there exists k ∈ {0, 1, ..., 15} such that x_k = ⌈p/4⌉ + k has a divisor e | x_k² satisfying:

(3 + 4k) | (4e + 1)

### Part 2: Required Residue Classes

For each m ∈ {3, 7, 11, 15, 19, 23, 27, 31, 35, 39, 43, 47, 51, 55, 59, 63}:

1. Compute the required residue: e ≡ -4⁻¹ (mod m)
2. Factor m and describe the structure of (Z/mZ)×
3. Identify which residue classes of prime factors would generate the required class

### Part 3: The x_k Structure by Class

For each of the 6 hard classes mod 840:

| Class | x₀ (mod 210) | x_k = x₀ + k (mod 210) for k = 0,...,15 |
|-------|--------------|----------------------------------------|

Identify which k values guarantee small prime factors (2, 3, 5, 7) in x_k.

### Part 4: Lemma Sequence

Break the conjecture into provable lemmas:

**Lemma 1 (Residue coverage):** For each m ≤ 63, characterize which multiplicative subgroups of (Z/mZ)× contain -4⁻¹ (mod m).

**Lemma 2 (Factor availability):** For each hard class and each k ≤ 15, determine which small primes divide x_k.

**Lemma 3 (Subgroup generation):** Show that for each hard prime p, at least one k ≤ 15 gives x_k whose prime factors generate a subgroup containing the required residue.

### Part 5: Proof Strategy

Outline how to prove the conjecture:

1. **Covering argument:** Show the 16 conditions (one per k) collectively cover all possibilities
2. **CRT structure:** Use the factorizations of the moduli m
3. **Density/sieve:** If needed, show exceptions have density 0

### Part 6: Computational Verification Plan

If a full proof is difficult:

1. What bound B would suffice to verify computationally?
2. How would we certify "no prime p < B in hard classes needs k > 15"?
3. Combined with an asymptotic argument, could this give a complete proof?

### Part 7: Comparison to Original ES Approaches

How does Route C1 (k ≤ 15) compare to:
1. The ED2/Dyachenko approach (requires small QR prime)
2. The Mordell/modular identity approach (covers 31/32 of primes)
3. Direct Bradford without the finite-k restriction

Is Route C1 genuinely new, or a repackaging of known methods?

## Goal

Produce a concrete proof roadmap for:

**Theorem:** For all primes p > p₀ (explicit), the Erdős-Straus equation 4/p = 1/x + 1/y + 1/z has a solution.

With Route C1 (k ≤ 15) handling the hard classes and modular identities handling the rest.
