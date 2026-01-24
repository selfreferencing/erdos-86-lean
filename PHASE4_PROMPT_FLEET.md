# Phase 4 Prompt Fleet: Existence Proof Strategy

## Date: January 21, 2025

## Context for All Prompts

We have established:
1. **D_max grows as O(√p)** - no finite certificate exists
2. **K_COMPLETE empirically covers 100%** of tested primes (179,468 up to 10^8)
3. **Resistant classes = G² ⊆ (ℤ/840ℤ)*** - the square subgroup
4. **Certificate = decision tree on quadratic characters**
5. **Salez filters**: S_11, S_23, S*_55, S*_77 explain the structure

**New Goal**: Prove existence of witness for some k ∈ K_COMPLETE (unbounded d)

---

## Prompt 37: Core Existence Proof

```
EXISTENCE PROOF FOR ESC TYPE II WITNESSES

We need to prove: For every prime p ≡ 1 (mod 4), there exists k ∈ K_COMPLETE and d ∈ ℕ such that:
1. d | x_k² where x_k = (p + m_k)/4
2. d ≡ -x_k (mod m_k)
3. gcd(x_k, m_k) = 1

where:
- K_COMPLETE = {0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41}
- m_k = 4k + 3
- Moduli: 3, 7, 11, 15, 19, 23, 27, 31, 39, 47, 55, 59, 67, 71, 79, 87, 95, 103, 107, 119, 127, 159, 167

GROUP-THEORETIC REFORMULATION:
For each admissible k, define H_{x_k} = ⟨q mod m_k : q prime, q | x_k⟩ ⊆ (ℤ/m_k ℤ)*

A witness exists iff -x_k ∈ H_{x_k} for some k ∈ K_COMPLETE.

KEY QUESTION: Why do the 23 moduli m_k ensure at least one "hit"?

EMPIRICAL DATA:
- 179,468 Mordell-hard primes tested up to 10^8
- 100% coverage
- D_max = 37,281 (grows as O(√p))

OBSERVATIONS:
1. The 6 resistant classes mod 840 are exactly G² (square subgroup)
2. Our m_k values include composite cross-filters: 55 = 5×11, 77 = 7×11
3. For hard cases, d/√p ratio is ~2-4

Can you prove (or give a conditional argument for) why K_COMPLETE suffices?
```

---

## Prompt 38: Map (k,d) Rules to Salez Types

```
MAPPING OUR (k,d) WITNESSES TO SALEZ'S MODULAR EQUATION TYPES

Our Type II witness rule:
- For prime p ≡ 1 (mod 4)
- Choose k ∈ K_COMPLETE with m_k = 4k + 3
- Compute x_k = (p + m_k)/4
- Require: gcd(x_k, m_k) = 1 (admissibility)
- Find d such that: d | x_k² AND d ≡ -x_k (mod m_k)

This gives an ESC solution:
4/p = 1/x_k + 1/(x_k·m_k) + 1/(x_k·m_k·d)

Salez (arXiv:1406.6307) classifies 7 modular equation types (14a-15d) for constant-coefficient identities.

QUESTIONS:
1. Which Salez type(s) does our (k,d) rule correspond to?
2. Is our rule equivalent to his (14a) family with m = 4k+3?
3. Why do composite moduli (55, 77) appear - is this the cross-filter phenomenon?
4. Salez's S_23 = {0,7,10,11,15,17,19,20,21,22} comes from BCD=6 in (14a). Does our k=5 (m_k=23) match this?

The mapping would help us understand:
- Whether K_COMPLETE is minimal
- Whether additional k values would help
- How to prove completeness using Salez's framework
```

---

## Prompt 39: O(√p) Bound on D_max

```
PROVING D_max = O(√p) FOR TYPE II WITNESSES

Our empirical data shows D_max grows roughly as O(√p) with coefficient ~2-4:

| Prime p | Min d | d/√p |
|---------|-------|------|
| 2,521 | 8 | 0.16 |
| 3,361 | 29 | 0.50 |
| 196,561 | 1,922 | 4.34 |
| 8,628,481 | 2,367 | 0.81 |
| 30,573,481 | 12,388 | 2.24 |
| 72,077,041 | 16,129 | 1.90 |
| 76,719,889 | 37,281 | 4.26 |

SETUP:
- x_k = (p + m_k)/4 ≈ p/4
- d | x_k²
- d ≡ -x_k (mod m_k)
- Trivial bound: d ≤ x_k² ≈ p²/16

QUESTION: Can we prove d = O(√p) or d = O(p^ε) for some ε < 1?

POSSIBLE APPROACHES:
1. Analytic number theory: smallest divisor in a residue class
2. Smooth number arguments: if x_k is smooth, small d exists
3. Character sum bounds: probability that -x_k ∈ H_{x_k}

The hard cases seem to occur when:
- x_k has few small prime factors
- No small product of prime powers ≡ -x_k (mod m_k)

Example: p = 76,719,889, x_5 = 19,179,978 = 2 × 3 × 17 × 43 × 4373
Smallest matching divisor: d = 3 × 17² × 43 = 37,281

Can you prove or conjecture a bound on d in terms of p?
```

---

## Prompt 40: Character Sum Approach

```
CHARACTER SUM APPROACH TO ESC COVERAGE

For each k ∈ K_COMPLETE with m_k = 4k + 3:
- x_k = (p + m_k)/4
- H_{x_k} = ⟨prime factors of x_k⟩ ⊆ (ℤ/m_k)*
- Witness exists iff -x_k ∈ H_{x_k}

QUESTION: Can we bound the probability (over p) that -x_k ∉ H_{x_k} for ALL k simultaneously?

SETUP:
- Let ω(x_k) = number of distinct prime factors of x_k
- H_{x_k} has size at least 2^{ω(x_k)-1} (generically)
- (ℤ/m_k)* has size φ(m_k)

HEURISTIC:
If prime factors of x_k are "random" mod m_k, then:
P(-x_k ∉ H_{x_k}) ≈ 1 - |H_{x_k}|/φ(m_k)

For the 23 moduli to all fail simultaneously:
P(all fail) ≈ ∏_k (1 - |H_{x_k}|/φ(m_k))

This should be very small if x_k values have many prime factors.

QUESTIONS:
1. Can character sums bound ∑_k 𝟙[-x_k ∉ H_{x_k}]?
2. Is there a result like "for ω(x) ≥ c log log p, coverage is guaranteed"?
3. How does the quadratic character obstruction (resistant = G²) interact with this?

The key insight: we're not trying to bound d, just prove existence for SOME k.
```

---

## Summary

| Prompt | Goal | Key Question |
|--------|------|--------------|
| 37 | Core existence proof | Why does K_COMPLETE suffice? |
| 38 | Salez mapping | Which equation types are we using? |
| 39 | Growth bound | Can we prove d = O(√p)? |
| 40 | Probabilistic | Character sum bounds on failure probability? |

## Recommended Order

1. **Prompt 37** - Most important, direct attack on main question
2. **Prompt 38** - Connects our work to established literature
3. **Prompt 39** - Secondary but useful for understanding
4. **Prompt 40** - Advanced, may require specialized knowledge

You can send all 4 in parallel or start with 37 and 38.
