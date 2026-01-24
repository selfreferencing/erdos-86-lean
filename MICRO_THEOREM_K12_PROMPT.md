# Micro-Theorem Prompt: The k ∈ {1,...,5} Rescue

## Context

This is part of a proof of the Erdős-Straus Conjecture for primes p ≡ 1 (mod 4).

**Setup**: For prime p ≡ 1 (mod 4) and integer k ≥ 0, define:
- n_k = (p + 4k + 3) / 4
- m_k = 4k + 3
- G(n, m) = number of coprime divisor pairs (a, b) of n with a + b ≡ 0 (mod m), divided by 2

**Known**: If G(n_k, m_k) ≥ 1 for some k, the ESC has a solution for p (Bradford 2025).

## What's Already Proven

1. **For p ≡ 5 (mod 12)**: k = 0 always works (G(n_0, 3) ≥ 1).

2. **For p ≡ 1 (mod 12)**: k = 0 sometimes works, sometimes fails.

3. **Computationally verified to 10^7**: For ALL primes p ≡ 1 (mod 4), some k ≤ 5 works.

## The Micro-Theorem to Prove

**Statement**: For every prime p ≡ 1 (mod 12) satisfying BOTH:
- (C1) (p+1)/2 has all prime factors ≡ 1 (mod 4)
- (C2) G((p+3)/4, 3) = 0

there exists k ∈ {1, 2, 3, 4, 5} such that G(n_k, m_k) ≥ 1.

## Key Observations About the Hypothesis

### When Does (C2) Hold?

For k = 0: m_0 = 3, n_0 = (p+3)/4.

G(n_0, 3) = 0 happens when n_0 has no coprime divisor pair summing to 0 (mod 3).

**Structural analysis** (for p ≡ 1 mod 12):
- n_0 ≡ 1 (mod 3) always

The 49 cases (up to 10^4) where (C1) and (C2) both hold have n_0 of these types:
- n_0 prime: 30 cases (e.g., p=73 gives n_0=19)
- n_0 = q² for q ≡ 1 (mod 3): 4 cases (e.g., p=193 gives n_0=49=7²)
- n_0 = qr semiprime with q+r ≢ 0 (mod 3): 14 cases
- Other: 1 case

### The Hardest Cases

Only 2 primes require k = 5:
- **p = 1201**: n_0 = 301 = 7·43 (semiprime), rescued at k=5 by n_5 = 306 = 2·3²·17
- **p = 2521**: n_0 = 631 (prime), rescued at k=5 by n_5 = 636 = 2²·3·53

## Observations About What k Values Do

| k | m_k | Key property |
|---|-----|--------------|
| 1 | 7 | Works if n_1 has divisors a, b with a+b ≡ 0 (mod 7) |
| 2 | 11 | Works if n_2 has divisors a, b with a+b ≡ 0 (mod 11) |
| 3 | 15 = 3·5 | Composite modulus, more flexible |
| 4 | 19 | Prime modulus |
| 5 | 23 | Prime modulus |

Note: n_{k+1} = n_k + 1 always.

## The Consecutive Integer Structure

The key insight is that n_0, n_1, ..., n_5 are **6 consecutive integers**.

If n_0 has constrained divisor structure (prime, prime power, or bad semiprime), then n_1, n_2, ..., n_5 provide "rescue" opportunities through:
1. Different prime factorizations
2. Different divisor sets
3. Different modular conditions

## Questions for Analysis

1. **Why does k ≤ 5 always suffice?** Is there a covering argument?

2. **Is there structure in which k rescues which primes?**
   - k=1 rescues most (~80%)
   - k=2 rescues some of the rest
   - k=5 only needed for p ∈ {1201, 2521}

3. **Can we show the 6 consecutive integers n_0, ..., n_5 always have at least one "good" member?**

4. **What makes p = 1201 and p = 2521 so resistant?**
   - p = 1201: factors are 601 (prime), n_0 = 301 = 7·43
   - p = 2521: factors are 13·97, n_0 = 631 (prime)

## Goal

Prove: At least one of n_1, n_2, n_3, n_4, n_5 satisfies G(n_k, m_k) ≥ 1, given that n_0 fails.

This would complete the ESC proof for all primes p ≡ 1 (mod 4).
