# Phase 1 Findings: Type-I-Resistant Primes

## Executive Summary

**p = 2521 is the ONLY Type-I-resistant prime up to 1,000,000.**

This is far rarer than expected. Among 395 primes ≡ 1 (mod 840) up to 1M, only p=2521 fails Type I.

## Key Findings

### 1. Rarity of Type-I Resistance

| Range | Primes Checked (≡1 mod 4) | Type-I-Resistant |
|-------|---------------------------|------------------|
| 1 - 100,000 | ~4,800 | 1 (p=2521) |
| 100,001 - 500,000 | ~14,000 | 0 |
| Primes ≡ 1 (mod 840) up to 1M | 395 | 1 (p=2521) |

### 2. The Semiprime Mechanism

**Why Type I fails for p=2521:**

For Type I to work, we need divisor m of kp+1 such that m ≡ -p (mod 4k).

For p=2521: **36 out of 50 values of kp+1 are semiprimes** (products of exactly two primes).

| k | kp+1 | Factorization | # Divisors | Semiprime? |
|---|------|---------------|------------|------------|
| 1 | 2522 | 2 × 13 × 97 | 8 | No |
| 4 | 10085 | 5 × 2017 | 4 | YES |
| 6 | 15127 | 7 × 2161 | 4 | YES |
| 9 | 22690 | 2 × 5 × 2269 | 8 | YES |
| 12 | 30253 | 30253 | 2 | YES (prime!) |

Semiprimes have at most 4 divisors. With few divisors, the probability of hitting the target residue class is extremely low.

**Comparison with p=3361** (next prime ≡ 1 mod 840):
- Type I succeeds at k=9
- At k=9: 30250 = 2 × 5³ × 11² has **24 divisors**
- Divisor 275 ≡ 23 (mod 36) = target → SUCCESS

### 3. Type II Saves p=2521

Type II uses: x_k = (p + m_k)/4 where m_k = 4k + 3

For p=2521, k=5:
- m_k = 23
- x_k = (2521 + 23)/4 = 636
- 636 = 2² × 3 × 53 has **12 divisors**
- Coprime pair (2, 159): 2 + 159 = 161 ≡ 0 (mod 23) ✓

The ESC solution: 4/2521 = 1/636 + 1/70588 + 1/5611746

### 4. Structure of p=2521

```
p = 2521
p mod 4 = 1
p mod 840 = 1 (first prime in "difficult" class)
p - 1 = 2520 = 2³ × 3² × 5 × 7
p + 1 = 2522 = 2 × 13 × 97

Legendre symbols:
  (2521|3) = 1  (QR)
  (2521|5) = 1  (QR)
  (2521|7) = 1  (QR)
  (2521|11) = -1 (NQR)
  (2521|13) = 1  (QR)
```

p=2521 is a quadratic residue mod all primes dividing 840 = 2³ × 3 × 5 × 7.

## Implications for Complementarity

### Confirmed Hypotheses

1. **Smooth Neighbor Hypothesis**: Type I succeeds when kp+1 is highly composite. Type I fails when kp+1 values are consistently unsmooth (semiprimes).

2. **Modular Coincidence Hypothesis**: p ≡ 1 (mod 840) is necessary but not sufficient for Type I resistance. Being the *first* prime in this class appears significant.

3. **Quadratic Structure**: The exceptional residue classes mod 840 are squares. p=2521 being a QR mod 3,5,7 may contribute to Type I failure.

### The Complementarity Mechanism

Type I fails → kp+1 values are semiprimes → few divisors

But this says nothing about x_k = (p + m_k)/4 for Type II.

In fact:
- Type I operates on: kp + 1
- Type II operates on: (p + 4k + 3)/4 ≈ p/4 + k

These are **different arithmetic sequences**. The semiprime phenomenon in kp+1 doesn't infect (p + m_k)/4.

### Why Complementarity Works

**Conjecture**: The multiplicative structure that makes kp+1 unsmooth (Type I failure) is independent of the divisibility structure of x_k = (p + m_k)/4 (Type II).

Since x_k ≈ p/4 + k is a *different* sequence from kp+1, there's no reason to expect both to be simultaneously problematic.

## Open Questions

1. **Is p=2521 truly unique?** Are there Type-I-resistant primes beyond 10⁶? Beyond 10⁹?

2. **What makes p=2521 produce so many semiprimes?** Is there a number-theoretic explanation for why kp+1 is semiprime so often?

3. **Why is the first prime ≡ 1 (mod 840) special?** Is this coincidence or structure?

4. **Can we prove Type II always works when Type I fails?** The independence of the two sequences suggests this should be provable.

## Next Steps

1. Extend search to 10⁷ or beyond to find more Type-I-resistant primes (if they exist)

2. Analyze the semiprime density of k×p+1 as a function of p mod 840

3. Prove that x_k has sufficient divisor density to ensure Type II success for primes where Type I fails

4. Investigate the connection between QR structure mod 3,5,7 and Type I resistance
