# DECISIVE QUESTION: Does Bradford's Obstruction Imply Principal Genus?

## IMPORTANT: Mordell-Hard Restriction is NECESSARY

GPT instance 7 found a counterexample to the general theorem:
- p = 2,158,069 (prime, but NOT Mordell-hard: p mod 840 = 109)
- ALL 18 odd prime factors of S have (p/q) = +1
- So the covering property FAILS for this p

This confirms: **The theorem is FALSE for general primes. The Mordell-hard restriction is essential.**

The theorem we need to prove is specifically for Mordell-hard primes.

## Context (Established Facts)

We are proving the Erdős-Straus conjecture for Mordell-hard primes via Bradford Type II decompositions with K₁₀ = {5,7,9,11,14,17,19,23,26,29}.

**Definitions:**
- x_k = (p + m_k)/4 where m_k = 4k + 3
- r = (p + 3)/4, so x_k = r + k
- χ_k(n) = (n/m_k) is the Jacobi symbol

**The Bradford Obstruction (O_k):**
The obstruction at k holds iff every odd prime q | x_k satisfies χ_k(q) = +1.

**Verified Equivalences:**
1. Via quadratic reciprocity: If q | x_k and χ_k(q) = +1, then (p/q) = +1
2. So O_k holds ⟺ every prime factor of x_k splits in Q(√p)
3. "All 10 obstructions hold" ⟺ r mod ℓ ∉ G_ℓ for every prime ℓ

**The Gap:**
- Sieve methods show the exceptional set has density zero
- But density zero ≠ empty
- For finiteness/emptiness, we need RIGIDITY

## The Decisive Question

**Two candidate rigidity mechanisms have been identified:**

### Mechanism 1: Genus Rigidity (Diophantine)

If "all prime factors of x_k split in Q(√(-m_k))" implies "x_k is a norm from Q(√(-m_k))", then:
- x_k = a² + m_k·b² (or similar quadratic form depending on discriminant)
- 10 simultaneous quadratic form constraints on the same r
- Fiber product has genus ≥ 2 for 3-4 constraints
- Faltings ⟹ finitely many solutions

**KEY QUESTION 1:** Does the Bradford obstruction O_k (all prime factors in ker(χ_k)) actually force x_k into the **principal genus** of the form class group for discriminant -4m_k?

Specifically:
- The obstruction says: x_k is supported only on primes q with (q/m_k) = +1
- Does this imply: x_k is representable by the principal form of discriminant -4m_k?
- Or can x_k be in a non-principal genus while still having all-split factorization?

If YES (principal genus forced): The Diophantine approach works. Exhibit the explicit quadratic form equations.

If NO: We need Mechanism 2.

### Mechanism 2: Primitive Divisor Forcing

Construct F(r) from the shifts {r+5, r+7, ..., r+29} such that:
1. For large r, F(r) has a primitive prime divisor ℓ (Zsigmondy-type)
2. The Frobenius of ℓ in the compositum of Q(√(-m_k)) forces χ_k(ℓ) = -1 for some k
3. And ℓ | x_k for that same k

This gives a deterministic witness, not probabilistic.

**KEY QUESTION 2:** If Mechanism 1 fails, can you construct such an F(r)?

Candidates:
- Products: ∏(r+k) for subsets of K₁₀
- Resultants or discriminants of polynomials in r
- Lucas sequences evaluated at r

## What We Need From You

1. **Resolve Question 1 definitively.** Either:
   - PROVE that O_k implies x_k is in the principal genus (giving the norm equation), OR
   - Give a COUNTEREXAMPLE: an integer n with all prime factors in ker(χ_k) but n not representable by the principal form

2. **If Q1 is YES:** Write out the explicit system of 3-4 quadratic form equations and verify the fiber product has genus ≥ 2.

3. **If Q1 is NO:** Propose a concrete F(r) for Mechanism 2 and prove it has the required properties.

## Relevant Data

**The m_k values:**
| k | m_k | Factorization | -4m_k | h(-4m_k) |
|---|-----|---------------|-------|----------|
| 5 | 23 | prime | -92 | 6 |
| 7 | 31 | prime | -124 | 6 |
| 9 | 39 | 3×13 | -156 | 8 |
| 11 | 47 | prime | -188 | 6 |
| 14 | 59 | prime | -236 | 6 |
| 17 | 71 | prime | -284 | 8 |
| 19 | 79 | prime | -316 | 10 |
| 23 | 95 | 5×19 | -380 | 8 |
| 26 | 107 | prime | -428 | 6 |
| 29 | 119 | 7×17 | -476 | 10 |

All class numbers h(-4m_k) > 1, so there ARE non-principal genera.

**The obstruction condition restated:**
- x_k has no prime factor q with (q/m_k) = -1
- Equivalently: x_k is supported only on primes that split in Q(√(-m_k))

**Does this force x_k into the principal genus?**

## Deadline Pressure

This is the ONLY remaining gap in a complete proof of Erdős-Straus for Mordell-hard primes. We have:
- ✓ Computational verification for p ≤ 10^7
- ✓ The reciprocity transformation
- ✓ The G_ℓ framework showing interaction
- ✗ Rigidity argument for emptiness/finiteness

Resolve the genus question and we're done.
