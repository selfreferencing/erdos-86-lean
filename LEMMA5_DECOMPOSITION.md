# Lemma 5 Decomposition: Independence Across Moduli

## Date: January 21, 2025

## The Hard Lemma

**Lemma 5 (Independence)**: The 23 failure events F_k = {-1 ∉ B(x_k)} satisfy:
```
P(∩_k F_k) ≤ C · (log p)^{-A} for some A > 1
```

This seems hard because the x_k = n + k + 1 share structure. But let's decompose it.

---

## Micro-Step 1: Prime Divisibility Classification

**Fact**: A prime q divides x_k = n + k + 1 iff n ≡ -(k+1) (mod q).

**Consequence**:
- For q > 42: At most ONE k ∈ {0,1,...,41} has q | x_k
- For q ≤ 42: Potentially multiple k values share q

**Why this matters**: Large primes contribute independently to different x_k.

**Status**: Elementary number theory. ✓ TRIVIAL

---

## Micro-Step 2: Small Prime Enumeration

**Task**: List all primes q ≤ 42 and which k values they can divide.

| Prime q | Divides x_k when k ≡ ? (mod q) | # of k ∈ K_COMPLETE affected |
|---------|-------------------------------|------------------------------|
| 2 | k ≡ -1-n (mod 2) | ~11-12 |
| 3 | k ≡ -1-n (mod 3) | ~7-8 |
| 5 | k ≡ -1-n (mod 5) | ~4-5 |
| 7 | k ≡ -1-n (mod 7) | ~3-4 |
| 11 | k ≡ -1-n (mod 11) | ~2 |
| 13 | k ≡ -1-n (mod 13) | ~1-2 |
| 17 | k ≡ -1-n (mod 17) | ~1-2 |
| 19 | k ≡ -1-n (mod 19) | ~1 |
| 23 | k ≡ -1-n (mod 23) | ~1 |
| 29 | k ≡ -1-n (mod 29) | ~1 |
| 31 | k ≡ -1-n (mod 31) | ~1 |
| 37 | k ≡ -1-n (mod 37) | ~1 |
| 41 | k ≡ -1-n (mod 41) | ~1 |

**Key point**: Only primes 2, 3, 5, 7 can affect more than 2-3 k values.

**Status**: Direct computation. ✓ FINITE ENUMERATION

---

## Micro-Step 3: Separate Large and Small Prime Contributions

**Decomposition**: Write x_k = S_k · L_k where:
- S_k = product of prime factors ≤ 42
- L_k = product of prime factors > 42

**Key property**: For j ≠ k, gcd(L_j, L_k) = 1 (large primes don't overlap).

**Character decomposition**: For odd quadratic χ_k mod m_k:
```
χ_k(x_k) = χ_k(S_k) · χ_k(L_k)
```

**Status**: Multiplicativity of characters. ✓ TRIVIAL

---

## Micro-Step 4: Large Prime Independence

**Claim**: The values {χ_k(L_k) : k ∈ K_COMPLETE} are essentially independent random variables.

**Reasoning**:
- L_k has prime factors > 42, each appearing in exactly one x_j
- Different x_k have disjoint large prime factors
- The character values χ_k(q) for large primes q are equidistributed (Chebotarev)
- The characters χ_k for different moduli m_k are independent

**Formalization needed**:
- State precisely what "essentially independent" means
- Quantify the error from small prime correlations

**Status**: ⚠️ NEEDS PRECISE STATEMENT (but conceptually clear)

---

## Micro-Step 5: Small Prime Contribution Bound

**Question**: How much correlation do small primes introduce?

**Observation**: There are only 13 primes ≤ 42. Each contributes a factor to at most ~12 of the x_k values (for prime 2).

**Worst case**: All 23 characters see the same small prime factors.

**But**: Even if χ_k(S_k) = +1 for all k (small primes all split), we still need χ_k(L_k) = +1 for all k.

**The large prime part is still essentially independent!**

**Status**: ✓ CONCEPTUALLY CLEAR

---

## Micro-Step 6: Conditional Independence Formulation

**Key insight**: Condition on the small prime part.

**Statement**: For any fixed values of {χ_k(S_k) : k ∈ K_COMPLETE}:
```
P(χ_k(L_k) = +1 ∀k | small prime values) ≈ ∏_k P(χ_k(L_k) = +1)
```

**Why this is (almost) true**:
- L_k values have disjoint prime support for k ≠ j
- Characters χ_k act independently on disjoint primes
- The only correlation is through the constraint that ∏ L_k = ∏ x_k / ∏ S_k

**This correlation is weak**: The L_k values aren't constrained to have any particular relationship.

**Status**: ⚠️ NEEDS CAREFUL FORMULATION

---

## Micro-Step 7: Failure Probability for Large Part

**For a single k**:
```
P(χ_k(L_k) = +1) = P(all large prime factors of x_k split in χ_k)
```

**Using Selberg-Delange**: If L_k has ω(L_k) large prime factors:
```
P(χ_k(L_k) = +1) ≈ 2^{-ω(L_k)}
```

**Typical ω(L_k)**: Since x_k ~ p/4, and most prime factors are large:
```
ω(L_k) ≈ ω(x_k) - O(1) ≈ log log p - O(1)
```

**So**:
```
P(χ_k(L_k) = +1) ≈ 2^{-log log p} = (log p)^{-log 2} ≈ (log p)^{-0.69}
```

**Status**: ✓ STANDARD ESTIMATE

---

## Micro-Step 8: Product Over k

**Under conditional independence**:
```
P(χ_k(L_k) = +1 ∀k) ≈ ∏_k (log p)^{-0.69} = (log p)^{-0.69 × 23} = (log p)^{-15.9}
```

**Even accounting for small prime correlations**: The exponent is still large.

**Key point**: We don't need exact independence; we just need the exponent to exceed 1 for Borel-Cantelli.

**Status**: ✓ HEURISTIC COMPLETE

---

## Micro-Step 9: Rigorous Statement

**Theorem (Target)**:
```
#{p ≤ X : p ≡ 1 (mod 4), F_k ∀k} ≤ C · X / (log X)^{A}
```
for some A > 1.

**Proof sketch**:
1. Decompose x_k = S_k · L_k (small × large primes)
2. Condition on small prime contributions
3. Use independence of large prime contributions
4. Apply Selberg-Delange to each L_k
5. Multiply (with correction for conditioning)

**What's needed to make rigorous**:
- Explicit error bounds in Selberg-Delange
- Quantification of conditioning effect
- Uniformity over k values

**Status**: ⚠️ CLEAR PATH, NEEDS EXECUTION

---

## Micro-Step 10: The Explicit Computation Alternative

**Alternative approach**: Instead of probabilistic bounds, directly verify.

**For each residue class r (mod M)** where M = lcm(m_k):
- Check: Does some k ∈ K_COMPLETE have a witness?

**This is finite**: |M| is large but computable.

**But**: M = lcm(3,7,11,...,167) is astronomically large (~10^{30}).

**Reduction**: Use CRT structure to factor the verification.

**Status**: ⚠️ POTENTIALLY TRACTABLE VIA CRT

---

## Summary: Decomposition Status

| Micro-Step | Content | Status |
|------------|---------|--------|
| 1 | Prime divisibility classification | ✓ Trivial |
| 2 | Small prime enumeration | ✓ Finite computation |
| 3 | Large/small decomposition | ✓ Trivial |
| 4 | Large prime independence | ⚠️ Needs precise statement |
| 5 | Small prime bound | ✓ Conceptually clear |
| 6 | Conditional independence | ⚠️ Key technical step |
| 7 | Single-k large part estimate | ✓ Standard |
| 8 | Product over k | ✓ Follows from 6-7 |
| 9 | Rigorous theorem | ⚠️ Assembly needed |
| 10 | Explicit alternative | ⚠️ CRT reduction needed |

---

## The Remaining Hard Work

The decomposition reveals that **Micro-Step 6** (conditional independence formulation) is the crux.

**Precise question for GPT**:

> Given that L_j and L_k have disjoint prime support for j ≠ k, and χ_j, χ_k are independent characters on independent moduli, how do we rigorously establish that:
> ```
> P(χ_j(L_j) = +1 AND χ_k(L_k) = +1) ≈ P(χ_j(L_j) = +1) × P(χ_k(L_k) = +1)
> ```
> with quantifiable error?

This is now a much more focused question than the original Lemma 5.

---

## New Micro-Prompts

**Micro-Prompt 6a**: Precise statement of conditional independence for characters on disjoint support

**Micro-Prompt 6b**: Error bounds when conditioning on small primes

**Micro-Prompt 9**: Assembly of micro-steps into rigorous theorem

**Micro-Prompt 10**: CRT reduction for explicit verification
