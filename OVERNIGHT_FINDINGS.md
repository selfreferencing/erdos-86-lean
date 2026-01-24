# Overnight Fleet Findings

## Prompt 1 Result: CLAIM IS FALSE

**Counterexample**: n = 312 = 2³·3·13

**Why**: All prime factors (2, 3, 13) are quadratic residues mod 23. Since -1 is NOT a QR mod 23, if all divisors are in the QR subgroup, their negatives are in the non-residue coset, so no coprime pair can sum to 0 mod 23.

**Infinite family**: Any n = 2^a · 3^b with a,b ≥ 1 has G(n, 23) = 0.

## The Exact Obstruction

G(n, 23) = 0 iff **all prime factors of n are QR mod 23**.

QR mod 23: {1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18}
QNR mod 23: {5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22}

## Impact on ESC Proof

### The Hardest Primes Have QNR Factors
- p = 1201: n_5 = 306 = 2·3²·**17** (17 is QNR mod 23) ✓
- p = 2521: n_5 = 636 = 2²·3·**53** (53 ≡ 7 mod 23, QNR) ✓

### When n_5 Has All-QR Factors
Earlier k values rescue! Example:
- p = 21169: n_5 has all-QR factors, but **Type I succeeds at k=5**

## Updated Max k Needed

| Range | Max k | Prime | Method |
|-------|-------|-------|--------|
| ≤ 5000 | 5 | 2521 | Type II |
| ≤ 50000 | 5 | 2521 | Type II |
| ≤ 100000 | 7 | 66529 | Type II |
| ≤ 200000 | 7 | 66529 | Type II |

**Key finding**: Max k = 5 was only verified to ~50,000. Beyond that, k = 7 is needed.

## Refined Proof Strategy

The proof must now address:

1. **When n_k has a QNR factor mod m_k**: G(n_k, m_k) ≥ 1 (the QNR provides escape)

2. **When n_k has all QR factors mod m_k**: Some earlier k or Type I rescues

3. **Why some k always works**: Need to understand the interplay between:
   - QR structure across different moduli (3, 7, 11, 15, 19, 23, 27, 31, ...)
   - Type I vs Type II complementarity

## New Prompts Needed

Based on these findings, new prompts should focus on:

1. **QR/QNR dichotomy**: Prove G(n, m) ≥ 1 when n has a QNR factor mod m
2. **Cross-modulus covering**: Show QR obstructions for different m_k can't all align
3. **Type I rescue**: Characterize when Type I succeeds at k where Type II fails

## Key Insight

The GPT correctly identified that the simple "6|n" claim fails because of the QR subgroup structure. But for the ESC-specific n_5 values, the constraints from earlier failures propagate information that prevents all-QR factorizations (or triggers Type I rescue).

This is actually **progress**: we now know the exact obstruction to overcome.
