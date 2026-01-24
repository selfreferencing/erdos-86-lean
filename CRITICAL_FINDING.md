# CRITICAL FINDING: D_max Grows with p

## Date: January 21, 2025

## Summary

The maximum witness bound D_max appears to **grow unboundedly** as we scan larger primes. This fundamentally changes the proof strategy.

## Data Points

| Prime p | Min Witness d | k | d/√p |
|---------|---------------|---|------|
| 2,521 | 8 | 5 | 0.16 |
| 3,361 | 29 | 0 | 0.50 |
| 196,561 | 1,922 | 25 | 4.34 |
| 8,628,481 | 2,367 | 5 | 0.81 |
| 30,573,481 | 12,388 | 25 | 2.24 |
| 72,077,041 | 16,129 | 7 | 1.90 |
| 76,719,889 | 37,281 | 5 | 4.26 |

**Trend:** d_max appears to be O(√p) with coefficient ~2-4 in worst cases

## Analysis of p = 30,573,481

- p ≡ 1 (mod 840) - Mordell-hard class
- Best witness: k = 25, m_k = 103
- x_k = (p + 103)/4 = 7,643,396
- x_k = 2² × 19 × 163 × 617 (only 4 distinct primes)
- x_k² has 135 divisors
- Target: d ≡ -x_k ≡ 28 (mod 103)
- Smallest matching divisor: d = 12,388 = 4 × 19 × 163

**Why so large?** The factorization of x_k has few small primes, and none of the small combinations give residue 28 mod 103.

## Implications for Proof Strategy

### ❌ Finite CRT Certificate Approach Does NOT Work

If D_max grows with p, we cannot enumerate a finite set of CRT rules that covers all primes. The "certificate" would be infinite.

### ✅ What DOES Work: K_COMPLETE Always Covers

The key observation is that K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41] always provides a witness - the witness just might be arbitrarily large.

### The Correct Proof Statement

**Theorem (if true):** For every prime p ≡ 1 (mod 4), there exists k ∈ K_COMPLETE and d ∈ ℕ such that:
1. d | x_k² where x_k = (p + m_k)/4
2. d ≡ -x_k (mod m_k)
3. gcd(x_k, m_k) = 1

This is an **existence theorem**, not a bounded certificate. The proof should show that for at least one k ∈ K_COMPLETE, the congruence d ≡ -x_k (mod m_k) has a solution among divisors of x_k².

## Revised Proof Approach

### Key Question
For fixed k, when does x_k² have a divisor d ≡ -x_k (mod m_k)?

### Sufficient Conditions
If x_k has a prime factor q such that:
- q ≡ -x_k (mod m_k), OR
- q² | x_k and q ≡ r where r² ≡ -x_k (mod m_k), OR
- Product of some prime powers of x_k ≡ -x_k (mod m_k)

Then d exists.

### Role of K_COMPLETE
K_COMPLETE provides 23 different moduli m_k. For any x, at least one m_k should "hit" the factorization structure of x to produce a valid witness.

The conjecture is: **The 23 moduli in {m_k : k ∈ K_COMPLETE} are "dense enough" in a quadratic residue sense to ensure coverage.**

## Prompts for GPT

### Prompt 37: Existence Proof
```
Given K_COMPLETE with m_k = 4k + 3 for k ∈ K_COMPLETE, prove:

For every prime p ≡ 1 (mod 4), there exists k ∈ K_COMPLETE such that x_k² has a divisor d ≡ -x_k (mod m_k), where x_k = (p + m_k)/4.

Note: d is NOT bounded. We just need to prove existence for at least one k.

Observations:
- gcd(x_k, m_k) = 1 (admissibility condition)
- d | x_k² means d is a product of prime powers from factorization of x_k
- We need some combination of these prime powers to equal -x_k mod m_k

The question reduces to: why do the 23 moduli m_k ensure at least one "hits"?
```

### Prompt 38: Quadratic Residue Analysis
```
Consider the set M = {3, 7, 11, 15, 23, ...} (m_k values from K_COMPLETE).

For a given integer x coprime to all m ∈ M, we want:
∃ m ∈ M such that x² has a divisor d ≡ -x (mod m)

This is related to quadratic residues. For each prime p | x, the set of possible residues {p^i mod m : i ≥ 0} generates a subgroup of (ℤ/mℤ)*.

The question: why do the specific m values in M ensure coverage?
```

## Files to Resume

- `scan_max_witness.py` - Running scan (check status)
- `max_witness_scan_100000000.txt` - Results file
- `SESSION_STATE_JAN21.md` - Full session state
- `PROOF_STRATEGY_UPDATE.md` - Earlier strategy (now updated)

## Scan Status

Process running: PID 61930
Check with: `tail -f /Users/kvallie2/Desktop/esc_stage8/max_witness_scan_100000000.txt`
