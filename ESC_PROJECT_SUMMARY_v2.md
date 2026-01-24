# Erdős-Straus Conjecture: Project Summary v2

**Date**: January 2026
**Status**: Correct approach identified, one lemma remains

---

## The Conjecture

**Erdős-Straus Conjecture (ESC)**: For every integer n ≥ 2, the equation
$$\frac{4}{n} = \frac{1}{x} + \frac{1}{y} + \frac{1}{z}$$
has a solution in positive integers x, y, z.

---

## What We Got WRONG (Important!)

### The Flawed Probabilistic Argument

We claimed: "The sum Σ C_k/m_k diverges, so P(all fail) → 0"

**GPT showed this is WRONG**:
1. For fixed p, only k ≤ (p-5)/12 are eligible (size constraint)
2. The sum is FINITE (~(1/2)log p), not divergent
3. The "Main Lemma for all x" is actually FALSE (x=3 is a counterexample)

### What This Means
- Our "95% complete" estimate was overconfident
- The probabilistic heuristic was suggestive but not a proof path
- We needed a different approach

---

## What We Got RIGHT

### The Algebraic Construction (Lemma 1)
If x_k has coprime divisors (a, b) with m_k | (a + b), then we get an ESC solution.

This is **rigorously correct** and matches Bradford's Type II criterion.

### Computational Verification
- Type II succeeds for ALL primes tested (up to 10^7)
- p = 2521 is the only Type-I-resistant prime
- Maximum first-success k = 5

### The Independence Discovery
Type I and Type II operate on independent sequences, explaining complementarity.

---

## The Correct Approach (From GPT Response 1)

### The Minimal Sufficient Condition

**Theorem**: If (p + 4a²) has a divisor m ≡ 3 (mod 4), then Type II succeeds with d = a².

**Proof**:
- Set x = (p + m)/4
- Then d = a² satisfies: a² ≡ -x (mod m)
- This is exactly Bradford's Type II condition ✓

### Computational Verification

| Primes p ≡ 1 (mod 4) tested | 609 (up to 10,000) |
|-----------------------------|---------------------|
| Simple case (a = 1) works | 426 (70%) |
| Need a > 1 | 183 (30%) |
| All rescued by a ≤ 10 | 100% |
| Maximum a needed | 10 |

### The p = 2521 Explanation

| Value | Factorization | Status |
|-------|---------------|--------|
| p + 4 = 2525 | 5² × 101 | All factors ≡ 1 (mod 4) → FAILS |
| p + 16 = 2537 | 43 × 59 | 43 ≡ 3 (mod 4) → SUCCEEDS |

This explains WHY p = 2521 was "hard" and how it's rescued.

---

## The Single Remaining Step

### Core Lemma (To Prove)

> **For every prime p ≡ 1 (mod 4), there exists a ∈ {1, 2, ..., A} (for some absolute constant A) such that (p + 4a²) has a prime factor q ≡ 3 (mod 4).**

### Why This Is Tractable

Unlike our flawed approach, this statement:
- Is about **prime factorization** (well-studied)
- Doesn't require **growing moduli**
- Can use **sieve methods**
- Has **density-theoretic** structure

### Heuristic Support

Integers with ALL factors ≡ 1 (mod 4) are rare (like sums of two squares).
For large enough A, the probability that ALL of (p+4), (p+16), ..., (p+4A²) avoid 3-mod-4 factors should be 0.

---

## File Structure (Updated)

```
/Users/kvallie2/Desktop/esc_stage8/
├── ESC_PROJECT_SUMMARY_v2.md     # This file (CURRENT)
├── ESC_PROJECT_SUMMARY.md        # Old summary (outdated)
│
├── GPT_RESPONSE_1_TORSOR.md      # First GPT response (the breakthrough)
├── GPT_RESPONSE_2_CRITIQUE.md    # Second GPT response (found the flaw)
├── SYNTHESIS_TWO_GPT_RESPONSES.md # Synthesis of both
│
├── verify_minimal_condition.py    # Verified (p+4a²) approach
├── PROOF_STRATEGY_FINAL.md       # Current proof roadmap
├── GPT_CORE_LEMMA_PROMPT.md      # Focused prompt for final step
│
├── [older files - historical interest only]
```

---

## Current Status

| Component | Status |
|-----------|--------|
| Problem reduction | ✓ Complete |
| Algebraic construction | ✓ Correct |
| Probabilistic argument | ✗ Invalid (GPT showed flaw) |
| (p + 4a²) mechanism | ✓ Discovered and verified |
| Computational verification | ✓ Complete to 10^4 |
| Core Lemma | **Needs rigorous proof** |

---

## For Another Instance

If you're picking this up:

1. **READ FIRST**: SYNTHESIS_TWO_GPT_RESPONSES.md (the current state)
2. **IGNORE**: The "divergent sum" argument - it's wrong
3. **FOCUS ON**: Proving the Core Lemma about (p + 4a²)
4. **RUN**: verify_minimal_condition.py to see the evidence

The key insight is that we need to show:
> At least one of (p+4), (p+16), (p+36), ..., (p+4A²) has a prime factor ≡ 3 (mod 4).

This is a statement about avoiding a thin set (integers with all factors ≡ 1 mod 4), which should be provable via sieve methods or density arguments.

---

## References

1. **Bradford (2025)**: Divisor-of-x² criterion - https://math.colgate.edu/~integers/z54/z54.pdf
2. **López (2024)**: Type A/B covering - https://arxiv.org/html/2404.01508v3
3. **Elsholtz-Tao**: Type II parameterizations - https://terrytao.wordpress.com/wp-content/uploads/2011/07/egyptian-count13.pdf
4. **Lenstra (1984)**: Divisors in residue classes - https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1984b/art.pdf
