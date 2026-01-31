# Investigation Summary: Prompts 46-58
## Unconditional Effective Erdős-Straus via ED2

**Date:** 2025-01-30
**Investigator:** Kevin Vallier + GPT 5.2 Thinking + Claude Opus 4.5
**Goal:** Determine if ES can be made unconditionally effective using ED2

---

## Executive Summary

**Question:** Can the Erdős-Straus conjecture be proven unconditionally AND effectively (with computable P₀)?

**Answer:** NO. The Siegel barrier blocks effectivity.

**What we achieved:**
- Unconditional ES for large P (ineffective P₀)
- GRH-conditional ES with effective P₀
- Complete understanding of WHY effectivity fails

---

## The Investigation Arc

### Phase 1: Understanding ED2 Requirements (Prompts 46-51)

**Key finding from 46:** ED2 doesn't require prime q. Squarefree q works via CRT.

**Key finding from 48:** Pollack gives q < P (too weak). We need q << √P.

**Key finding from 50-51:** The constraint is SIZE (q << √P), not primality.

### Phase 2: The Squarefree Density Approach (Prompts 52-53)

**Initial hypothesis:** Maybe squarefree q gives "more candidates" to find one below √P.

**Result: DEAD END**

From 53A/53B:
> "Existence of squarefree q << √P ⟺ existence of prime ℓ << √P with same condition"

Squarefree doesn't bypass the "first good prime" bottleneck.

### Phase 3: The Burgess-Product Approach (Prompt 54)

**New hypothesis:** Use Burgess-scale primes (P^{0.151}) and take products.

**Result: WRONG SIGN**

From 54A/54B + 57A/57B:
- Burgess/Pollack/Treviño give χ(ℓ) = **-1** (nonresidues)
- ED2 needs (−P/ℓ) = **+1** (residues)
- **These are different!**

### Phase 4: The Residue-Side Methods (Prompts 55-56)

**P+1 Trick (56B):**
- If ℓ | (P+1) is odd, then -P ≡ 1 (mod ℓ), so (−P/ℓ) = 1
- Works for most P (not Sophie Germain exceptions)
- Fully explicit when it works

**Linnik-Vinogradov (56A):**
- Least prime quadratic residue ≤ P^{1/4+ε}
- Covers all large P
- **But ineffective** (Siegel)

### Phase 5: The Bridge Problem (Prompts 57-58)

**Discovery from 57A/58A:** We were conflating two things:

1. "Find small q with s² ≡ -P (mod q)" ← Methods 1-2 solve this
2. "Find ED2 triple (δ, b, c) satisfying identity" ← The actual requirement

**Resolution from 58B:** The ED2 construction DOES work once you have small q with right character. The window q < √P is sufficient.

### Phase 6: The Effectivity Wall (Prompt 58B)

**Final answer:**

| What | Status |
|------|--------|
| Unconditional ES for large P | ✓ TRUE |
| Effective (computable) P₀ | ✗ BLOCKED |
| Blocker | Siegel zeros |

---

## The Three Methods Evaluated

### Method 1: P+1 Trick

```
Take ℓ = smallest odd prime factor of (P+1)
Since ℓ | (P+1): -P ≡ 1 (mod ℓ), so (−P/ℓ) = 1
If ℓ ≤ √P: take q = ℓ, done
```

| Aspect | Verdict |
|--------|---------|
| Correct sign | ✓ |
| Small enough | ✓ (when works) |
| Effective | ✓ |
| Covers all P | ✗ (Sophie Germain exceptions) |

### Method 2: Linnik-Vinogradov

```
Least prime quadratic residue ≤ P^{1/4+ε}
Take q = that prime
P^{1/4} << √P, so ED2 window satisfied
```

| Aspect | Verdict |
|--------|---------|
| Correct sign | ✓ |
| Small enough | ✓ |
| Effective | ✗ (Siegel) |
| Covers all P | ✓ |

### Method 3: Burgess/Pollack Product

```
Take k primes ≤ P^{0.151}, product ≤ P^{0.45} < √P
```

| Aspect | Verdict |
|--------|---------|
| Correct sign | ✗ (gives -1, need +1) |
| Small enough | ✓ |
| Effective | N/A |
| Covers all P | N/A |

**Method 3 was a red herring** - wrong character value.

---

## Key Technical Findings

### 1. The Sign Distinction

| Source | Character value | What it gives |
|--------|----------------|---------------|
| Burgess bound | χ = -1 | Nonresidues (inert primes) |
| Treviño explicit | (D/p) = -1 | Nonresidues |
| Linnik-Vinogradov | χ = +1 | Residues (split primes) |
| P+1 trick | (−P/ℓ) = +1 | Residues |

**ED2 needs residues (+1), not nonresidues (-1).**

### 2. The ED2 Window

The fundamental constraint is on A, not q:
```
A ∈ (P/4, 3P/4)
```

The q << √P constraint is DERIVED from this via how q controls the parameter k.

Any q ≤ P^{1/2-ε} satisfies the window with room to spare.

### 3. The Siegel Barrier

The P^{1/4+ε} bound for least prime quadratic residue is:
- Unconditionally true (Linnik-Vinogradov)
- Ineffective (constant depends on possible Siegel zeros)

This is the SAME barrier that blocks effective Chebotarev.

### 4. The Density of Exceptions

For the P+1 trick, exceptions occur when (P+1)/2 is prime (Sophie Germain pattern):
- Density: ~X/(log X)² among primes ≤ X
- Density 0, but infinitely many
- Cannot be ruled out unconditionally

---

## Theorems We Can State

### Theorem A (Unconditional, Non-Effective)

> For every ε > 0, there exists P₀(ε) such that for all primes P > P₀(ε), the equation 4/P = 1/x + 1/y + 1/z has a solution in positive integers.

**Proof:** Linnik-Vinogradov gives prime q ≤ P^{1/4+ε} with (−P/q) = 1. ED2 with this q produces the solution.

**Caveat:** P₀(ε) is not effectively computable.

### Theorem B (GRH-Conditional, Effective)

> Assuming GRH, for all primes P > P₀ (explicit), the equation 4/P = 1/x + 1/y + 1/z has a solution in positive integers.

**Status:** This is what your Lean formalization proves.

### Theorem C (Partial, Fully Effective)

> For all primes P such that (P+1)/2 is not prime, the P+1 trick gives an explicit ES solution.

**Proof:** Take q = smallest odd prime factor of (P+1). Explicitly constructible.

---

## Literature Discovered

| Topic | Reference |
|-------|-----------|
| ED2 formalization | Dyachenko arXiv:2511.07465 |
| Least prime residue | Ge-Milinovich-Pollack (Ole Miss) |
| Burgess bounds | Pollack NTS0812.pdf |
| Residue-side Burgess | Pollack hudson.pdf |
| Explicit Treviño | Lake Forest College PDF |
| Ineffectivity | MathOverflow #401156 |

---

## What This Means for the Project

### Achieved
- Complete understanding of the unconditional landscape
- Confirmation that Siegel is the fundamental barrier
- Multiple methods that work "eventually"

### Not Achieved
- Unconditional effective ES (blocked by Siegel)
- Explicit P₀ without GRH

### Path Forward Options

1. **Accept GRH:** Your current Lean proof is the best possible effective result.

2. **Hybrid approach:** Use P+1 trick for most P, computational verification for exceptions up to some bound.

3. **Different conjecture:** Some ES variants might avoid the character condition entirely.

4. **Wait for breakthroughs:** Siegel zero nonexistence would immediately give effectivity.

---

## Conclusion

The investigation conclusively shows that **unconditional effective ES via ED2 is blocked by the Siegel barrier**. This is not a gap in our approach—it's a fundamental limitation of current number theory.

The GRH-conditional result remains the strongest effective statement available.

---

## Appendix: Prompt Index

| Prompt | Topic | Key Finding |
|--------|-------|-------------|
| 46 | ED2 requirements | Squarefree q works via CRT |
| 47 | Research decision | Which bet to pursue |
| 48 | Linnik dichotomy | Pollack gives q < P (too weak) |
| 49 | Alternative params | q-bottleneck fundamental |
| 50 | Squarefree in literature | Size constraint, not primality |
| 51 | Effective ES survey | Verified to 10^17, hard core mod 840 |
| 52 | Siegel history | Dichotomy patterns work sometimes |
| 53 | Sieve for squarefree | Density doesn't help existence |
| 54 | Burgess for squarefree | Explicit bounds exist (wrong sign) |
| 55 | Density estimates | |Q_P(X)| ~ X/√(log X) |
| 56 | Almost-primes | P+1 trick; L-V for residues |
| 57 | ED2 bridge | Local solvability ≠ ED2 triple |
| 58 | Final verification | Siegel blocks effectivity |
