# APPROACH 31: L² to Pointwise Control for Specific Irrationals

## Context

We are working on the Erdős 86 Conjecture: the last zeroless power of 2 is 2^86.

Previous work (APPROACH7, APPROACH12) established a Fourier/Parseval framework:

### The Setup

Let F_m ⊂ [0,1) be the set of x such that the first m digits of 10^x are all nonzero (the "zeroless region"). Then:
- μ(F_m) = (9/10)^m ≈ 0.9^m (exponentially small)
- 2^n has zeroless m-digit prefix iff {n·θ} ∈ F_m, where θ = log₁₀(2)

Define the discrepancy function:
```
R_m(x) = #{0 ≤ n < L_m : {n·θ + x} ∈ F_m} - L_m · μ(F_m)
```
where L_m = ⌊10/θ⌋ · m ≈ 3.32m is the orbit length at scale m.

### The L² Result (Essentially Proven)

The Parseval identity gives:
```
∫₀¹ |R_m(x)|² dx = (L_m terms involving overlaps)
```

Under mild assumptions (or even crude bounds), this yields:
```
||R_m||₂ = O(m · 0.95^m) → 0 exponentially
```

This proves **metric finiteness**: for almost every θ, the orbit {n·θ} enters F_m only finitely often.

### The Critical Gap: L² to Pointwise

The L² bound controls R_m for **almost every** x. But we need R_m at the **specific** point x = 0 (or equivalently, we need to know that the orbit of θ₀ = log₁₀(2) avoids F_m for large m).

**Chebyshev gives:** μ{x : |R_m(x)| > 1/2} ≤ 4·||R_m||₂² → 0

**Borel-Cantelli gives:** For a.e. x, only finitely many m have |R_m(x)| > 1/2.

**But:** The point x changes with m in our problem (we're asking about different depths), and we need the specific θ₀ = log₁₀(2), not a generic θ.

### The Paradigm Shift (from Exp 40)

Computational investigation revealed:
- The exceptional set B_m = {x : |R_m(x)| > 1/2} has **near-full measure** for small m
- The point m·θ is IN B_m for all m = 2..30
- N_m = 0 for all m ≥ 36 (verified to m = 100)
- For m ≥ 50, |R_m(m·θ)| < 1, so the problem "solves itself" asymptotically

**Key realization:** The L²-to-pointwise step is **equivalent to the conjecture itself** in the pre-asymptotic regime (m = 36..49).

## The Core Question

**How do we prove that the specific point θ₀ = log₁₀(2) avoids the bad set B_m for large m?**

This is not a generic almost-everywhere result. It requires arithmetic properties of θ₀.

## What We Know About θ₀ = log₁₀(2)

### Continued Fraction
```
θ = [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117, ...]
```

### Irrationality Measure
By Baker's theorem on linear forms in logarithms, θ₀ has **finite irrationality measure** μ(θ₀) = 2 (it's not a Liouville number). In fact, for any ε > 0:
```
|θ₀ - p/q| > c(ε) · q^{-(2+ε)}  for all rationals p/q
```

### Diophantine Type
θ₀ is of **finite type** (bounded partial quotients in a measure-theoretic sense), which is the "generic" behavior for algebraic irrationals.

## Questions

### Q1: Known Shrinking Target Theorems

The classical shrinking target results (Kurzweil, Kim-Tseng, Haynes-Jensen-Kristensen) say:

> If θ has finite type and B_m are nested balls with Σ μ(B_m) < ∞, then for a.e. θ, only finitely many n have {n·θ} ∈ B_n.

**Problem:** Our B_m is NOT a nested sequence of balls. It's a union of ~9^m intervals (or fewer after pruning) with complicated geometry.

Can these theorems be extended to digit-cylinder targets? What structural properties of B_m would be needed?

### Q2: The Hausdorff Dimension Bound

APPROACH8 response noted: dim_H(E) ≤ log₁₀(9) ≈ 0.954, where E is the set of θ for which the orbit enters F_m infinitely often.

This means E is a **null set** (measure zero). But it doesn't directly show θ₀ ∉ E.

Can we strengthen this to show E is contained in a Diophantine class that excludes θ₀?

### Q3: Effective Equidistribution

For irrational rotations, there are effective equidistribution results:
```
|#{n ≤ N : {n·θ} ∈ I} - N·|I|| ≤ C(θ) · log(N)
```

for intervals I, where C(θ) depends on the continued fraction of θ.

Can we use effective equidistribution for θ₀ = log₁₀(2) combined with the structure of F_m to get pointwise control?

### Q4: The Fourier Coefficient Approach

The indicator 1_{F_m} has Fourier expansion:
```
1_{F_m}(x) = μ(F_m) + Σ_{k≠0} ĉ_k(m) · e^{2πikx}
```

The discrepancy R_m(x) involves evaluating this at x = n·θ and summing:
```
R_m(0) = Σ_{k≠0} ĉ_k(m) · (Σ_{n<L_m} e^{2πikn·θ})
```

The inner sum is a geometric series with known bounds. If |ĉ_k(m)| decay fast enough in k, and the geometric sums have cancellation, we get pointwise control.

What decay rate on |ĉ_k(m)| is needed? Is it achievable for the zeroless indicator?

### Q5: The Carry Automaton and Correlation Decay

The overlap μ(F_m ∩ (F_m - h·θ)) measures correlation between F_m and its translate. Experimentally (Exp 32, Exp 38), these overlaps are bounded by:
```
μ(F_m ∩ (F_m - h·θ)) ≤ C(h) · μ(F_m)²
```

for small h, suggesting quasi-independence. The carry automaton provides a mechanism: multiplication by 2^h scrambles digits via carry propagation.

Can correlation decay (quantified via the carry automaton's spectral gap) yield pointwise Fourier control?

### Q6: The Danger Cylinder Bypass

An alternative to proving pointwise control everywhere is proving it only matters for a finite set:

**Claim (unproven):** For large m, the set of "dangerous" configurations that could capture the orbit {n·θ} has only O(1) elements.

If true, we wouldn't need generic pointwise control; we'd only need to check finitely many cases, which Baker's theorem could then handle.

This connects to APPROACH11/28 (danger cylinders). But the O(1) claim remains unproven.

### Q7: The Maynard Decorrelation Strategy

James Maynard's work on primes in arithmetic progressions uses sophisticated decorrelation arguments. The key idea:

> Even if pointwise bounds are hard, if we can show that the "bad" contributions from different scales m are uncorrelated, Borel-Cantelli applies to the intersection.

For our problem: even if |R_m(θ)| is occasionally large, if the events "|R_m(θ)| > 1/2" are sufficiently independent across m, only finitely many can occur.

Can this decorrelation strategy be applied to the zeroless problem?

### Q8: The Specific Arithmetic of θ₀

The continued fraction of θ₀ = log₁₀(2) has some large partial quotients (18, 117, ...). These create "near-resonances" where {q_n · θ₀} is very small.

Do these near-resonances cause problems for pointwise control? Or do they only affect a sparse set of m values?

## What Would Suffice

To prove Erdős 86 via this route, we need ONE of:

1. **Direct pointwise bound:** |R_m(0)| < 1/2 for all m ≥ M₀, for some explicit M₀ ≤ 35 (since N_m > 0 for m ≤ 27)

2. **Exceptional set exclusion:** Prove θ₀ is not in the exceptional set E

3. **Decorrelation + Borel-Cantelli:** Prove the events {|R_m(0)| > 1/2} are sufficiently independent

4. **Finite reduction:** Reduce to checking finitely many dangerous configurations, then verify

## Desired Output

1. **Assessment of each approach** (Q1-Q8): which are viable, which are blocked?

2. **The most promising path** to pointwise control for θ₀ = log₁₀(2)

3. **What new techniques or results** would be needed?

4. **If this route is fundamentally blocked:** explain why, and what the obstruction reveals about the problem's difficulty

## References

- Kurzweil (1955): Shrinking targets for irrational rotations
- Kim & Tseng: Effective results on shrinking targets
- Haynes, Jensen, Kristensen: Shrinking targets for badly approximable numbers
- Maynard, J.: Decorrelation in analytic number theory
- OEIS A007377: Powers of 2 with no zeros

## Data Available

- Correct zeroless powers list: n = 1,2,3,4,5,6,7,8,9,13,14,15,16,18,19,24,25,27,28,31,32,33,34,35,36,37,39,49,51,67,72,76,77,81,86
- N_m counts for m = 2..100 (showing N_m = 0 for m ≥ 36)
- Overlap ratios from Exp 32, Exp 38
- Continued fraction of θ₀ to 50+ terms
