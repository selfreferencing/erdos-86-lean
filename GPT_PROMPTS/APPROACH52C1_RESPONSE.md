# APPROACH 52C1: GPT Response — Full 18×18 Matrix Analysis

## Summary

GPT built the explicit 18×18 transition matrix P from Exp 82's 9×9 pair data using the canonical "max-entropy" lift.

## Key Quantitative Results

| Quantity | Exp 82 (Data-Driven) | 52A/B (Theoretical) | Uniform Baseline |
|----------|---------------------|---------------------|------------------|
| p₀ = π̃(5,0) | **0.04877** | 0.0385 | 0.0494 (4/81) |
| \|λ₂\| | **0.01546** | 0.227 | 0 |
| ρ (survival) | **0.94853** | 0.9602 | 0.9479 |
| Correlation length | **0.24 digits** | ~4 digits | ∞ |

## Critical Insight: Why Exp 82 Differs from 52A/B

> "The Exp 82 matrix is an *average over all positions and all numbers*, conditioning only on 'this pair has no 0'. That average apparently washes out the stronger conditional suppression you saw in Exp 62–71 / Exp 70."

The 52A/B numbers used **~22% killing pair suppression** (p₀/baseline ≈ 0.78). Exp 82 shows only **~1-2% suppression** on average.

**The discrepancy isn't from "2×2 aggregation loses information."** The full 9×9 chain is still almost i.i.d. The discrepancy comes from **conditioning/context**: Exp 82 is not the same conditional regime as the one that matters for long zeroless survival.

## Eigenvalue Analysis

Full 9×9 digit chain eigenvalues (sorted by magnitude):
- 1.0000000
- **-0.01545995** (λ₂)
- +0.01480257
- +0.00932619
- -0.00590842 ± 0.00547771i
- +0.00593261
- +0.00489828 ± 0.00215892i

Correlation decay:
- Distance 1: ~1.5%
- Distance 2: ~0.024%
- Distance 3: ~0.00037%

**The digit process is essentially memoryless beyond one step.**

## Stationary Distribution π̃(d,c)

| digit d | π̃(d,0) | π̃(d,1) | π̃(d,0)+π̃(d,1) |
|---------|---------|---------|----------------|
| 1 | 0.0524 | 0.0617 | 0.1141 |
| 2 | 0.0507 | 0.0618 | 0.1124 |
| 3 | 0.0499 | 0.0603 | 0.1101 |
| 4 | 0.0501 | 0.0608 | 0.1110 |
| **5** | **0.0488** | 0.0623 | 0.1110 |
| 6 | 0.0487 | 0.0613 | 0.1100 |
| 7 | 0.0489 | 0.0609 | 0.1098 |
| 8 | 0.0487 | 0.0608 | 0.1095 |
| 9 | 0.0495 | 0.0626 | 0.1120 |

**Effective zero rate:** p₀ = π̃(5,0) ≈ 0.0488 (only ~1.2% below uniform)

## What Missing Data Would Help (Q6)

To make the 18-state model meaningfully 18-state, we need one of:

### Option A: Conditional digit transitions by carry-in
- Q^(0)[a,b] = P(next digit = b | current digit = a, carry-in = 0)
- Q^(1)[a,b] = P(next digit = b | current digit = a, carry-in = 1)

### Option B: 3-gram counts of digits
Since carry-in is determined by the PREVIOUS digit's low/high class:
- N₀[a,b] = #{(x,a,b) : x ∈ {1,2,3,4}} (carry-in 0)
- N₁[a,b] = #{(x,a,b) : x ∈ {5,6,7,8,9}} (carry-in 1)

### Option C: Direct 18×18 state transition counts
Scan triples (a_{i-1}, a_i, a_{i+1}) and count transitions (a_i, c_i) → (a_{i+1}, c_{i+1}) where c_i = τ(a_{i-1}).

### Additional Recommendation
Compute Q restricted to positions inside runs of ≥k consecutive nonzero digits (e.g., k=5,10), or from the rare actually-zeroless powers (up to n=86).

## Bottom Line

If we take Exp 82's 9×9 pair matrix at face value:
- The lifted 18-state chain is explicit
- Mixing is extremely fast: |λ₂| ≈ 0.0155
- Effective kill rate: p₀ ≈ 0.0485-0.0488
- Survival spectral radius: ρ ≈ 0.9485 (barely above i.i.d. uniform)

**To recover the stronger effects from 52A/B, we need carry-conditioned or longer-run-conditioned transition data.**
