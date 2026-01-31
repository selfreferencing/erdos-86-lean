# Experiment 37: Corrected Discrepancy with Dirichlet Kernel

## Summary

Exp 37 computed the CORRECT discrepancy bound T_m = sum_{k!=0} |hat{1_{F_m}}(k)| * |D_{L_m}(k*theta)| using the Dirichlet kernel instead of the naive 1/||k*theta|| bound from Exp 36. The Dirichlet kernel reduces the sum by a factor of ~10 (T/S ~ 0.10-0.11), but T_m is still far too large (66-109) to prove finiteness (need T_m < 1).

## Key Results

### 1. T_m values

| m | L_m | T_m (corrected) | S_m (naive) | T/S ratio |
|---|-----|-----------------|-------------|-----------|
| 2 | 7 | 19.4 | 182.9 | 0.106 |
| 3 | 10 | 47.7 | 450.0 | 0.106 |
| 4 | 14 | 97.4 | 963.3 | 0.101 |
| 5 | 17 | 108.9 | 1030.3 | 0.106 |
| 6 | 20 | 102.0 | 930.6 | 0.110 |
| 7 | 24 | 66.1 | 602.8 | 0.110 |

T_m peaks at m=5 then decreases. The ratio T/S is stable at ~10%, meaning the Dirichlet kernel gives a consistent 10x improvement over the naive bound.

### 2. The finiteness criterion FAILS badly

For N_m = 0, need T_m < 1 - L_m*rho_m. But L_m*rho_m > 1 for all m <= 20 (it peaks around m=7 at 12.4 then slowly decreases). The threshold is negative, making the criterion impossible to satisfy.

This is not a "just barely fails" situation. T_m is 60-100x too large.

### 3. The sum does NOT converge

Part G shows the truncation convergence check:

| K_cutoff | T_m (m=6) |
|----------|-----------|
| 100 | 7.2 |
| 500 | 20.1 |
| 1000 | 29.9 |
| 2000 | 43.5 |
| 5000 | 70.8 |
| 10000 | 102.0 |

T_m grows roughly as log(K) or K^{0.3}. The sum does not converge as K -> infinity. This is a fundamental obstruction, not a truncation artifact.

### 4. Dominant frequencies

k=10 (convergent denominator) dominates at every m, contributing ~0.7 to T_m. Other persistent contributors: k=103, k=30, k=63, k=93, k=392. These cluster near convergent denominators of theta = log10(2).

### 5. C(k) extrapolation is valid for m >= 5

The predicted T_m (using m=6 as template) matches actual within 2.5% for m=5,6. For m=7, the prediction is 47.9% too high (because K_max = 5000 for m=7 vs 10000 for the template). For m <= 3, the prediction is wildly off because C(k) has not yet stabilized.

## Interpretation

### Why Strategy C' fails in the direct Erdos-Turan form

The discrepancy bound sum_{k!=0} |hat(k)| * |D_L(k*theta)| diverges because:

1. **|hat{1_{F_m}}(k)| ~ C(k) * (9/10)^{m-1}** with C(k) ~ 1/k on average. This gives |hat(k)| ~ 1/k * 0.9^m.

2. **|D_L(k*theta)| ~ min(L, 1/||k*theta||)**, and for most k, |D_L| ~ L ~ 3m (the Dirichlet kernel hits its maximum value L when ||k*theta|| is not too small, i.e., for generic k).

3. **The sum** ~ sum_{k=1}^{infty} (1/k * 0.9^m) * 3m = 3m * 0.9^m * sum 1/k. The harmonic sum diverges, so T_m = infinity for any fixed m.

The exponential decay 0.9^m cannot compete with the logarithmic divergence of the harmonic sum. The Erdos-Turan / Weyl sum approach, applied with triangle-inequality bounds on each Fourier mode separately, is structurally incapable of proving N_m = 0.

### The missing ingredient: PHASE CANCELLATION

The actual error is:

N_m - L_m * rho_m = sum_{k!=0} hat{1_{F_m}}(k) * W_m(k)

where W_m(k) = e(k*m*theta) * D_{L_m}(k*theta) is a COMPLEX number. The triangle inequality |sum| <= sum |terms| discards the phases, losing all cancellation.

The data from Exp 25 shows |N_m - L_m*rho_m| < 11 for all m <= 27. So the actual error is O(1), while the triangle-inequality bound is ~100. The cancellation ratio is ~10:1.

### What this means for the proof strategy

1. **Direct Erdos-Turan is dead.** No amount of refinement to the term-by-term bound can make the sum converge. The approach is structurally wrong for this problem.

2. **Phase-aware methods needed.** To prove N_m = 0, we need to show that the complex sum sum_k hat(k) * W_m(k) is small, exploiting cancellation between terms, not bounding each term separately.

3. **Possible approaches:**
   - (a) Show that hat{1_{F_m}}(k) and D_L(k*theta) are "decorrelated" so that the complex sum cancels.
   - (b) Group frequencies by convergent denominator blocks and show intra-block cancellation.
   - (c) Use the product structure of F_m to rewrite the Weyl sum in a form where cancellation is manifest.
   - (d) Abandon Fourier entirely; use a direct argument (e.g., transfer operator spectral gap from Noda's framework).

4. **Strategy F (second moment)** remains viable. It avoids Fourier phases entirely by working with expectations and variances.

## Conclusions

**Conclusion 41.** The corrected discrepancy bound T_m = sum |hat(k)| * |D_L(k*theta)| reduces the naive bound S_m by a factor of ~10 (T/S ~ 0.10) but is still 60-100x too large to prove finiteness.

**Conclusion 42.** The Erdos-Turan bound diverges as K -> infinity because |hat{1_{F_m}}(k)| ~ C(k)/k * 0.9^m combined with |D_L| ~ L ~ 3m gives a harmonic-sum divergence. This is structural, not a truncation artifact.

**Conclusion 43.** Strategy C' in the triangle-inequality form (bound each Fourier mode separately) is DEAD. Phase cancellation is essential. The actual discrepancy is O(1) (Exp 25), while the triangle-inequality bound is ~100. The 10:1 cancellation ratio indicates substantial but finite cancellation in the Weyl sum.

**Conclusion 44.** The problem reduces to either (a) a phase-aware bound on sum_k hat{1_{F_m}}(k) * D_L(k*theta), or (b) an entirely different approach (transfer operator spectral gap, second moment method). The Fourier coefficient data from Exp 36 (C(k) stabilization) is still valuable for approach (a).

## Recommended Next Steps

1. **Phase-aware Weyl sum analysis**: Compute the ACTUAL complex sum sum_k hat(k) * W_m(k) for m = 2..7 and compare to N_m - L_m*rho_m. Verify the ~10:1 cancellation ratio. Identify which frequency bands contribute constructively vs destructively.

2. **Convergent-block decomposition**: Group k by proximity to convergent denominators q_n. Within each block, the phases e(k*m*theta) rotate coherently. Show that intra-block cancellation reduces each block's contribution.

3. **Strategy F acceleration**: The second moment / Borel-Cantelli approach (Exp 32 quasi-independence) avoids Fourier phases. Prioritize the Diophantine input needed to specialize from a.e. theta to theta = log10(2).

4. **Noda spectral gap**: If Noda's transfer operator M_n[1_{nonzero}] has a spectral gap (eigenvalues < 1 except the leading one), this directly gives exponential mixing and thus equidistribution, bypassing Fourier entirely.
