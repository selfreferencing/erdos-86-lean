# Experiment 38 Analysis: Carry Automaton and Overlap Measures

## Summary

Exp 38 tests the APPROACH7 response's Parseval/correlation strategy by:
1. Building carry automaton transfer matrices for multiplication by 2^h
2. Computing spectral radii to predict overlap rates
3. Directly computing continuous overlap measures mu(F_m ∩ (F_m - h*theta))
4. Verifying the Parseval identity (★)

## Part B: Spectral Radius Results

| h | sr_both | sr_input | ratio sr_both/sr_input |
|---|---------|----------|----------------------|
| 1 | 8.5311 | 9.0000 | 0.9479 |
| 2 | 8.2749 | 9.0000 | 0.9194 |
| 3 | 8.1401 | 9.0000 | 0.9045 |
| 4 | 8.1187 | 9.0000 | 0.9021 |
| 5 | 8.1481 | 9.0000 | 0.9053 |
| 6 | 8.1208 | 9.0000 | 0.9023 |
| 7 | 8.0991 | 9.0000 | 0.8999 |
| 8 | 8.0997 | 9.0000 | 0.9000 |
| 9 | 8.1014 | 9.0000 | 0.9002 |
| 10 | 8.1008 | 9.0000 | 0.9001 |

**Key finding:** The spectral radius ratio converges to 9/10 = 0.900 as h increases. For h >= 7, the ratio is within 0.01% of 0.900. The sr_input is exactly 9 (the number of nonzero digits).

**Interpretation:** The carry automaton for multiplication by 2^h in base 10 shows that, for large h, each output digit is independently ~9/10 likely to be nonzero, conditioned on the input digit being nonzero. The carry propagation creates short-range correlations (noticeable at h=1 where the ratio is 0.948), but these wash out by h ~ 7.

**Important:** sr_both/sr_input ~ 0.9 does NOT mean the overlap ratio mu(overlap)/rho^2 is bounded. The spectral radius controls the ASYMPTOTIC growth rate per digit, not the finite-m ratio. The finite-m ratio includes boundary effects (carry starts at 0) and may differ.

## Part E: Matrix Power Predictions

The conditional probability P(output zeroless | input zeroless) via matrix power:

| h | m=2 | m=3 | m=4 | m=5 | m=6 | m=7 | m=8 | m=9 |
|---|-----|-----|-----|-----|-----|-----|-----|-----|
| 1 | 0.840 | 0.796 | 0.754 | 0.715 | 0.678 | 0.642 | 0.609 | 0.577 |
| 2 | 0.815 | 0.749 | 0.689 | 0.633 | 0.582 | 0.535 | 0.492 | 0.452 |
| 3 | 0.802 | 0.726 | 0.656 | 0.594 | 0.537 | 0.486 | 0.439 | 0.397 |
| 10 | 0.790 | 0.712 | 0.639 | 0.575 | 0.518 | 0.466 | 0.419 | 0.377 |

The conditional probability decays as ~ sr_both^m / sr_input^m ~ (sr_both/9)^m.

For comparison, the "independence" prediction is rho_m = (9/10)^{m-1}:

| m | rho_m | h=1 cond. | h=10 cond. |
|---|-------|-----------|------------|
| 2 | 0.900 | 0.840 | 0.790 |
| 3 | 0.810 | 0.796 | 0.712 |
| 4 | 0.729 | 0.754 | 0.639 |
| 5 | 0.656 | 0.715 | 0.575 |
| 9 | 0.430 | 0.577 | 0.377 |

**Crucial observation:** The conditional probabilities are HIGHER than rho_m for small h (especially h=1), meaning the overlap ratio mu(overlap)/rho^2 > 1 (positive correlation). The conditional probability is LOWER than rho_m for large h, meaning negative correlation.

This matches the continuous overlap data: lag-1 shows the strongest positive correlation.

## Part F: Continuous Overlap Ratios

mu(F_m ∩ (F_m - h*theta)) / rho_m^2:

| m | h=0 | h=1 | h=2 | h=3 | h=4 | h=5 | h=9 | h=10 |
|---|-----|-----|-----|-----|-----|-----|-----|------|
| 2 | 1.136 | 1.050 | 1.013 | 1.000 | 0.988 | 0.982 | - | - |
| 3 | 1.265 | 1.106 | 1.035 | 1.003 | 0.989 | 0.989 | 1.024 | 1.038 |
| 4 | 1.405 | 1.165 | 1.057 | 1.008 | 0.992 | 0.995 | 1.024 | 1.039 |
| 5 | 1.562 | 1.227 | 1.080 | 1.013 | 0.994 | 1.001 | 1.024 | 1.039 |

**WARNING: The lag-1 ratio is GROWING with m.** It goes 1.050 -> 1.106 -> 1.165 -> 1.227.

If this growth continues, it appears to approach ~1.56 (which is the h=0 self-correlation, i.e., 1/rho_m). This would be VERY BAD: it would mean the lag-1 excess grows proportionally to 1/rho_m, which would overwhelm the exponential decay in the Parseval identity.

**However:** The lag-1 ratio grows slowly (factor ~1.07 per m increment). Let me fit:
- m=2: 1.050, m=3: 1.106, m=4: 1.165, m=5: 1.227
- Differences: 0.056, 0.059, 0.062 (linearly growing)
- Pattern: ratio ~ 1 + 0.05*m (approximately)

If ratio ~ 1 + C*m, then the excess at lag 1 is:
excess = (ratio - 1) * rho_m^2 ~ C*m * rho_m^2

The contribution to (★) from lag 1 alone is:
2 * (L-1) * excess ~ 2 * 3m * C*m * rho_m^2 = 6C * m^2 * rho_m^2

Since rho_m^2 ~ 0.81^m, this still decays exponentially. So the Parseval approach SURVIVES even if the lag-1 ratio grows linearly in m.

**For lags h >= 3:** The ratios are within [0.985, 1.040] and show NO growth trend with m. The h=10 ratio is ~1.039 for all m, matching the convergent denominator q_2 = 10.

## Part G: Parseval Identity Verification

| m | ||R_m||_2 | sqrt(L*rho) | Chebyshev bound |
|---|-----------|-------------|-----------------|
| 2 | 1.081 | 2.482 | 4.678 |
| 3 | 1.751 | 2.812 | 12.268 |
| 4 | 2.431 | 3.156 | 23.635 |
| 5 | 2.861 | 3.300 | 32.737 |

**Problem:** ||R_m||_2 is GROWING with m for m = 2..5. This contradicts the APPROACH7 response's prediction of ||R_m||_2 ~ sqrt(m) * 0.95^m -> 0.

**Diagnosis:** For small m (2-5), L_m * rho_m is LARGE (6.2, 7.9, 10.0, 10.9). The Parseval prediction is designed for the ASYMPTOTIC regime where L_m * rho_m << 1. We're not there yet.

The L_m * rho_m values:
- m=2: 7*0.880 = 6.16
- m=5: 17*0.640 = 10.89
- m=10: 34*0.387 = 13.16 (still large!)
- m=15: 50*0.206 = 10.28 (still large!)
- m=20: 67*0.122 = 8.14
- m=30: 100*0.042 = 4.24
- m=50: 166*0.005 = 0.86 (now < 1)
- m=86: 286*0.00001 = 0.003 (asymptotic regime)

L_m * rho_m peaks around m ~ 10 at ~13 and only drops below 1 around m ~ 45-50. The Parseval argument only bites in the asymptotic regime.

**This is not a problem for the conjecture** (which needs N_m = 0 for LARGE m), but it means the Parseval identity cannot be verified as "going to zero" with our small-m data.

## Conclusions

**Conclusion 45.** The carry automaton spectral radius for multiplication by 2^h satisfies sr_both/sr_input -> 9/10 as h -> infinity, confirming that output digits become independent of input digits as the shift h grows. Short-range correlations (h=1: ratio 0.948, h=3: ratio 0.904) wash out by h ~ 7.

**Conclusion 46.** The continuous overlap ratio mu(F_m ∩ (F_m - h*theta))/rho_m^2 at lag 1 grows approximately linearly: ~1 + 0.05*m. This growth is concerning but does NOT kill the Parseval approach, because the contribution 2(L-1) * excess * rho_m^2 ~ m^2 * 0.81^m still decays exponentially.

**Conclusion 47.** For lags h >= 3, the overlap ratio is within [0.985, 1.040] with no growth trend in m, confirming quasi-independence at medium and long lags.

**Conclusion 48.** The convergent denominator q_2 = 10 creates a noticeable positive correlation at lag h=10 (ratio ~1.039). Lags near convergent denominators show systematically higher overlap ratios. This is consistent with the resonance structure of theta = log10(2).

**Conclusion 49.** The Parseval identity ||R_m||_2^2 is verified for m=2..5 but is NOT yet in the asymptotic regime where it decays. L_m * rho_m peaks at ~13 (around m=10) and only drops below 1 around m ~ 50. The Parseval argument is valid but only bites asymptotically.

**Conclusion 50.** The carry automaton transfer matrix approach CANNOT compute overlaps for h >= 11 due to the exponential growth of carry states (2^h states). For h >= 11, an alternative approach is needed (e.g., the continuous overlap computation used in Part F, or a compressed carry automaton exploiting the structure of 2^h).

## Status of the Parseval/QI Strategy

The strategy is VIABLE but requires:
1. A **proof** that mu(F_m ∩ (F_m - h*theta))/rho_m^2 <= C(h) with C(h) having at most polynomial growth in h (the data shows C(1) ~ 1 + 0.05*m grows linearly in m, but the weighted sum still converges).
2. An **upgrade** from L2 to pointwise at x = m*theta (the "exceptional set avoidance" problem).

The carry automaton approach works for small h but hits a state-space explosion for h >= 11. The proof of QI for all lags h <= L_m ~ 3m requires either:
- A compressed carry automaton (exploiting base-10 structure of 2^h)
- A product-formula argument that bounds the overlap without explicit carry tracking
- A direct Fourier/spectral argument

## Recommended Next Steps

1. **Extrapolate the lag-1 ratio growth.** Compute continuous overlaps for m = 6,7 (slow but possible) to confirm the linear growth pattern and get a tighter bound.

2. **Write APPROACH12 prompt.** The prompt should present the Parseval identity, the QI data (including the lag-1 growth), and ask about: (a) proving QI via carry automaton or other means, (b) upgrading L2 to pointwise, (c) whether the lag-1 growth is bounded by O(m) or could be worse.

3. **The key mathematical question:** Does mu(F_m ∩ (F_m - theta)) / rho_m^2 grow as O(m), O(sqrt(m)), or is it bounded? The answer determines whether the Parseval approach works with room to spare (bounded), barely works (O(m)), or fails (faster than polynomial).
