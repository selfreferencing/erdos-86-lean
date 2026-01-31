# Experiment 29 Analysis: Probabilistic Finiteness

## Central Question

Can probabilistic arguments (Borel-Cantelli, second moment) close the gap from "E[N_m] -> 0" to "N_m = 0 eventually"?

## Verdict: The probabilistic route faces a quantitative barrier but provides crucial structural information.

## Part A: E[N_m] is large and slow to decay

E[N_m] = L_m * mu(F_m) = ceil(m/theta) * 0.9^{m-1}.

This function peaks around m ~ 9 (where E[N_m] ~ 13) and decays slowly:
- E[N_m] < 10 at m = 19
- E[N_m] < 5 at m = 29
- **E[N_m] < 1 at m = 50**
- E[N_m] < 0.1 at m = 76
- E[N_m] < 0.01 at m = 100

The Borel-Cantelli sum is finite: sum_m E[N_m] = 332.7. But the tail sum is large:
- sum_{m >= 27} = 77.6
- sum_{m >= 50} = 11.3
- sum_{m >= 100} = 0.107
- sum_{m >= 150} = 0.0008

This means: under a uniform random alpha, the expected number of m-values beyond m=27 with N_m > 0 is ~78. So it's not surprising that at m=29-34 we still see hits. The expected cessation point under uniform distribution would be around m ~ 80-100. For theta = log10(2) specifically, the actual N_m will depend on whether it's a "lucky" or "unlucky" alpha.

## Part B: The oversampling pattern (KEY FINDING)

The ratio N_m / E[N_m] (actual vs expected) reveals a striking pattern:

**Phase 1 (m=2-19): Undersampling.** Ratio ranges 0.44-0.95. The orbit actually UNDER-samples F_m compared to uniform. Mean ratio ~ 0.73.

**Phase 2 (m=20-30): Oversampling.** Ratio ranges 1.10-2.54. The orbit OVER-samples F_m. The spike at m=24-25 (ratio 2.54x) is dramatic.

**Phase 3 (m=31-34): Return toward 1.** Ratio drops back to 0.57-1.37.

The phase transition around m=20 is important. Before m=20, the orbit under-samples (good for finiteness). After m=20, it over-samples (bad for finiteness). But even with 2x oversampling, E[N_m] * 2 = 2 * ceil(m/theta) * 0.9^{m-1} still -> 0, just more slowly.

**The 2.5x oversampling at m=24-25 corresponds to the appearance of persistent wide components.** These are F_m components of width 0.3-0.5 that certain orbit points keep hitting. The oversampling comes from the orbit being quasi-periodic with period close to theta ~ 0.301, and some orbit points persistently landing in these wide components.

## Part C: Pair correlations reveal clustering

Under independence, E[pairs] = C(L,2) * rho_m^2. The actual pair count vs expected:

| m | Pair ratio | Interpretation |
|---|-----------|----------------|
| 5 | 0.36 | Strong negative correlation (repulsion) |
| 10 | 0.78 | Mild negative correlation |
| 15 | 0.16 | Very strong negative correlation |
| 20 | 1.12 | Slight positive correlation |
| 25 | 6.13 | STRONG positive correlation (clustering) |
| 29 | 3.53 | Strong positive correlation |

The pair correlation transitions from negative (repulsive) at small m to positive (clustering) at large m. This mirrors the oversampling pattern: at large m, the hits cluster in groups (consecutive orbit indices hitting F_m together), inflating both N_m and the pair count.

The consecutive hit gaps confirm this: at m=25, gaps are [2,4,1,1,4,14,14,1,1,5,1,1,2,1,8,23] showing many gap-1 pairs (consecutive hits). At m=29, gaps are [1,32,1,6,4,9,23,12,5] with a gap-1 pair early and then wider spacing.

## Part D: Second moment does NOT concentrate

The ratio N_m^2 / E[N_m]^2 should be near 1 if N_m concentrates at its mean. Instead:

- For m < 20: ratio < 1 (N_m is below expectation, consistent with undersampling)
- For m=24-25: ratio ~ 6.4 (N_m is 2.5x expected, so N_m^2 is 6.4x E^2)
- For m=29: ratio ~ 3.9

The second moment method fails because N_m does not concentrate. The variance is comparable to or larger than the mean. This means Markov's inequality (P(N_m > 0) <= E[N_m]) is the best we get from first-moment methods, and E[N_m] > 1 until m=50.

**Conclusion: Pure probabilistic arguments (Borel-Cantelli, Markov) cannot prove N_m = 0 for m < 50.** They can only establish that N_m = 0 "most of the time" for large m.

## Part E: Persistent alpha values (THE MOST IMPORTANT FINDING)

Certain alpha values appear as hits across 14-19 consecutive m values:

| Alpha | # of m-values | Range |
|-------|-------------|-------|
| 0.567 | 19 | m=16-34 |
| 0.353 | 16 | m=12-27 |
| 0.868 | 14 | m=16-29 |
| 0.674 | 14 | m=17-30 |
| 0.588 | 14 | m=20-33 |
| 0.878 | 13 | m=18-30 |
| 0.511 | 9 | m=25-33 |

These are orbit points that keep landing in F_m for many consecutive m values. The alpha ~ 0.567 orbit point hits F_m for 19 consecutive digit counts (m=16 through m=34). This is the "persistent wide component" phenomenon identified in Exp 28.

The orbit point alpha ~ 0.511 corresponds to n=86 (the last known zeroless power). It persists for 9 m-values (m=25-33), which is consistent with 2^86 having 26 digits and being zeroless.

**These persistent orbit points are the SOLE source of the oversampling.** They land in wide components of F_m that shrink slowly with m. The finiteness proof must show that even these persistent orbit points eventually leave F_m.

## Part F: Wide vs narrow component decomposition

| m | N_m | Wide (>0.01) | Narrow (<0.01) | E[N_m] |
|---|-----|-------------|---------------|--------|
| 10 | 12 | 11 | 1 | 13.2 |
| 15 | 5 | 5 | 0 | 11.4 |
| 20 | 10 | 9 | 1 | 9.1 |
| 25 | 17 | 12 | 5 | 6.7 |
| 29 | 10 | 7 | 3 | 5.1 |

The vast majority of hits are in wide components (width > 0.01). At m=29, 7 of 10 hits are in components wider than 0.01, and the widest is 0.43. The narrow hits (width < 0.01) are increasing in proportion (from 1/12 at m=10 to 3/10 at m=29), suggesting that eventually all surviving components will be narrow and easily missed.

## Part G: The critical m=50 threshold

E[N_m] first drops below 1 at **m = 50**. This is the earliest m where Markov's inequality gives P(N_m > 0) < 1 (under uniform distribution). With the ~2x oversampling factor for theta = log10(2), the effective threshold where E_theta[N_m] < 1 would be around m ~ 55-60.

The tail sums show:
- Expected number of m-values with N_m > 0 beyond m=80 is 0.72 (under uniform)
- Expected number beyond m=100 is 0.11
- Expected number beyond m=150 is 0.0008

Even with 2x oversampling: beyond m=100, the expected surviving m-values count is ~ 0.22, suggesting N_m = 0 for all m > 100 with very high probability (under mild regularity).

## Implications for the Proof

1. **First moment alone is insufficient for m < 50.** E[N_m] > 1 until m=50, so Markov's inequality cannot prove N_m = 0 in this range. The actual finiteness at m=27 (N_m = 10, the last m with verifiable hits) cannot be proved by probabilistic methods.

2. **The oversampling is structured, not random.** It comes from ~6-7 persistent orbit points that track wide F_m components. A proof must either:
   (a) Show these wide components eventually narrow below orbit spacing, or
   (b) Show the orbit points drift away from the component centers as m increases.

3. **The coboundary approach remains the best path.** The bounded discrepancy in the transition zone (Exp 25) is precisely what overcomes the oversampling: even if some orbit points cluster in F_m, the total count is bounded by 2*||g_m||_inf + L_m * ||epsilon_m||, and once this bound drops below 1, N_m = 0.

4. **A hybrid argument is possible:** Use coboundary/bounded discrepancy for m < 80, and first-moment (Markov) for m >= 80 (where E[N_m] < 0.72 even with 2x oversampling). This would reduce the problem to: prove bounded discrepancy holds in the transition zone for finitely many m values (m=27 to m=80).
