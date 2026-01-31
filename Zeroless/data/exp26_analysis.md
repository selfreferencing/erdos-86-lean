# Experiment 26 Analysis: Denjoy-Koksma and the Transition Zone

## Central Question

Exp 25 showed the transition zone discrepancy |D_m(L)| < 11 for all m = 2..27, where L = ceil(C*m). The standard Denjoy-Koksma inequality on the circle gives a bound of V(f_m) ~ 9^m, which is useless. Why is the actual discrepancy O(1)?

## Part A: Orbit Variation vs Circle Variation

Both grow exponentially, so orbit variation does NOT explain the bounded discrepancy.

| m | T_m | orbit_var | circle_var | ratio |
|---|-----|-----------|------------|-------|
| 2 | 20 | 2 | 4 | 0.50 |
| 3 | 100 | 18 | 36 | 0.50 |
| 4 | 500 | 114 | 196 | 0.58 |
| 5 | 2,500 | 658 | 1,164 | 0.57 |
| 6 | 12,500 | 3,574 | 6,230 | 0.57 |
| 7 | 62,500 | 18,698 | 30,390 | 0.62 |
| 8 | 312,500 | 95,312 | 156,738 | 0.61 |

The orbit variation is consistently ~55-60% of the circle variation. The ratio is NOT decreasing toward zero. Both grow as ~ rho_m * T_m ~ 0.9^m * 5^m ~ (4.5)^m. The factor-of-2 reduction from orbit ordering is structurally interesting (the orbit visits adjacent regions less often than the circle ordering), but irrelevant for bounding the transition zone discrepancy.

**Verdict:** Orbit variation cannot explain the O(1) discrepancy. Both variations grow exponentially.

## Part B: Per-Digit Sequential Filtering

The sequential filtering reveals how discrepancy accumulates digit by digit.

**Key pattern:** Lower digits (1-5) tend to produce POSITIVE discrepancy (more survivors than expected), while upper digits (6+) produce NEGATIVE discrepancy (fewer survivors than expected). The total discrepancy is a cancellation between these two effects.

At m=15, L=50: After digit 5, survivors = 37 (expected 29.5, disc = +7.5). After digit 15, survivors = 2 (expected 10.3, disc = -8.3). The positive excess from lower digits is wiped out and reversed by the upper digit bias.

At m=20, L=67: Similar pattern. Positive disc builds to +10 by digit 4, then erodes through upper digits to -2.1 at digit 20.

**Mechanism:** Lower digits have close-to-uniform distribution (P(zero) ~ 0.1) or even slight underrepresentation of zeros, producing positive discrepancy. Upper digits are strongly biased toward zero (the leading-zero mechanism from Exp 16/20b), producing large negative discrepancy. The two effects partially cancel, leaving a residual of order O(1) to O(10).

## Part C: Discrepancy Profile D_m(L) for L = 1..200

**Within the transition zone (L <= L_trans):** Discrepancy builds gradually from 0 and stays bounded. At m=5, L_trans=17: max |disc| = 5.6. At m=10, L_trans=34: max |disc| = 7.7. At m=20, L_trans=67: max |disc| = 5.8. At m=25, L_trans=84: max |disc| = 4.7.

**Beyond the transition zone:** Discrepancy continues growing, reaching |disc| ~ 13-18 by L=200 for various m.

**The key observation:** The discrepancy at L_trans is always a fraction of the maximum over larger L. The transition zone is "protected" by its shortness.

## Part D: Random Walk Comparison

The ratio |actual_disc| / sqrt(L * rho * (1-rho)) measures how the actual discrepancy compares to an i.i.d. Bernoulli random walk:

| m range | typical ratio | interpretation |
|---------|--------------|----------------|
| 2-5 | 1.6-4.1 | actual disc > random walk by 2-4x |
| 6-10 | 1.4-3.5 | similar |
| 11-17 | 1.7-3.5 | peak at m=13 (ratio 3.5) |
| 18-22 | 0.8-2.1 | approaches random walk scale |
| 23-27 | 1.0-2.5 | moderate excess |

The actual discrepancy is typically 1-4x the random walk scale. This means the digit values ARE correlated (not i.i.d.), but the correlation only amplifies the discrepancy by a bounded factor, not an exponentially growing one.

**Verdict:** The orbit sequence is "close to random" at the scale of the transition zone, with correlations producing a bounded multiplicative factor. The RW scale sqrt(L * rho) ~ sqrt(3.3m * 0.9^m) -> 0, so even a constant multiplicative factor keeps the discrepancy bounded.

## Part E: Convergent Denominator Analysis

The discrepancy at convergent denominators of theta = log10(2) confirms Exp 25's finding:

- At q_2 = 10: disc ~ -4 to -5 (moderate, within transition zone range)
- At q_3 = 93: disc ~ -3 to -8 (still moderate)
- At q_4 = 196: disc ~ -10 to -17 (growing)
- At q_8 = 28738: disc ~ -64 to -76 (large, the resonance peak)
- At q_10 = 70777: disc ~ -130 to -137 (very large)

The convergent denominators q_2 = 10 and q_3 = 93 bracket the transition zone. For m <= 27, L_trans <= 90 < 93, so the transition zone never reaches q_3. The first "dangerous" convergent that could cause large discrepancy is q_3 = 93.

**The protection mechanism is now clear:** L_trans < q_3 for all m <= 27 (and for m >= 28, L_trans ~ 93 but rho_m ~ 0.9^m is negligibly small, so even disc ~ 10 is harmless since 10 >> rho_m * L ~ 0).

## Part F: Star Discrepancy

| m | L | D_L* | D_L* * L |
|---|---|------|----------|
| 5 | 17 | 0.107 | 1.82 |
| 10 | 34 | 0.087 | 2.95 |
| 15 | 50 | 0.059 | 2.94 |
| 20 | 67 | 0.043 | 2.86 |

D_L* * L is approximately constant (~2.9). This means D_L* ~ 3/L, consistent with the Ostrowski bound for bounded-type irrationals. The Koksma-Hlawka bound gives |disc| <= V(f) * D_L* ~ 9^m * 3/L ~ 9^m / m, still terrible.

**Verdict:** Star discrepancy behaves normally (~ 3/L). The exponential variation V(f_m) is the obstacle for Koksma-Hlawka, and no amount of good equidistribution fixes it.

## Part G: Orbit Transitions in the Transition Zone (KEY FINDING)

This is the most revealing part of the experiment.

| m | L | transitions | max_run_0 | max_run_1 |
|---|---|-------------|-----------|-----------|
| 5 | 17 | 3 | 9 | 4 |
| 10 | 34 | 4 | 21 | 7 |
| 15 | 50 | 4 | 34 | 1 |
| 20 | 67 | 9 | 47 | 2 |
| 25 | 84 | 4 | 56 | 1 |
| 26 | 87 | 2 | 60 | 1 |
| 27 | 90 | 0 | 90 | 0 |

**The transition zone has extremely few transitions.** For m >= 13, there are only 4-10 transitions in L ~ 40-90 steps. At m=27, there are ZERO transitions (the entire transition zone is all 0s: no orbit element is a survivor).

The max run of 0s grows linearly with L (roughly 0.7*L for large m), meaning most of the transition zone is one long consecutive run of non-survivors, occasionally interrupted by 1-2 isolated survivors.

**Why this matters:** A function with V transitions in L steps has "effective variation" V, not the circle variation 9^m. The Birkhoff sum over such a function is bounded by V + 1 (the discrepancy can change by at most 1 at each transition, plus the accumulated drift). With V ~ 4-10 and L*rho ~ 3-7, the discrepancy is naturally bounded by ~ V + L*rho ~ 10-20.

**This is the mechanism.** The transition zone discrepancy is bounded because f_m has only O(1) transitions along the orbit in the transition zone. The circle variation 9^m is irrelevant because it counts transitions along the WRONG ordering (the [0,1) ordering, not the orbit ordering). The orbit ordering compresses the enormous circle variation into a few isolated blips within the transition zone.

**Why so few transitions?** The orbit visits {i*theta mod 1} for i = 0, 1, ..., L-1. For small i, the orbit is near-monotone (since theta ~ 0.301, the orbit steps roughly 0.301 per step around the circle, visiting ~ L/3 consecutive regions). The zeroless set F_m occupies measure rho_m ~ 0.9^m, arranged in ~ 9^m tiny intervals each of length ~ 10^{-m}. For L ~ 3m, the orbit visits ~ 3m points spaced ~ 0.3 apart. The chance that consecutive orbit points straddle a boundary of F_m is ~ 9^m * (1/0.3) * 10^{-m} ~ (9/10)^m / 0.3 ~ 3 * 0.9^m ~ 0. So transitions are exponentially rare, and only O(1) occur in L steps.

## Part H: Martingale Increment Discrepancies

Each digit r contributes a discrepancy increment = S_r(L) - 0.9 * S_{r-1}(L), representing the deviation from the expected 90% survival at digit r.

| m | total increment disc | Final N_m(L) | rho*L |
|---|---------------------|-------------|-------|
| 8 | -2.60 | 9 | 11.62 |
| 12 | -3.00 | 6 | 11.30 |
| 16 | -7.50 | 2 | 10.01 |
| 20 | -0.90 | 6 | 8.15 |
| 25 | -5.40 | 2 | 6.03 |

Individual digit increments are each O(1) (ranging from about -4.7 to +8.4). The total is a sum of m terms of O(1), but with cancellation between lower digits (positive) and upper digits (negative). The total stays bounded, not growing as m increases.

**This confirms the per-digit mechanism:** Each digit contributes bounded discrepancy, and the total cancels rather than accumulates.

## Synthesis: Three Converging Explanations

### Explanation 1: Low orbit variation (Part G)
The function f_m has only O(1) transitions along the orbit in the transition zone. This directly bounds the Birkhoff sum discrepancy, bypassing the enormous circle variation entirely.

### Explanation 2: Per-digit cancellation (Parts B, H)
Lower digits create positive discrepancy, upper digits create negative discrepancy. The two effects partially cancel, keeping the total O(1).

### Explanation 3: Convergent denominator protection (Part E)
The transition zone length L_trans < q_3 = 93 means the orbit hasn't completed enough near-periods to build up resonant discrepancy. The first dangerous convergent is beyond the transition zone.

**These three explanations are not independent.** The low orbit variation (Exp 1) is CAUSED by the short length relative to convergent denominators (Exp 3): the orbit points are spread roughly uniformly in [0,1) without near-repetitions, so consecutive points rarely straddle the same tiny zero-interval boundary. The per-digit cancellation (Exp 2) is a consequence of the orbit structure interacting differently with lower vs upper digit conditions.

## Implications for the Proof

### The correct lemma to prove

**Restricted Low-Variation Lemma:** For f_m = indicator of F_m (the zeroless set) and the orbit x_i = frac(i*theta), the number of transitions in (f_m(x_0), f_m(x_1), ..., f_m(x_{L-1})) is O(1) for L <= C*m.

This is equivalent to: the orbit of length L crosses only O(1) boundaries of F_m. Since F_m has ~9^m boundary points and L ~ 3m orbit points with spacing ~1/3, the expected number of boundary crossings is ~ L * (boundary density) = 3m * 9^m * 10^{-m} = 3m * 0.9^m -> 0.

This means: for large m, the orbit in the transition zone crosses ZERO boundaries of F_m with probability -> 1. Either all L orbit points are in F_m (improbable since |F_m| ~ 0.9^m is tiny) or all are outside F_m (the generic case, giving N_m(L) = 0).

### The finiteness argument, made explicit

1. For m >= 28, L_trans < 93 and rho_m < 0.9^28 < 0.06.
2. The expected number of F_m-boundary crossings in L_trans steps is < 3m * 0.9^m < 1 for m >= 28.
3. So with high probability, the orbit in the transition zone is entirely outside F_m (zero survivors) or entirely inside one component (which can't happen since no component spans a length-0.3 interval for large m).
4. Therefore N_m(L_trans) = 0 for all large m, i.e., no n in the transition zone produces a zeroless 2^n.

### What remains to make this rigorous

The "high probability" in step 3 needs to be replaced by a CERTAINTY. This requires:
- An explicit bound on the measure of alpha-values for which the orbit crosses a boundary of F_m in L_trans steps
- Showing that frac(m * log10(2)) is not in this exceptional set for any large m

This is essentially the same Diophantine input identified by GPT 4B: a restricted small-divisor bound ensuring log10(2) doesn't have pathological interactions with the digit-boundary structure.

### Connection to Exp 25's restricted bounded discrepancy

Exp 25 showed |disc| < 11 in the transition zone. Exp 26 now explains WHY: the orbit has only O(1) transitions, and the O(1) discrepancy is simply the difference between actual survivors and expected survivors, which is bounded by the number of transitions plus a drift term proportional to L * rho_m.

The precise relationship: if there are V transitions in L steps, the discrepancy satisfies |disc| <= V + L * rho_m + 1. With V ~ 4-10 and L * rho_m ~ 3-7, this gives |disc| <= 15-18, consistent with the observed bound of 11.
