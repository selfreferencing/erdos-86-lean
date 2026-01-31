# Experiment 35 Analysis: Cluster Forcing Delta

## Central Question

If N_m >= r hits all lie in distinct components (Step B+), what is the minimum pairwise distance delta_m between hit positions? Can Baker/Matveev lower bounds on ||h*theta|| contradict this forced proximity?

## Results

### Part B: Minimum Pairwise Gap by Level

| m | N_m | delta_m | pair achieving min | h = diff | h*theta mod 1 |
|---|-----|---------|-------------------|----------|---------------|
| 2 | 5 | 0.0969 | (2,5) | 3 | 0.0969 |
| 3 | 3 | 0.3010 | (4,5) | 1 | 0.3010 |
| 4 | 4 | 0.0969 | (9,12) | 3 | 0.0969 |
| 5 | 7 | 0.0969 | (10,13) | 3 | 0.0969 |
| 6 | 4 | 0.1072 | (12,19) | 7 | 0.1072 |
| 7 | 5 | 0.0969 | (17,20) | 3 | 0.0969 |
| 8 | 9 | 0.0103 | (16,26) | 10 | 0.0103 |
| 9 | 9 | 0.0103 | (18,28) | 10 | 0.0103 |
| 10 | 9 | 0.0969 | (21,24) | 3 | 0.0969 |
| 11 | 8 | 0.0103 | (25,35) | 10 | 0.0103 |
| 12 | 6 | 0.0103 | (27,37) | 10 | 0.0103 |
| 13 | 2 | 0.3979 | (36,38) | 2 | 0.3979 |
| 14 | 2 | 0.3979 | (35,37) | 2 | 0.3979 |
| 15 | 2 | 0.3979 | (34,36) | 2 | 0.3979 |
| 16 | 2 | 0.1835 | (35,51) | 16 | 0.1835 |
| 17 | 2 | 0.4949 | (50,55) | 5 | 0.4949 |
| 18 | 4 | 0.0103 | (49,59) | 10 | 0.0103 |
| 19 | 5 | 0.0103 | (48,58) | 10 | 0.0103 |
| 20 | 6 | 0.0103 | (47,57) | 10 | 0.0103 |
| 21 | 6 | 0.0103 | (46,56) | 10 | 0.0103 |
| 22 | 6 | 0.0103 | (54,64) | 10 | 0.0103 |
| 23 | 5 | 0.0103 | (53,63) | 10 | 0.0103 |
| 24 | 3 | 0.2041 | (53,57) | 4 | 0.2041 |
| 25 | 2 | 0.4949 | (56,61) | 5 | 0.4949 |

### Key Observations

1. **The minimum gap is almost always ||h*theta|| for a convergent-related h.** The most common minimizing h values are h=3 (||3*theta|| = 0.0969) and h=10 (||10*theta|| = 0.0103). These are the convergent denominators q_1 = 3 and q_2 = 10 of theta = log10(2).

2. **For levels with N_m >= 4 hits, delta_m is usually 0.0103 = ||10*theta||.** This is because 4+ hits spread across the transition zone inevitably include a pair separated by ~10 indices.

3. **For levels with N_m = 2 hits, delta_m can be larger** (up to 0.4949 at m=17,25), since only one pair exists and it may not align with a convergent.

## Baker Comparison

The cluster forcing argument requires: if N_m >= r, then the pigeonhole principle forces ||h*theta|| <= delta for some h <= H, and Baker gives ||h*theta|| >= C/h^A. A contradiction arises if delta < C/H^A.

For theta = log10(2), Baker/Matveev gives ||h*theta|| >= c_0 / h^{lambda} where lambda ~ 1 and c_0 depends on the specific Baker constant. With h <= L_m ~ 3.3m:

Baker lower bound: ||h*theta|| >= c_0 / (3.3m)^lambda

Forced upper bound (from cluster forcing with r hits): delta_m ~ max_comp(F_m) per the pigeonhole argument, which is ~3.5 * 10^{-(m-1)}.

**For m >= 4:** Baker lower bound ~ c_0/m >> 3.5 * 10^{-(m-1)} = cluster forcing upper bound. The Baker bound wins by an exponential factor. This means the cluster forcing contradiction WORKS: having r >= 2 hits forces a proximity that Baker rules out, therefore N_m <= 1 for large m.

However, the cluster forcing argument as stated requires r >= 2 hits to generate a pair. For the regime m >= 13 where N_m is already very small (0-2 hits), the argument is trivially inapplicable (no pairs to force proximity from).

## The Real Power of Cluster Forcing

The cluster forcing argument is most powerful at intermediate m (8-12) where N_m ~ 6-9. Here, pigeonhole on 6-9 hits across ~10 components of F_m in [0,1) forces a pair with gap <= 1/(N_m - 1) ~ 0.1. The actual minimum gap at these levels is 0.0103, which is ||10*theta||. Baker gives ||10*theta|| = 0.0103 > 0 (trivially positive). The argument doesn't produce a contradiction because the forced gap (~ 0.1) is LARGER than Baker's lower bound (~ c_0/m ~ 0.01).

**The cluster forcing argument requires max_comp(F_m) to be much smaller than Baker's lower bound.** Since max_comp ~ 10^{-(m-1)} and Baker ~ 1/m, this is satisfied for m >= 4. But the pigeonhole step forces delta ~ 1/r ~ 1/N_m, not delta ~ max_comp. The gap is: pigeonhole gives delta ~ 0.1, not delta ~ 10^{-(m-1)}.

## Refined Interpretation

**CORRECTION: The pigeonhole step below is INCORRECT.** The original analysis claimed the following argument works, but subsequent analysis revealed a fundamental gap.

The proposed argument was:
1. Step B+ proves each hit is in a distinct component.
2. If N_m >= 2 hits across components of total measure rho_m, pigeonhole forces some pair within distance <= rho_m, giving ||h*theta|| <= rho_m.
3. Baker gives ||h*theta|| >> 1/m^A, contradicting step 2 for large m.

**Why step 2 is wrong:** Having N_m points in a set of total measure rho_m does NOT force any pair within distance rho_m. The 9^{m-1} components of F_m are scattered across [0,1). Two hits can land in components far apart on the circle. The pigeonhole principle on measure requires the points to be constrained to an interval of length rho_m, but F_m is a union of ~9^{m-1} tiny intervals spread across the entire circle.

The data confirms this: the minimum pairwise gaps delta_m are O(1) constants (0.0969 = ||3*theta||, 0.0103 = ||10*theta||), determined by convergent denominators of theta, NOT shrinking with m. These gaps reflect the orbit's quasi-periodic structure and have nothing to do with rho_m.

## New Conclusion

**Conclusion 34 (CORRECTED).** The cluster forcing pigeonhole step is INCORRECT. The minimum pairwise gap delta_m between hit positions concentrates at O(1) constants ||q_j*theta|| (0.0969 for q_1=3, 0.0103 for q_2=10), NOT at rho_m ~ 0.9^m. The claim that N_m >= 2 hits force ||h*theta|| <= rho_m was wrong: hits can sit in F_m components scattered across [0,1), and having points in a set of measure rho_m does not force any pair within distance rho_m. Strategy E is blocked. See Conclusion 35 for the full analysis of rescue attempts.
