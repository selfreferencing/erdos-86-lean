# Experiment 31 Analysis: Boundary Point Complexity

## Central Question

For the orbit points that hit F_m, what are the nearest boundary integers of their component? Do these boundary integers factor into small primes {2,3,5,7}? This is the critical feasibility test for the Baker step in the resonance template program.

## Part A: Boundary Identification

For each hit at level m, the nearest boundary of the containing component was identified. "Boundary" here means the nearest integer with a zero digit (marking the edge of the gap in F_m where the hit resides).

94 boundary integers were examined across m=2..20.

## Part B: Factorization Results

**Only 5 out of 94 boundary integers (5.3%) are {2,3,5,7}-smooth.**

The smooth cases occur exclusively at small m (m=2,3) where boundary integers are small enough to factor entirely into small primes. For m >= 4, no boundary integer is {2,3,5,7}-smooth.

## Part C: Complexity Growth

| m | #hits | #smooth | max_prime | avg_distinct_primes | max_distinct_primes |
|---|-------|---------|-----------|--------------------|--------------------|
| 2 | 5 | 3 | 7 | 2.2 | 3 |
| 3 | 3 | 2 | 7 | 2.0 | 3 |
| 4 | 4 | 0 | 41 | 2.8 | 3 |
| 5 | 7 | 0 | 41 | 3.3 | 5 |
| 6 | 4 | 0 | 521 | 3.2 | 4 |
| 7 | 5 | 0 | 3529 | 3.4 | 4 |
| 8 | 9 | 0 | 14713 | 3.7 | 5 |
| 9 | 9 | 0 | 65537 | 4.1 | 6 |
| 10 | 9 | 0 | 65537 | 4.6 | 7 |

The maximum prime factor grows rapidly with m (from 7 at m=2 to 65537 at m=9-10), as does the number of distinct prime factors. For m >= 6, boundary integers routinely have prime factors in the thousands or larger.

## Part D: Persistent Boundary Structure

Tracking boundary integers for persistent orbit indices across m levels reveals no special structure. The boundary integers grow in magnitude and complexity as m increases, with no tendency toward smooth factorization.

## Verdict

**Strategy D (boundary Baker) is BLOCKED.** The naive Baker/Matveev approach requires boundary integers n_0 to be {2,3,5,7}-smooth so that log10(n_0) can be expressed as a linear form in logarithms of algebraic numbers. Since 95% of boundary integers fail this test, the strategy cannot apply to the generic case.

**Recommendation: Pivot to Strategy E (cluster forcing + direct Baker on theta).** The cluster forcing lemma (Conclusion 27) does NOT require smooth boundaries. It uses pigeonhole on component positions to force small ||h*theta|| for h = n_i - n_j (a difference of orbit indices), then applies Baker directly to theta = log10(2) = log(2)/log(10), which IS a ratio of logarithms of algebraic numbers. Baker gives ||h*theta|| >= C/h^A, contradicting the forced proximity for large enough m.

## New Conclusion

**Conclusion 30.** Boundary integers of F_m components at hit points are NOT {2,3,5,7}-smooth for m >= 4 (only 5.3% smooth overall, all at m <= 3). Strategy D (applying Baker to boundary points beta = log10(n_0)) is blocked by the complexity barrier: n_0 has large prime factors and log10(n_0) cannot be expressed as a linear form in logs of small primes. The viable alternative is Strategy E (cluster forcing), which applies Baker directly to theta = log10(2) via the pigeonhole mechanism on orbit index differences, bypassing the boundary complexity issue entirely (Exp 31).
