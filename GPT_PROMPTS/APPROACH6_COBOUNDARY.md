# GPT Prompt: o(1) Coboundary / Low-Frequency Fourier Mass Approach to Zeroless Powers of 2

## Role

You are a research mathematician specializing in ergodic theory of circle rotations, Fourier analysis on the torus, bounded remainder sets (BRS), coboundary decompositions for irrational rotations, and Baker-type linear forms in logarithms. Your expertise includes the Kesten-Oren BRS theory, Denjoy-Koksma inequalities, shrinking target problems (Kurzweil, Kim, Tseng), and effective equidistribution. I need your help proving a specific o(1) discrepancy estimate for a structured shrinking target.

## Problem Background

**The Conjecture.** The set A = {n >= 1 : 2^n has no digit 0 in base 10} is finite. Computationally, A has 41 elements with largest element 86.

**What We Have Proved.**
1. A has density zero (elementary, using parity-balance in the 5-adic orbit).
2. **Step B (PROVED):** For all m >= 2, max_component(F_m) < theta = log10(2), where F_m is the "zeroless set" in [0,1). No single component of F_m can contain two consecutive orbit points.
3. **Step B+ (PROVED for m >= 4):** max_component(F_m) < min_{1 <= k <= L_m} ||k*theta|| for all m >= 4. No two orbit points in the transition zone share a component of F_m, regardless of their lag separation. Every orbit hit is isolated in a distinct component.
4. **Quasi-independence (confirmed, Exp 32):** mu(F_m cap (F_m - h*theta)) / mu(F_m)^2 is bounded by 1.58 for lag h=1 and within [0.97, 1.04] for lags h >= 3.
5. **O(1) danger cylinders (confirmed, Exp 30):** At most 9 distinct components of F_m are hit by orbit points, across all tested m.
6. **Borel-Cantelli (metric finiteness):** sum_m L_m * mu(F_m) = sum_m ceil(m/theta) * 0.9^{m-1} < infinity. For Lebesgue-a.e. theta, the orbit hits F_m only finitely many times.

**What Has Been Eliminated.** Six strategies have been tested and blocked:
1. All Fourier magnitude methods (L1, pointwise, l^p Holder, additive Fourier): magnitudes don't decay.
2. Sieve methods: reduce to short-interval equidistribution which fails empirically.
3. Thread-to-approximation (Strategy B): survival doesn't force good rational approximation.
4. Resonance template + boundary Baker (Strategy D): boundary integers of F_m are not smooth; Baker inapplicable.
5. Cluster forcing + pigeonhole + Baker (Strategy E): the pigeonhole step is WRONG. Having N_m >= 2 points in a set of measure rho_m does NOT force any pair within distance rho_m. Hits scatter across [0,1).
6. Ostrowski renormalization + Denjoy-Koksma (Strategy C): J-digit approximation requires J ~ m, making DK bounds useless.

## The Setup

### Definitions

- **theta = log10(2) ~ 0.30103.** An irrational rotation on [0,1). CF expansion: [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117, ...]. Convergent denominators: q_0=1, q_1=3, q_2=10, q_3=93, q_4=196, ...

- **F_m (the zeroless set):** {alpha in [0,1) : the m-digit number with significand 10^alpha has all digits nonzero}. Equivalently, F_m is the set of alpha such that floor(10^{alpha+k-1}) mod 10 != 0 for all k = 1, ..., m. It is a union of exactly 9^{m-1} connected components, each of width ~10^{-(m-1)} in alpha-space. Its Lebesgue measure is rho_m ~ (9/10)^{m-1}.

- **Transition zone:** For digit count m, the candidates are n with D(2^n) = m, giving L_m = ceil(m/theta) ~ ceil(3.32*m) orbit points. These are {frac(i*theta + c_m)} for i = 0, ..., L_m - 1, where c_m = frac(m*theta).

- **N_m = #{i < L_m : frac(i*theta + c_m) in F_m}:** The number of m-digit zeroless powers of 2. The conjecture is: N_m = 0 for all large m.

### What the metric theory gives

E[N_m] = L_m * rho_m ~ ceil(m/theta) * 0.9^{m-1} ~ 3.3m * 0.9^m -> 0.

By Borel-Cantelli, for a.e. theta, N_m = 0 for all sufficiently large m. The entire problem is certifying this for the specific value theta = log10(2).

### Why exact coboundary (BRS) is ruled out

An exact bounded coboundary for 1_{F_m} (i.e., 1_{F_m}(x) - rho_m = g_m(x + theta) - g_m(x) + epsilon_m(x) with ||g_m||_inf = O(1) uniformly in orbit length) is equivalent to F_m being a bounded remainder set (BRS) for rotation by theta. By Kesten's theorem (1966), a single interval [0, beta) is BRS iff beta is in Z + theta*Z. By Oren's generalization, finite unions of intervals satisfy a rigid pairing/permutation condition. F_m (a union of 9^{m-1} micro-intervals with digit-fractal structure) almost certainly does not satisfy these conditions. Exact coboundary is ruled out.

## The Target Estimate

**o(1) discrepancy on the transition zone.** We need: for all sufficiently large m,

|N_m - L_m * rho_m| < 1/2.

Since L_m * rho_m -> 0, this forces N_m = 0 for large m.

The coboundary approach decomposes 1_{F_m} into its Fourier series on [0,1):

1_{F_m}(x) = rho_m + sum_{k != 0} hat{1_{F_m}}(k) * e^{2*pi*i*k*x}

The Birkhoff sum is:

N_m = sum_{j=0}^{L_m - 1} 1_{F_m}(frac(j*theta + c_m)) = L_m * rho_m + sum_{k != 0} hat{1_{F_m}}(k) * e^{2*pi*i*k*c_m} * D_{L_m}(k*theta)

where D_L(alpha) = sum_{j=0}^{L-1} e^{2*pi*i*j*alpha} = (e^{2*pi*i*L*alpha} - 1)/(e^{2*pi*i*alpha} - 1).

The error is bounded by:

|N_m - L_m * rho_m| <= sum_{k != 0} |hat{1_{F_m}}(k)| * |D_{L_m}(k*theta)|

Using |D_L(alpha)| <= 1/(2*||alpha||) (standard bound), this becomes:

|N_m - L_m * rho_m| <= sum_{k != 0} |hat{1_{F_m}}(k)| / (2*||k*theta||)

**THE KEY ESTIMATE.** We need:

**S_m := sum_{k != 0} |hat{1_{F_m}}(k)| / ||k*theta|| = o(1) as m -> infinity.**

## What We Know About Each Factor

### The denominators: ||k*theta||

Baker's theorem on linear forms in logarithms gives: for theta = log10(2) = log(2)/log(10), and for all nonzero integers k,

||k*theta|| >= C_0 / |k|^{lambda}

where C_0 and lambda are effective constants. For a linear form in two logarithms (log 2 and log 10), Baker-Wustholz gives lambda = 1 with an explicit (large) constant. The key point: the denominators decay at most polynomially.

For the low-frequency terms |k| <= H = poly(m), the sum over denominators is at most:

sum_{|k|=1}^{H} 1/||k*theta|| <= sum_{k=1}^{H} |k|^{lambda} / C_0 ~ H^{lambda+1} / C_0

With lambda = 1 and H = poly(m), this is poly(m).

### The numerators: |hat{1_{F_m}}(k)|

For the DC term: hat{1_{F_m}}(0) = rho_m = (9/10)^{m-1}.

For nonzero k, the Fourier coefficient is:

hat{1_{F_m}}(k) = integral_0^1 1_{F_m}(x) * e^{-2*pi*i*k*x} dx

**Product structure.** F_m is defined by m-1 independent digit conditions (digits 2 through m must be nonzero). In x = 10^alpha coordinates, each digit condition is a function of a different decimal position. This suggests:

hat{1_{F_m}}(k) should have size related to the product structure.

**The heuristic.** If the digit conditions were "independent" in the Fourier sense, then |hat{1_{F_m}}(k)| ~ rho_m = 0.9^{m-1} for all |k| << 10^{m-1}. This is because the individual digit indicators have Fourier support at high frequencies (~10^j for digit j), while low-frequency k << 10^{m-1} cannot resolve individual digit structure.

**If the heuristic holds:** S_m ~ sum_{|k|=1}^{H} rho_m / ||k*theta|| ~ rho_m * H^{lambda+1} ~ 0.9^m * poly(m) -> 0. Done.

### What we know from experiments

1. The max non-DC additive Fourier coefficient |hat{f_m}(a)|/rho_m = 0.2154 for k=1 (depth-1 in 5-adic structure), dropping to ~0.088 for deeper levels. This is for the 5-ADIC Fourier basis on Z/5^m Z, not the continuous circle Fourier basis.

2. The l^1 norm sum |hat{f_m}(k)| grows ~2.13x per level in the multiplicative basis. But this is a different Fourier basis from the continuous one.

3. The actual Birkhoff sum error |N_m - L_m*rho_m| is O(1) (bounded by 11 for m = 2..27), reaching 0 at m=27. The error IS o(1) empirically. The question is proving it.

## Questions for You

1. **Is the Fourier coefficient bound |hat{1_{F_m}}(k)| ~ rho_m for |k| <= poly(m) true?** Can you prove or disprove this using the product structure of F_m (intersection of m-1 digit conditions)? Each digit condition "digit j != 0" is a union of 9 intervals of width 1/10 in the j-th decimal place. The Fourier coefficients of each individual condition are standard (Bohr sets / digital functions). What happens to their intersection?

2. **Is there a standard result for Fourier coefficients of intersections of digital conditions?** The Mauduit-Rivat framework handles sums of digital functions. Does it give bounds on the Fourier transform of the PRODUCT (intersection) of digital conditions? The relevant reference may be Mauduit-Rivat (JEMS 2010, Annals 2010) on the sum-of-digits function, or Maynard's (Annals 2019) work on primes with restricted digits.

3. **Can the problem be reformulated as a shrinking target problem where existing results apply?** Our setup: rotation by theta on the circle, targets F_m with mu(F_m) ~ 0.9^{m-1}. The targets are not monotone (F_{m+1} is not a subset of F_m in general), but they are nested in a 5-adic sense. Does Kurzweil 1955 or the more recent Kim-Tseng (2007) framework give individual-theta results for targets of this type?

4. **Is there a truncation strategy?** Instead of summing over ALL k != 0, could we split the sum S_m into:
   - |k| <= H (low frequency): bound by rho_m * H^{A+1}
   - |k| > H (high frequency): bound by sum |hat{1_{F_m}}(k)| / ||k*theta|| using Parseval or a weaker Fourier bound
   What is the optimal H, and does the high-frequency tail contribute o(1)?

5. **Does the specific arithmetic of theta = log10(2) help beyond Baker?** The CF of theta has partial quotients [3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, ...]. This is not bounded type, but the partial quotients are moderate. Does the specific CF structure (particularly a_13 = 18 and any larger partial quotients beyond our computation range) affect the viability of the estimate?

6. **Is there a simpler formulation that avoids Fourier analysis entirely?** For example: can the shrinking target result be proved by a direct geometric argument about how the orbit {frac(j*theta)} interacts with the Cantor-dust structure of F_m? The Cantor-dust has all components of width ~10^{-(m-1)} and total measure ~0.9^{m-1}. The orbit has ~3m points spaced ~0.3 apart (with finer structure from convergent denominators). Is there a covering argument?
