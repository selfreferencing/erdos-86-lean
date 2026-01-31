# GPT Prompt: Exponential Sum / Bourgain Approach to Zeroless Powers of 2

## Role

You are a research mathematician specializing in exponential sums, harmonic analysis on finite groups, and the Bourgain school of additive combinatorics. I need your help applying exponential sum techniques to prove finiteness in the Erdos 86 conjecture.

## Problem Background

**The Conjecture.** The set A = {n >= 1 : 2^n has no digit 0 in base 10} is finite. Computationally, A has 35 elements with largest element 86.

**What We Have Proved.** The set A has density zero, via the 5-adic orbit structure. Full machinery described below.

**What remains.** Prove that for large m, no n in the "transition zone" survives at level D(n) (its digit count). This reduces to bounding the count of survivors in a short initial interval of the orbit.

## The Algebraic Structure

### The orbit and its period

The sequence 2^n mod 10^m for n >= m is periodic with period T_m = 4 * 5^{m-1} = phi(5^m). Each orbit element has the form x = 2^m * u where u = 2^{n-m} mod 5^m. The key algebraic fact:

**2 is a primitive root mod 5^m for all m >= 1.**

So the orbit {u mod 5^m : n = m, m+1, ...} generates the FULL multiplicative group (Z/5^m Z)^*, and the orbit has period T_m = phi(5^m) = 4 * 5^{m-1}.

### The CRT decomposition

Since 10^m = 2^m * 5^m with gcd(2^m, 5^m) = 1, by CRT:

Z/10^m Z ~ Z/2^m Z x Z/5^m Z

The orbit element x = 2^m * u satisfies:
- x mod 2^m = 0 (since 2^m | x)
- x mod 5^m = 2^m * u mod 5^m (ranges over all of (Z/5^m Z)^* as u does)

**The fundamental asymmetry:**
- Mod 5^m: the orbit is PERFECTLY equidistributed (covers the full group)
- Mod 2^m: the orbit is COMPLETELY degenerate (always 0)

### The digit-zero condition

An orbit element x = 2^m * u is a level-m survivor iff all m digits of x (in base 10) are nonzero. Define:

f_m(u) = 1 if 2^m * u mod 10^m has all digits nonzero, else 0

This is a function on (Z/5^m Z)^*. The survivor count is:

Z_m = sum_{u in (Z/5^m Z)^*} f_m(u)

## The Fourier Analysis

### DFT on the orbit

Since the orbit has period T_m, we can expand f_m via DFT on Z/T_m Z:

f_m(i) = sum_{j=0}^{T_m - 1} F_m(j) * exp(2*pi*i*j*i/T_m)

where F_m(j) = (1/T_m) * sum_{i=0}^{T_m-1} f_m(i) * exp(-2*pi*i*j*i/T_m).

The DC component is F_m(0) = Z_m / T_m = rho_m (survivor density).

### Counting survivors in [0, L)

The count of survivors in the short interval [0, L) is:

|S_m intersect [0, L)| = L * rho_m + sum_{j=1}^{T_m-1} F_m(j) * D_L(j)

where D_L(j) = sum_{i=0}^{L-1} exp(2*pi*i*j*i/T_m) is a geometric sum with |D_L(j)| <= min(L, 1/(2*|sin(pi*j/T_m)|)).

### The naive bound fails

**Experiment 17 data.** The naive error bound sum |F_m(j)| * |D_L(j)| grows exponentially:

| m | L   | Main term L*rho | Error bound | Actual error | Cancellation |
|---|-----|-----------------|-------------|--------------|--------------|
| 3 | 10  | 8.10            | 7.86        | -5.10        | 1.5x         |
| 5 | 17  | 11.14           | 44.12       | -4.14        | 10.7x        |
| 7 | 24  | 12.74           | 217.00      | -7.74        | 28.0x        |
| 9 | 30  | 12.90           | 1007.03     | -3.90        | 258.4x       |

The bound grows at rate ~2.1x per level (doubling), while the actual signed error remains O(1). The cancellation factor (bound/|actual error|) reaches 258x at m=9 and grows exponentially.

### Why the bound fails: L^1 norm growth

The L^1 norm of the non-DC spectrum:

| m | L1(F_m, nonDC) | Growth ratio |
|---|----------------|--------------|
| 2 | 1.17           | -            |
| 3 | 3.21           | 2.74         |
| 4 | 7.41           | 2.31         |
| 5 | 16.28          | 2.20         |
| 6 | 35.05          | 2.15         |
| 7 | 74.77          | 2.13         |
| 8 | 159.18         | 2.13         |
| 9 | 338.55         | 2.13         |

The L^1 norm grows by factor ~2.13 per level. Since the geometric sum |D_L(j)| contributes additional factors, the total error bound grows at ~2.1x.

### Spectral structure

**Experiment 17 data.** The dominant Fourier coefficients have a clean pattern:

At level m, the largest non-DC Fourier coefficient occurs at j = 5^{m-2} with:
- |F_m(5^{m-2})| / rho_m ~ 0.1234 (constant across m)
- The top 10 coefficients all have 5-adic valuation v_5(j) = m-2

**Spectral concentration is low:**

| m | Top 1 | Top 5 | Top 10 | Top 50 | Top 100 |
|---|-------|-------|--------|--------|---------|
| 3 | 6.2%  | 26.1% | 43.4%  | 91.2%  | -       |
| 5 | 2.9%  | 12.4% | 21.2%  | 44.4%  | 55.8%   |
| 7 | 1.7%  | 7.4%  | 12.6%  | 26.5%  | 33.5%   |
| 9 | 1.2%  | 4.9%  | 8.4%   | 17.7%  | 22.3%   |

The spectrum is diffuse: the L^2 energy spreads across many coefficients as m grows. This makes pointwise (L^infinity) bounds on individual F_m(j) insufficient.

### The digit factorization

**Experiment 18 data.** The survivor indicator factors as f_m = g_1 * g_2 * ... * g_m where g_j is the j-th digit indicator. The Fourier transform of the product is the convolution of the individual transforms.

**Compression ratio** = L1(hat(f_m)) / Product(mean_j + L1_j):

| m | L1(hat(f_m)) | Product of individuals | Compression    |
|---|--------------|----------------------|----------------|
| 2 | 1.17         | 2.07                 | 0.565          |
| 4 | 7.41         | 44.69                | 0.166          |
| 6 | 35.05        | 16,720               | 0.0021         |
| 8 | 159.18       | 144,191,148          | 0.0000011      |

The compression is super-exponential: the product structure creates massive Fourier cancellation. The actual L1 norm is a vanishing fraction of the product of individual L1 norms.

### Discrepancy

**Experiment 18 data.** The discrepancy D_m = max_L |cumsum(f_m, L)/Z_m - L/T_m|:

| m | D_m           | D_m * T_m  | D_m * C*m  |
|---|---------------|------------|------------|
| 3 | 0.0742        | 7.42       | 0.742      |
| 5 | 0.0113        | 28.22      | 0.192      |
| 7 | 0.00299       | 186.60     | 0.072      |
| 9 | 0.000632      | 987.48     | 0.019      |

D_m * C*m -> 0, meaning the survivor set becomes equidistributed at the scale of the transition zone. But D_m * Z_m grows, so the Erdos-Turan approach (bounding discrepancy via Fourier coefficients) is too loose.

## The Key Structural Facts

1. **2 is a primitive root mod 5^m**: the orbit covers all of (Z/5^m Z)^*, giving perfect equidistribution mod 5^m. The character sums are:

   sum_{u in (Z/5^m Z)^*} exp(2*pi*i*a*u/5^m) = 0 for gcd(a, 5) = 1

   (Ramanujan sum). So the orbit elements are perfectly uniformly distributed modulo 5^m.

2. **The orbit is degenerate mod 2^m**: x = 2^m * u, so x mod 2^m = 0 always. The digit-zero condition mixes the 5-adic part (equidistributed) with the 2-adic part (degenerate) through base-10 arithmetic.

3. **The digit-zero indicator has multiplicative structure across digit positions**: each digit depends on a different "scale" (mod T_j), and the conditions are nearly independent.

4. **Phase cancellation is massive**: the signed Fourier error is O(1) while the unsigned bound is O(2^m). This means the Fourier phases are highly structured and cancel.

## Related Literature

- **Dumitru 2025** (arXiv:2503.23177): Uses a dynamical Borel-Cantelli lemma to prove a metric result (measure-zero exceptional set) for powers of 2 with all even digits. The gap: proving the result for the specific orbit starting at 0.

- **Bourgain 2005-2007**: Exponential sum estimates over subgroups of (Z/qZ)^* for arbitrary q. Key result: if H is a subgroup with |H| > q^epsilon, then |sum_{x in H} exp(2*pi*i*ax/q)| <= |H| * q^{-delta(epsilon)}. In our case H = full group, so we get perfect cancellation (Ramanujan).

- **Mauduit-Rivat**: Exponential sum framework for "digital functions" (functions of the digit representation). Their framework requires the function to satisfy a "carry property" and a "Fourier property." The digit-zero indicator satisfies both.

- **Maynard 2019**: Proves infinitely many primes missing any single digit, using the Hardy-Littlewood circle method. The Fourier transform of the restricted-digit set exhibits "better than square-root cancellation" due to the multiplicative structure across digit positions. This is exactly what we see in our compression ratio data.

## The Specific Questions

### Question 1: Exploiting the multiplicative structure

The survivor indicator f_m = g_1 * ... * g_m has product structure. Each g_j has a Fourier transform that is "simple" (supported on frequencies related to T_j). The convolution creates cancellation.

Can this multiplicative structure be exploited to bound the ERROR TERM (not just the L^1 norm)? Specifically, can we show:

|sum_{j=1}^{T_m-1} F_m(j) * D_L(j)| <= C * (something that goes to 0)

using the fact that F_m = G_1 * G_2 * ... * G_m (convolution in Fourier space)?

The naive bound replaces |F_m * D_L| by |F_m| * |D_L| and loses all phase information. Can we do better by using the convolution structure of F_m and the known form of D_L?

### Question 2: The Bourgain approach adapted

Since 2 generates the full group (Z/5^m Z)^*, the orbit is trivially equidistributed mod 5^m. The hard part is converting this to digit equidistribution. The digit-zero condition involves x = 2^m * u mod 10^m, which mixes the 5-adic and 2-adic components.

Can Bourgain's sum-product techniques, or his results on exponential sums over subgroups, be applied to bound:

sum_{u in H} f(2^m * u mod 10^m)

where H = (Z/5^m Z)^* (full group) and f is the digit-zero indicator? The fact that f has product structure across digit positions should interact with the exponential sum machinery.

### Question 3: The Mauduit-Rivat / Maynard transfer

Maynard proved infinitely many primes missing a digit using the circle method. His key insight: the Fourier transform of the restricted-digit set in [0, 10^m) has the form:

hat(S)(t) = Product_{j=0}^{m-1} (1/10) * sum_{d in {1,...,9}} exp(2*pi*i*d*10^j*t)

This product structure gives "better than square-root cancellation" on minor arcs.

Our situation is analogous but with two differences:
- We count powers of 2 (a geometric sequence) rather than primes
- We restrict to ALL digits nonzero (not just missing one specific digit)

Can Maynard's Fourier-analytic treatment of the digit restriction be combined with the orbit structure of powers of 2 to give the required bound?

### Question 4: The discrepancy gap

The discrepancy D_m * C*m -> 0 (empirically, ~5^{-m} * m), meaning survivors become equidistributed at the relevant scale. But the Erdos-Turan inequality gives a bound D_m * Z_m which grows.

Is there a refined discrepancy inequality that bounds |S_m intersect [0,L)| directly in terms of D_m and L (not D_m * Z_m)? Something like:

|S_m intersect [0,L)| <= L * rho_m + D_m * L^{1/2} * Z_m^{1/2}?

The "geometric mean" form would give D_m * L^{1/2} * Z_m^{1/2} ~ 5^{-m} * m^{1/2} * (9/2)^{m/2} which still grows. But maybe the product structure of f_m allows a sharper discrepancy bound specific to intersection-of-conditions sifted sets.

## What I Am Looking For

1. A method to bound the signed error sum using the multiplicative structure (convolution) of F_m, not just its magnitude.
2. A connection between our digit-restriction Fourier analysis and Maynard's circle method or Mauduit-Rivat's digital function framework.
3. Any exponential sum inequality that converts "equidistribution mod 5^m" + "digit structure" into a pointwise bound on survivor counts in short intervals.
4. If a full proof is out of reach, the identification of which technical step is the bottleneck, and what auxiliary lemma would suffice.
