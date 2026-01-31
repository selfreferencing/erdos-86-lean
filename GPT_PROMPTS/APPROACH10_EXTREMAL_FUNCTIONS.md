# GPT Prompt: Beurling-Selberg Extremal Functions for Digit-Structured Sets

## Role

You are a research mathematician specializing in harmonic analysis, extremal problems in Fourier analysis, the Beurling-Selberg problem, and the application of bandlimited approximation to number-theoretic equidistribution. Your expertise includes Vaaler polynomials, Graham-Vaaler truncation, the Selberg sieve's Fourier-analytic foundations, one-sided trigonometric polynomial approximation, and the Fourier analysis of digitally-defined sets (as in Maynard's work on restricted-digit primes). I need your help constructing an extremal minorant or majorant for a specific digit-structured set with controlled Fourier support.

## Problem Background

**The Conjecture.** The set A = {n >= 1 : 2^n has no digit 0 in base 10} is finite, with max element 86.

**What Is Proved.**
1. Density zero (elementary).
2. Metric finiteness (Borel-Cantelli): for a.e. rotation parameter theta, the orbit hits the zeroless set only finitely often.
3. Quasi-independence of the pair correlations (variance ratio ~ 1.26, near Poisson).

**The Current Bottleneck.** We have the exact error formula:

N_m = L_m * rho_m + R_m

where N_m is the count of m-digit zeroless powers of 2 (need N_m = 0 for large m), L_m ~ 3.32m is the transition zone length, rho_m ~ (9/10)^{m-1} is the measure of the zeroless set F_m, and

R_m = sum_{k != 0} hat{1_{F_m}}(k) * e(k * m * theta) * D_{L_m}(k * theta)

with theta = log10(2) and D_L the Dirichlet kernel.

A prior analysis (Approach 6A) established:
- **Low-frequency part is solved.** For |k| <= H = poly(m), the coboundary/cohomological equation can be solved. The Birkhoff sum telescopes, giving contribution o(1). This is not the bottleneck.
- **High-frequency tail is THE bottleneck.** For |k| > H, the triangle inequality gives a divergent bound (harmonic sum). Phase cancellation or an entirely different approach is needed.
- **Triangle-inequality approach is dead.** Experiments 36-37 showed T_m = sum |hat(k)| * |D_L(k*theta)| ~ 60-109, diverging as K_cutoff grows. The 1/k decay of Fourier coefficients combined with L ~ 3m creates an unbounded sum.

**The Proposed Strategy (from Approach 6A).** Replace 1_{F_m} with a bandlimited approximant h_m whose Fourier series is supported on |k| <= M = poly(m). Since h_m has only finitely many Fourier modes, the Weyl sum with h_m is automatically a finite sum, and the coboundary truncation handles all terms. The cost is the approximation error ||h_m - 1_{F_m}||, which must be controlled.

## The Beurling-Selberg Problem for F_m

### Classical Beurling-Selberg

For a single interval I = [a, b] of length delta, the classical Beurling-Selberg problem asks: find a trigonometric polynomial h(x) = sum_{|k| <= M} c_k e(kx) such that:
- h(x) <= 1_I(x) for all x (minorant), or h(x) >= 1_I(x) for all x (majorant).
- The integral (sum of Fourier coefficients) is as close to delta as possible.

The classical solution (Vaaler 1985, Graham-Vaaler 1981) gives:
- Majorant: integral = delta + 1/(M+1).
- Minorant: integral = delta - 1/(M+1).
- The error is exactly 1/(M+1), independent of the interval length delta.

### The Digit-Structured Extension

F_m is NOT a single interval. It is a union of 9^{m-1} intervals of width ~10^{-(m-1)}, arranged in a Cantor-dust pattern. Specifically:

F_m = {alpha in [0,1) : all digits of floor(10^{m-1+alpha}) are in {1,...,9}}

The components are indexed by digit strings (d_1,...,d_{m-1}) in {1,...,9}^{m-1}, and the j-th component has width approximately 10^{-(m-1)} * (1 + O(10^{-1})).

**Naive approach:** Apply the classical Beurling-Selberg construction to each of the 9^{m-1} components separately. Each component contributes error 1/(M+1), so total error = 9^{m-1}/(M+1). For this to be o(rho_m) = o(0.9^{m-1}), we need M >> 10^{m-1}. This gives Fourier support of size 10^{m-1}, which is far too large (we need poly(m)).

**The key question:** Can the PRODUCT STRUCTURE of F_m be exploited to build h_m with Fourier support poly(m) and approximation error o(rho_m)?

### The Product Structure

F_m has a recursive/product description: alpha is in F_m iff d_1(alpha) in {1,...,9} AND d_2(alpha) in {1,...,9} AND ... AND d_{m-1}(alpha) in {1,...,9}, where d_j(alpha) = floor(10^{j+alpha}) mod 10 is the j-th digit.

This means 1_{F_m}(alpha) = prod_{j=1}^{m-1} 1_{D_j}(alpha) where D_j = {alpha : d_j(alpha) != 0}.

Each factor 1_{D_j} is a union of 10^{j-1} intervals of width 9 * 10^{-j}, and has measure 9/10. The Fourier coefficients of 1_{D_j} satisfy:

hat{1_{D_j}}(k) = (9/10) * delta_{k=0} + (correction terms for k != 0)

The product structure of 1_{F_m} creates a CONVOLUTION structure for the Fourier coefficients:

hat{1_{F_m}} = hat{1_{D_1}} * hat{1_{D_2}} * ... * hat{1_{D_{m-1}}}

where * denotes Dirichlet-type convolution in Fourier space.

## Questions for You

### Question 1: Product-Structure Beurling-Selberg

Suppose we approximate each factor 1_{D_j} by a bandlimited function g_j with Fourier support |k| <= K_j. Then h_m = prod_{j=1}^{m-1} g_j has Fourier support |k| <= K_1 + K_2 + ... + K_{m-1}.

(a) **If each K_j = O(1) (constant per digit position),** then the total Fourier support is O(m). Is this achievable? Each D_j is a union of 10^{j-1} intervals. For j = 1, D_1 = (0.1, 1.0) is essentially one interval, so K_1 = O(1) works. For j = 2, D_2 is a union of 10 intervals, so K_2 = O(10) might be needed. For general j, K_j = O(10^{j-1})?

(b) **If K_j grows with j, what is the total Fourier support?** If K_j = 10^{j-1}, the total is sum 10^{j-1} = (10^{m-1} - 1)/9, which is exponential. This is no better than the naive approach.

(c) **Can the product be computed in Fourier space without expanding the support?** The convolution hat{g_1} * ... * hat{g_{m-1}} has support |k| <= sum K_j, but perhaps most of the convolution mass is concentrated on |k| <= poly(m). If the Fourier coefficients decay rapidly, truncating the convolution to |k| <= M might lose only O(exp(-M/m)) mass.

(d) **Is there a precedent for Beurling-Selberg approximation of product-structured sets?** Maynard's restricted-digit primes paper uses a product structure for the digit indicator, but he works with the unrestricted Fourier transform (no bandlimiting). Has anyone combined product structure with bandlimited approximation?

### Question 2: Approximation Quality

For a minorant h_m <= 1_{F_m} with Fourier support |k| <= M:

(a) **L1 error:** ||1_{F_m} - h_m||_1 = integral (1_{F_m} - h_m). By the Beurling-Selberg theory, this equals rho_m - (integral of h_m). What is the best achievable L1 error as a function of M and m?

(b) **The critical threshold:** We need integral(h_m) > rho_m - 1/L_m (so that L_m * integral(h_m) > L_m * rho_m - 1, which combined with N_m being an integer and the Weyl sum for h_m being bounded, gives N_m = 0). Since L_m ~ 3m, we need the L1 error to be o(1/m).

(c) **Comparison with rho_m:** The measure rho_m = (9/10)^{m-1} decays exponentially. The L1 error of the Beurling-Selberg approximation to a SINGLE interval is 1/(M+1). For 9^{m-1} intervals (naive), the error is 9^{m-1}/(M+1). For this to be smaller than rho_m / m, we need M >> m * 10^{m-1}. Is the product structure essential to avoid this exponential blowup?

### Question 3: The Weyl Sum with the Bandlimited Approximant

Define the "smoothed count":

N_m^{smooth} = sum_{j=0}^{L_m - 1} h_m(frac((m+j)*theta))

Since h_m has Fourier support |k| <= M:

N_m^{smooth} = sum_{|k| <= M} hat{h_m}(k) * e(k*m*theta) * D_{L_m}(k*theta)

This is a FINITE sum. The coboundary truncation from Approach 6A handles it:
- The k = 0 term gives L_m * integral(h_m).
- For 0 < |k| <= M, the cohomological equation phi_k(x) - phi_k(x + theta) = hat{h_m}(k) * e(kx) can be solved with ||phi_k|| <= |hat{h_m}(k)| / ||k*theta||.
- The Birkhoff sum telescopes, giving |sum_{0 < |k| <= M}| <= 2 * sum_{k=1}^{M} |hat{h_m}(k)| / ||k*theta||.

(a) **Can this finite sum be bounded by o(1)?** The key estimate: each |hat{h_m}(k)| should be at most rho_m * C(k) where C(k) is bounded. Then the sum is at most rho_m * sum_{k=1}^{M} C(k)/||k*theta||. For M = poly(m) and the known CF structure of theta, this sum is O(M * log M) = O(poly(m) * log m). So the total is rho_m * poly(m) = 0.9^m * poly(m) = o(1). This would work.

(b) **What are the actual Fourier coefficients of h_m?** If h_m is built as a product of per-digit approximants, hat{h_m} is a convolution. The leading term is hat{1_{F_m}}(k) = C(k) * (9/10)^{m-1} (from Exp 36). The correction from bandlimiting adds an error that depends on M and the smoothing kernel.

(c) **Does the relationship N_m <= N_m^{smooth} hold for a majorant?** If h_m >= 1_{F_m}, then N_m <= N_m^{smooth}. So bounding N_m^{smooth} < 1 gives N_m = 0. This only requires a majorant, which is easier than a minorant in the Beurling-Selberg theory. What is the best majorant with support |k| <= poly(m)?

### Question 4: The Digit-Automaton Compression

The set F_m is defined by a finite automaton: the states are partial digit strings, the transitions are "append digit d," and the accepting states are those with no zero digit. This automaton has O(m) states (or even O(1) states if we track only whether a zero has appeared).

(a) **Can the Beurling-Selberg approximant be computed via the automaton?** Instead of constructing h_m as a product of 9^{m-1} interval approximants, can we define h_m via a transfer-matrix recursion over the automaton states? The automaton processes one digit at a time, and at each step, we apply a local Beurling-Selberg smoothing.

(b) **The transfer matrix approach:** Define a vector v_m(alpha) in C^{states} that tracks the smoothed indicator through the automaton. At each level j, the transfer matrix T_j acts on v_j to produce v_{j+1}. If T_j is defined using smoothed (bandlimited) digit indicators instead of exact indicators, then the final output is a bandlimited approximant to 1_{F_m}.

(c) **Computational complexity:** The automaton has O(1) states (just "have we seen a zero?" = 2 states). The transfer matrix is 2x2 at each level. The bandlimited version requires tracking O(K) Fourier modes per level. The total computation is O(m * K), which is poly(m) if K = poly(m). Is this correct?

(d) **Error accumulation:** If each digit-level smoothing introduces error epsilon_j, the total error after m levels is at most sum epsilon_j (for a minorant) or prod (1 + epsilon_j) - 1 ~ sum epsilon_j (for small errors). If each epsilon_j = O(1/K), the total error is O(m/K). Setting K = m^2 gives error O(1/m) = o(1/L_m) since L_m ~ 3m. Is this achievable?

### Question 5: Selberg Sieve Connection

The Selberg sieve constructs optimal upper-bound sieves by solving a quadratic optimization problem over the "sifting" weights. The sieve weights are automatically bandlimited (supported on divisors up to D). The connection to Beurling-Selberg:

(a) **Is F_m a "sifted set"?** The zeroless integers can be described as integers surviving a sieve: remove all integers with digit 0 in position j, for j = 1,...,m-1. Each "sieving condition" (digit j = 0) removes a set of density 1/10. The inclusion-exclusion gives 1_{F_m} = prod (1 - 1_{d_j = 0}).

(b) **Can the Selberg sieve provide optimal smoothed weights?** The Selberg upper-bound sieve minimizes the L1 error of a majorant subject to the "support level" constraint (analogous to Fourier support). Applied to the digit sieve, this would give the optimal majorant h_m >= 1_{F_m} with controlled Fourier complexity.

(c) **What is the Selberg sieve dimension for this problem?** The sieve dimension (denoted kappa) controls the quality of the sieve: kappa = 1 is the easiest case (linear sieve), kappa > 1 is harder. For the digit sieve, each position j contributes independently, so the sieve dimension should be 1 (or even 0, since the sieving densities are not multiplicative in the number-theoretic sense).

### Question 6: Vaaler Polynomials and One-Sided Approximation

Vaaler (1985) constructed the optimal one-sided trigonometric polynomial approximation to the sawtooth function, which gives the best Beurling-Selberg approximants for intervals.

(a) **Explicit construction for a single interval:** For I = [a, a+delta], the Vaaler minorant of degree M satisfies integral = delta - 1/(M+1) and the majorant satisfies integral = delta + 1/(M+1). Can you write out the explicit formula and verify the error bound?

(b) **Extension to unions of intervals:** For F_m = union of I_1, ..., I_{9^{m-1}}, the naive approach gives error 9^{m-1}/(M+1). But if the intervals have special structure (equispaced within blocks, self-similar, Cantor-dust), can the error be reduced?

(c) **Graham-Vaaler truncation:** Graham and Vaaler (1981) showed how to truncate the Fourier series of a BV function to get one-sided approximants. For 1_{F_m}, which has total variation 2 * 9^{m-1} (each interval contributes 2 jumps), the Graham-Vaaler bound gives error proportional to (total variation) / M = 2 * 9^{m-1} / M. For this to be o(rho_m), we need M >> 10^{m-1}. Is this bound sharp, or can the product structure improve it?

(d) **The Fejer kernel alternative:** Instead of exact one-sided approximation, use Fejer kernel smoothing: convolve 1_{F_m} with a Fejer kernel of width 1/M. This gives a non-negative trigonometric polynomial h_m with support |k| <= M and ||h_m - 1_{F_m}||_1 = O(total variation / M) = O(9^{m-1}/M). Same exponential blowup. Is there a smarter convolution kernel?

### Question 7: The Key Structural Question

The fundamental tension is:
- F_m has 9^{m-1} components, so any "generic" bandlimited approximation needs Fourier support exponential in m.
- But F_m has a PRODUCT STRUCTURE (each digit independently in {1,...,9}), which compresses the description from 9^{m-1} components to m independent constraints.
- The question is whether this compression extends to the Beurling-Selberg problem.

(a) **Is there a theorem that says:** if f = prod f_j and each f_j has a good bandlimited approximant g_j, then prod g_j is a good bandlimited approximant to f? The issue is that prod g_j has Fourier support equal to the sum of the individual supports (convolution in Fourier space), which grows linearly in the number of factors.

(b) **But linear growth is OK for us.** If each g_j has support |k| <= K, then prod g_j has support |k| <= m*K. For K = O(1), this is O(m), which is poly(m). The question is whether K = O(1) per digit position is achievable.

(c) **For the first digit position:** D_1 = {alpha : d_1(alpha) in {1,...,9}} is approximately [0.1, 1.0), a single interval of length 0.9. A Vaaler polynomial of degree K_1 gives minorant with error 1/(K_1 + 1). For K_1 = 10, error = 1/11 ~ 0.09. This is comparable to the measure (0.9), so a 10% relative error. Is this good enough?

(d) **Error accumulation across digit positions:** If each factor has relative error epsilon (meaning integral(g_j) = (9/10)(1 - epsilon)), then the product has integral = (9/10)^{m-1} * (1 - epsilon)^{m-1} ~ rho_m * exp(-epsilon * m). For the total to be rho_m * (1 - O(1/m)), we need epsilon = O(1/m^2), which requires K_j = O(m^2) per position, giving total support O(m^3). Still polynomial in m.

(e) **Is O(m^3) Fourier support sufficient for the Weyl sum?** With M = m^3, the coboundary bound is rho_m * sum_{k=1}^{m^3} C(k)/||k*theta||. Using |C(k)| <= 1 and ||k*theta|| >> 1/k (since theta has irrationality exponent 2), the sum is O(m^6). So the total is 0.9^m * m^6 = o(1). This works.

## What Would Constitute a Solution

**Best case:** An explicit construction of a bandlimited majorant h_m >= 1_{F_m} with:
- Fourier support |k| <= poly(m).
- Integral = rho_m + O(rho_m / m^2) (so L_m * integral ~ L_m * rho_m + o(1)).
- The construction uses the product structure, with each digit position contributing O(poly(m)) Fourier modes.
- A proof that the smoothed Weyl sum sum_{|k| <= M} hat{h_m}(k) * e(k*m*theta) * D_L(k*theta) is o(1), using the coboundary truncation.

This would give N_m <= N_m^{smooth} = L_m * (rho_m + O(rho_m/m^2)) + o(1) = o(1), forcing N_m = 0 for large m.

**Good case:** A construction showing that the product-structure Beurling-Selberg approach gives polynomial Fourier support with controlled error, even without optimizing the Weyl sum bound. This would motivate a formal proof and identify the optimal polynomial degree.

**Partial result:** A proof that for a SINGLE digit position, the Beurling-Selberg approximation has quality sufficient for the product construction, even if the full product analysis is not completed. Or: a proof that the digit-automaton compression (Question 4) reduces the Beurling-Selberg problem from exponential to polynomial complexity.

## Key Constants

- theta = log10(2) = 0.30102999566398...
- CF: [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117, ...]
- Convergent denominators: q_0=1, q_1=3, q_2=10, q_3=93, q_4=196, q_5=485, q_6=2136
- rho_m = mu(F_m) ~ (9/10)^{m-1}
- L_m = ceil(m/theta) ~ ceil(3.32*m) (orbit length in transition zone)
- T_m = 4*5^{m-1} (full orbit period)
- |hat{1_{F_m}}(k)| = C(k) * (9/10)^{m-1}, C(k) stable for m >= 4 (Exp 36)
- Total variation of 1_{F_m}: 2 * 9^{m-1}
- Number of components of F_m: 9^{m-1}
- Component width: ~10^{-(m-1)}

## Experimental Data (Exp 36-37)

- C(k) ranges from ~0.02 to ~0.08 for k = 1..100, with C(k) ~ 1/k on average.
- The triangle-inequality bound T_m = sum |hat(k)| * |D_L(k*theta)| diverges as K_cutoff -> infinity.
- T_m grows as log(K) due to harmonic-sum structure.
- Actual error |N_m - L_m*rho_m| < 11 for all m <= 27 (Exp 25), so the true Weyl sum is O(1), while the triangle bound is ~100. The cancellation ratio is ~10:1.

## References

- Vaaler, "Some extremal functions in Fourier analysis," Bull. AMS 12 (1985)
- Graham and Vaaler, "A class of extremal functions for the Fourier transform," Trans. AMS 265 (1981)
- Selberg, "Remarks on sieves," Proc. 1972 Number Theory Conference, Boulder
- Montgomery, "Ten Lectures on the Interface between Analytic Number Theory and Harmonic Analysis," CBMS Regional Conference Series (1994), Ch. 1-2
- Maynard, "Primes with restricted digits," Invent. math. 217: 127-218 (2019)
- Noda, "Upper Bounds for Digitwise Generating Functions of Powers of Two," arXiv:2510.18414 (2025)
