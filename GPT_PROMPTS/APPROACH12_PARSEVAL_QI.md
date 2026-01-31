# GPT Prompt: Parseval/Correlation Route to the Erdos 86 Conjecture

## Role

You are a research mathematician specializing in ergodic theory, Fourier analysis on the circle, dynamical Borel-Cantelli lemmas, pair correlation of digitally-defined sets, and the arithmetic of irrational rotations. Your expertise includes spectral methods for equidistribution, quasi-independence bounds for dynamically-defined events, transfer operators for digit expansions, and exceptional-set avoidance in shrinking target problems. I need your help completing a two-step proof strategy for a specific conjecture about powers of 2.

## Problem Background

**The Conjecture.** The set A = {n >= 1 : 2^n has no digit 0 in base 10} is finite, with max element 86.

**What Is Proved.**
1. Density zero (elementary).
2. Step B+: for m >= 4, every orbit hit in the transition zone is in a distinct component of F_m.
3. Quasi-independence empirically confirmed (Exp 32, Exp 38).
4. Metric finiteness (Borel-Cantelli): for a.e. theta, the orbit hits F_m only finitely often.
5. The gap: certifying theta = log10(2) is not exceptional.

**The Current Bottleneck (as of Stage 8).** Prior work showed:
- The triangle-inequality Fourier bound diverges (harmonic sum). DEAD.
- Low-frequency coboundary truncation works (contribution o(1)). SOLVED.
- High-frequency tail cannot be bounded by absolute Fourier sums. THE PROBLEM.

## THE BREAKTHROUGH: The Parseval/Correlation Identity (★)

A prior analysis (APPROACH7 response) identified the following identity that **eliminates the high-frequency tail entirely**:

Define f_m(x) = 1_{F_m}(x) - rho_m and the Birkhoff sum R_m(x) = sum_{j=0}^{L-1} f_m(x + j*theta).

Then N_m = L_m * rho_m + R_m(m*theta), and we need |R_m(m*theta)| < 1 - L_m*rho_m for large m.

**The Parseval identity:**

int_0^1 |R_m(x)|^2 dx = L*(rho_m - rho_m^2) + 2*sum_{h=1}^{L-1} (L-h) * [mu(F_m ∩ (F_m - h*theta)) - rho_m^2]

This is exact. The entire infinite Fourier series (including the divergent high-frequency tail) collapses into O(L_m) overlap measures. No harmonic divergence. No truncation needed.

**Under quasi-independence** (mu(F_m ∩ (F_m - h*theta)) <= (1+eps)*rho_m^2 for all 1 <= h <= L-1):

||R_m||_2^2 <= L*rho_m*(1 + eps*L*rho_m) << L*rho_m

So ||R_m||_2 << sqrt(L_m * rho_m) ~ sqrt(m) * (9/10)^{m/2}, which decays exponentially.

## THE TWO-STEP PROOF STRUCTURE

**Step 1:** Prove a quasi-independence bound:
mu(F_m ∩ (F_m - h*theta)) <= C(h) * rho_m^2 for 1 <= h <= L_m
with C(h) growing at most polynomially in h and m.

**Step 2:** Upgrade from L2 (a.e. x) to pointwise at x = m*theta:
Show that x = m*theta is not in the "exceptional set" where |R_m| is large.

## EXPERIMENTAL DATA ON QUASI-INDEPENDENCE (Exp 38)

### Continuous overlap ratios mu(F_m ∩ (F_m - h*theta)) / rho_m^2:

| m | h=1 | h=2 | h=3 | h=4 | h=5 | h=10 |
|---|-----|-----|-----|-----|-----|------|
| 2 | 1.050 | 1.013 | 1.000 | 0.988 | 0.982 | - |
| 3 | 1.106 | 1.035 | 1.003 | 0.989 | 0.989 | 1.038 |
| 4 | 1.165 | 1.057 | 1.008 | 0.992 | 0.995 | 1.039 |
| 5 | 1.227 | 1.080 | 1.013 | 0.994 | 1.001 | 1.039 |

**Key observation:** The lag-1 ratio GROWS with m: approximately 1 + 0.05*m. For lags h >= 3, the ratio is within [0.985, 1.040] with no growth trend. The h=10 spike (1.039) corresponds to the convergent denominator q_2 = 10.

### Carry automaton spectral radii:

The transfer matrix for "multiply by 2^h, require all output digits nonzero given all input digits nonzero" has spectral radius ratio sr_both/sr_input:

| h | ratio |
|---|-------|
| 1 | 0.948 |
| 3 | 0.904 |
| 7 | 0.900 |
| 10 | 0.900 |

The ratio converges to 9/10 by h ~ 7. This confirms that at the spectral-radius level, the output digits become independent of input digits. The lag-1 deviation (0.948 vs 0.900) reflects short-range carry correlations.

### Empirical quasi-independence from Exp 32 (discrete orbit):

The discrete orbit version (fraction of orbit elements with both position i and position i+h zeroless):
- Lag 1: ratio <= 1.58 (at m=10)
- Lags >= 3: ratio within [0.97, 1.04]
- Var(N_m)/E[N_m] ~ 1.26

### Critical question about the lag-1 growth:

The pattern 1.050, 1.106, 1.165, 1.227 at lag 1 grows approximately linearly in m. If this continues as ~1 + C*m with C ~ 0.05, the contribution to (★) from lag 1 is:

2*(L-1) * C*m * rho_m^2 ~ 6C * m^2 * (9/10)^{2(m-1)}

This still decays exponentially (m^2 * 0.81^m -> 0). But if the growth were faster (e.g., exponential in m), the Parseval approach would fail.

## Questions for You

### Question 1: What controls the lag-1 overlap growth?

The overlap mu(F_m ∩ (F_m - theta)) / rho_m^2 grows as approximately 1 + 0.05*m. The lag-1 shift is theta = log10(2) ~ 0.301.

(a) **Why does the lag-1 ratio grow?** The shift by theta moves digits by a fraction of a position. For the most significant digit, the condition "d_1(alpha) != 0 AND d_1(alpha + theta) != 0" creates a correlation because both conditions constrain alpha to avoid the same zeros. As m increases, more digit positions create more opportunities for correlation.

(b) **Is the growth O(m), O(m^2), or bounded?** The data for m=2..5 shows approximately linear growth. Can you determine the asymptotic rate analytically? A key question: does each new digit position contribute O(1) additional correlation (giving O(m) total), or do the contributions diminish?

(c) **Does the growth depend on the arithmetic of theta?** If theta were rational (p/q), the correlation structure would be very different (periodic). For irrational theta, the correlation at lag 1 involves the partial quotients of the CF expansion of theta. Since theta = [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, ...], the partial quotients determine which digit positions interact most.

(d) **What growth rate is tolerable for the Parseval approach?** The weighted contribution to (★) is sum_{h=1}^{L-1} (L-h) * excess(h). If excess(h) = C(h) * rho_m^2 with C(h) = 1 + c*m for h=1 and C(h) bounded for h >= 2, then the total is:
(L-1) * c*m * rho_m^2 + sum_{h=2}^{L-1} (L-h) * O(rho_m^2)
= O(m^2 * rho_m^2) + O(L^2 * rho_m^2) = O(m^2 * 0.81^m) -> 0.

So O(m) growth at lag 1 is fine. What about O(m^2)? The total would be O(m^3 * 0.81^m), still -> 0. In fact, ANY polynomial growth in m is tolerable because 0.81^m kills any polynomial.

### Question 2: Proving quasi-independence rigorously

The APPROACH7 response sketched a "carry automaton" proof. The idea: mu(F_m ∩ (F_m - h*theta)) counts alpha such that x = 10^{m-1+alpha} is zeroless AND 2^h * x has zeroless significand. The multiplication by 2^h in base 10 is a finite-state carry automaton, and the transfer matrix has spectral radius that controls the overlap rate.

(a) **Can the carry automaton proof be made rigorous?** For h <= 10, the transfer matrix has 2^h states and can be computed explicitly. The spectral radius ratio sr_both/sr_input converges to 9/10. Does the matrix power (with initial carry = 0) give a rigorous bound on the overlap ratio?

(b) **What about h >= 11?** The carry automaton has 2^h states, which is exponentially large. Is there a compressed representation? The digits 0-9 in base 10 interact with the carry, and the carry range is {0, ..., 2^h - 1}. Can the transfer matrix be block-diagonalized using the structure of 2^h mod 10^k for various k?

(c) **Alternative: a product-formula proof.** 1_{F_m}(alpha) = prod_{j=1}^{m-1} 1_{D_j}(alpha) where D_j = {alpha : d_j(alpha) != 0}. The overlap is:

mu(F_m ∩ (F_m - h*theta)) = integral prod_{j=1}^{m-1} 1_{D_j}(alpha) * 1_{D_j}(alpha + h*theta) dalpha

If the factors (1_{D_j}(alpha) * 1_{D_j}(alpha + h*theta)) are approximately independent across j, the integral ~ prod (9/10)^2 = (81/100)^{m-1} = rho_m^2. Can this "approximate independence across digit positions" be proved?

(d) **The Mauduit-Rivat connection.** Mauduit-Rivat type arguments bound correlations of digitally-defined functions. Their framework handles additive digital functions, but the "all digits nonzero" condition is multiplicative (product of digit indicators). Can the multiplicative structure be handled by logarithms or by a direct product analysis?

### Question 3: Upgrading L2 to pointwise (the exceptional set problem)

The Parseval identity gives ||R_m||_2 -> 0 (exponentially). This implies R_m(x) -> 0 for a.e. x (by Chebyshev + Borel-Cantelli, since sum ||R_m||_2^2 < infinity implies R_m(x) -> 0 for a.e. x by the first Borel-Cantelli).

But we need R_m(m*theta) -> 0 for the specific point x = m*theta. This point CHANGES with m (it's not a fixed x).

**CRITICAL NEGATIVE RESULT (from a prior Diophantine analysis, APPROACH8):** The "desired theorem" one might hope for, namely "if theta has finite type and sum mu(B_m) < infinity, then the orbit n*theta mod 1 enters B_m only finitely often," is **FALSE** for general measurable targets B_m.

**Counterexample:** Take B_m to be a tiny ball of radius epsilon_m centered at m*alpha mod 1, with sum epsilon_m < infinity. The balls are placed exactly on the orbit, so the orbit enters every B_m, despite summability. This shows the theorem requires structural conditions on B_m (not just summability and finite type).

**Known shrinking target theorems** (Kurzweil 1955, Kim-Tseng, Haynes-Jensen-Kristensen) require **monotone ball targets** (single intervals). Our B_m = {x : |R_m(x)| > 1/2} is a union of many intervals, potentially O(9^m), with no monotonicity.

**(a) Three routes identified by the prior analysis:**

**Route A: E ⊆ Diophantine class.** Show the exceptional set E (where the orbit enters F_m infinitely often) is contained in {theta : irrationality exponent > 2}. Then Baker's theorem (mu(log10(2)) = 2) finishes. Problem: E is defined by digit-cylinder conditions, not Diophantine ones, and translating between the two seems intractable.

**Route B: Pointwise Fourier control (most promising).** Prove |R_m(x)| is small specifically at x = m*theta, using the Fourier structure of R_m evaluated at this specific point. This does not require a general shrinking target theorem. Instead, it exploits the relationship between the Fourier coefficients hat{f_m}(k), the Dirichlet kernel D_L(k*theta), and the evaluation phase e(k*m*theta).

**Route C: New shrinking target theorem for digit-cylinder targets.** Prove a Borel-Cantelli result adapted to the Cantor-dust structure of B_m. This would be a new result in the theory of irrational rotations.

**(b) Route B in detail.** Since R_m(x) = sum_{k != 0} hat{f_m}(k) * D_L(k*theta) * e(kx), evaluating at x = m*theta gives:

R_m(m*theta) = sum_{k != 0} hat{f_m}(k) * D_L(k*theta) * e(k*m*theta)

The phases e(k*m*theta) are specific to the evaluation point. If the partial sums of this series converge (using Abel/Cesaro summation), the problem reduces to bounding a smoothed Weyl sum. Is there phase cancellation at x = m*theta that is absent at generic x?

**(c) The Hausdorff dimension bound.** The exceptional set E has dim_H(E) <= log10(9) ≈ 0.954. This is a provable partial result, using the covering structure of F_m. But it does not certify that theta_0 = log10(2) is not in E.

**(d) Does the digit structure of B_m help?** The set B_m is NOT arbitrary. It is defined by a Birkhoff sum of 1_{F_m}, which has digit structure (product of indicator functions over digit positions). Can this product structure be exploited to show B_m has bounded complexity (covered by O(poly(m)) intervals)? If so, known shrinking target results for intervals might apply (Route C).

**(e) The decorrelation strategy (extending Maynard).** Maynard's work on primes with restricted digits uses a "decorrelation" argument that separates Diophantine conditions from digital conditions. Could a similar argument show that the orbit position m*theta is "decorrelated" from the digital condition defining B_m? This would be a form of Route B, using the independence between the irrational rotation dynamics and the base-10 digit structure.

### Question 4: What if QI fails at lag 1?

Suppose the lag-1 overlap ratio grows as C * rho_m^{-delta} for some delta > 0 (i.e., faster than polynomial in m). Then:

mu(F_m ∩ (F_m - theta)) = C * rho_m^{2-delta}

and the contribution to (★) from lag 1 is:
2*(L-1) * (C * rho_m^{2-delta} - rho_m^2) ~ 2*L * C * rho_m^{2-delta}
= O(m * rho_m^{2-delta})

This decays to zero iff 2 - delta > 0, i.e., delta < 2. Since rho_m ~ 0.9^m, the overlap must grow slower than rho_m^{-2} = (10/9)^{2m} for the Parseval approach to work.

(a) **What is the worst-case lag-1 overlap ratio?** The self-overlap (h=0) gives ratio = 1/rho_m = (10/9)^{m-1}. Can the lag-1 ratio be as large as 1/rho_m (i.e., delta = 1)? The data shows it's much smaller (1.23 vs 1.56 at m=5).

(b) **Is there a theoretical upper bound on the lag-1 overlap?** Since F_m - theta is a different set from F_m (shifted by theta = log10(2)), the overlap cannot exceed min(rho_m, rho_m) = rho_m. So the ratio is at most 1/rho_m ~ 1.11^m. Even this worst case gives delta = 1, and the contribution is m * rho_m^1 -> 0. So the Parseval approach works even with the WORST possible lag-1 ratio.

(c) **Wait: is this argument correct?** The contribution from lag 1 is 2*(L-1) * mu(overlap_1) = 2*(L-1) * rho_m (at worst). And L = O(m), rho_m = (9/10)^{m-1}. So the worst-case contribution is O(m * 0.9^m) -> 0. Meanwhile, the "main term" L * rho_m also -> 0. So ||R_m||_2^2 = L*rho_m + O(m*0.9^m) = O(m*0.9^m) -> 0 regardless.

**This suggests that quasi-independence is NOT actually needed for the L2 bound.** The bound ||R_m||_2^2 <= sum_{h=0}^{L-1} (2L - 1) * rho_m = (2L - 1)*L*rho_m is automatically valid because each overlap is at most rho_m. And (2L-1)*L*rho_m = O(m^2 * 0.9^m) -> 0.

*If this is correct, the entire proof reduces to Step 2 (L2 to pointwise) and quasi-independence is a bonus, not a requirement.*

### Question 5: The crude L2 bound and its implications

Let me spell out the crude bound:

||R_m||_2^2 = sum_{h=-(L-1)}^{L-1} (L - |h|) * Cov(h)

where Cov(h) = mu(F_m ∩ (F_m - h*theta)) - rho_m^2.

Since mu(F_m ∩ (F_m - h*theta)) <= rho_m for all h (trivially), we have:
Cov(h) <= rho_m - rho_m^2 = rho_m(1 - rho_m) <= rho_m.

So: ||R_m||_2^2 <= sum_{h=-(L-1)}^{L-1} (L - |h|) * rho_m = L^2 * rho_m.

Therefore: ||R_m||_2 <= L * sqrt(rho_m) = O(m * (9/10)^{m/2}).

This decays exponentially. The sum sum_m ||R_m||_2^2 <= sum m^2 * 0.9^m < infinity.

(a) **Is this crude bound correct?** The key step is mu(F_m ∩ (F_m - h*theta)) <= rho_m, which holds because F_m ∩ (F_m - h*theta) is contained in F_m. Is there any subtlety I'm missing?

(b) **If correct, what does this buy us?** The bound ||R_m||_2 = O(m * 0.95^m) means:
- mu{x : |R_m(x)| > 1/2} <= 4 * m^2 * 0.9^m
- sum_m mu(B_m) < infinity
- For a.e. x, |R_m(x)| < 1/2 for all large m.

This is EXACTLY the metric finiteness statement (already proved via Borel-Cantelli). The Parseval identity provides an alternative proof but doesn't go beyond it.

(c) **What is gained by quasi-independence?** QI tightens the L2 bound from O(m * 0.95^m) to O(sqrt(m) * 0.95^m). This gives a tighter measure bound on B_m but doesn't change the qualitative conclusion (sum still converges).

(d) **So the ENTIRE difficulty is Step 2: upgrading a.e. to the specific orbit.** Can you confirm that the L2 bound is correct and that the only remaining obstacle is showing that the orbit {m*theta mod 1} avoids the exceptional set limsup B_m?

### Question 6: Explicit structure of the exceptional set

The set B_m = {x : |R_m(x)| > 1/2} has measure O(m^2 * 0.9^m). What does B_m look like?

**This question is CRITICAL for Route C (Question 3).** If B_m has bounded interval complexity, known shrinking target theorems for intervals might apply.

(a) **Is B_m a union of intervals?** R_m(x) = sum_{j=0}^{L-1} (1_{F_m}(x+j*theta) - rho_m) is a step function (piecewise constant) with jumps at the endpoints of F_m shifted by j*theta for j = 0, ..., L-1. Each shifted copy has 2*9^{m-1} endpoints, so R_m has at most 2*L*9^{m-1} jumps. This gives B_m at most O(L*9^{m-1}) = O(m * 9^m) intervals. This is exponential in m.

(b) **Can B_m be covered by FEWER intervals?** Although R_m has O(m * 9^m) jumps, most of these may correspond to tiny changes in R_m (a single digit flipping). If B_m has a threshold at 1/2 and R_m typically stays well below or well above this threshold, the boundary of B_m might have far fewer connected components. Can you estimate the actual number of connected components of B_m?

(c) **How does B_m relate to F_m?** Since R_m(x) = N_m(x) - L*rho_m where N_m(x) counts the hits of the orbit starting at x, B_m consists of starting points x where the orbit has "too many" or "too few" hits in F_m.

(d) **A self-similar structure?** Since F_m has Cantor-dust structure (self-similar across scales), does B_m inherit any regularity from this? If B_m decomposes into pieces that are approximately translates of each other, this regularity could substitute for the "single interval" requirement in shrinking target theorems.

### Question 7: The orbit sequence {m*theta mod 1}

The evaluation point x = m*theta moves as m increases. The sequence {m*theta mod 1} is equidistributed by Weyl's theorem.

(a) **Is {m*theta mod 1} a "typical" sequence for avoiding small sets?** For a fixed small set B, a uniformly random point avoids B with probability 1 - mu(B). For the orbit sequence, the avoidance probability depends on the arithmetic of theta.

(b) **Known results:** For theta of finite type (irrationality exponent mu(theta) = 2, which holds for theta = log10(2) by the Roth-type bound), there are effective equidistribution results. Specifically, for any interval I of length delta:

|#{m <= M : m*theta mod 1 in I} - M*delta| = O(M^epsilon)

Can this be extended to general measurable sets B_m (not just fixed intervals)?

(c) **The key difficulty:** The sets B_m change with m. We're asking about a MOVING TARGET: does the sequence m*theta avoid B_m for all large m? This is a quantitative shrinking-target problem with non-monotone, non-interval targets. **A prior analysis (APPROACH8) showed that the general theorem "finite type + sum mu(B_m) < infinity => finitely many hits" is FALSE.** So any result must exploit the specific structure of B_m.

(d) **Effective equidistribution with structured targets.** The Erdos-Turan inequality gives discrepancy bounds for intervals. For B_m that can be decomposed into J_m intervals, the effective equidistribution error is at most O(J_m / m^A) for some A depending on the Diophantine type of theta. If J_m is polynomial in m and mu(B_m) decays exponentially, the sum converges:

sum_m [mu(B_m) + J_m / m^A] < infinity

This gives the orbit avoids B_m for large m. **The key question from Q6 is therefore: what is J_m (the interval complexity of B_m)?**

(e) **The Martin-Lof randomness boundary.** The prior analysis notes that certifying a specific theta is not exceptional "borders on Martin-Lof randomness questions." For algorithmically random theta, no effective null set captures it. Since log10(2) is conjectured (but not proved) to have no exceptional patterns, a full solution may require understanding the pseudo-randomness properties of log10(2) at a level beyond current number theory. Is this pessimism warranted, or does the specific digit structure of B_m create a loophole?

## What Would Constitute a Solution

**Best case:** A complete proof that:
1. ||R_m||_2^2 <= C * m^2 * 0.9^m (the crude bound), AND
2. The orbit {m*theta mod 1} avoids {x : |R_m(x)| > 1/2} for all large m.

Combined, these give |R_m(m*theta)| < 1/2 for large m, forcing N_m = 0.

**Good case:** A proof that B_m can be decomposed into O(poly(m)) intervals, enabling effective equidistribution arguments for Step 2 (Route C). Or: a pointwise Fourier bound at x = m*theta exploiting the specific Dirichlet kernel structure (Route B).

**Partial result:** A proof that the crude L2 bound is correct (confirming the "does QI even matter?" analysis in Q4-Q5). Or: a characterization of the interval complexity of B_m. Or: a proof that dim_H(E) <= log10(9) < 1 (the Hausdorff dimension bound from APPROACH8). Or: an identification of which route (A, B, or C from Q3) is most tractable for our specific problem.

## Key Constants

- theta = log10(2) = 0.30102999566398...
- CF: [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117, ...]
- Convergent denominators: q_0=1, q_1=3, q_2=10, q_3=93, q_4=196, q_5=485, q_6=2136
- rho_m = mu(F_m) ~ (9/10)^{m-1} (actual: 0.880 at m=2, 0.640 at m=5)
- L_m = ceil(m/theta) ~ ceil(3.32*m)
- N_m = 0 for m >= 27 (empirically, 2^86 is the last zeroless power)
- L_m * rho_m: peaks at ~13 (around m=10), drops below 1 around m ~ 50
- Overlap ratio at lag 1: ~1 + 0.05*m (Exp 38)
- Overlap ratio at lags >= 3: within [0.985, 1.040] (Exp 38)

## References

- Kurzweil, "On the metric theory of inhomogeneous Diophantine approximations," Studia Math. 15 (1955)
- Kim and Tseng, "On the distribution of subsequences of the sequence n*alpha," Proc. AMS (2011)
- Mauduit and Rivat, "La somme des chiffres des carres," Acta Math. 203 (2009)
- Maynard, "Primes with restricted digits," Invent. math. 217: 127-218 (2019)
- Noda, "Upper Bounds for Digitwise Generating Functions of Powers of Two," arXiv:2510.18414 (2025)
- Haynes, Jensen, Kristensen, "Metrical musings on Littlewood and friends," Proc. AMS 142 (2014)
- Philipp, "Some metric theorems in number theory," Pacific J. Math. 20 (1967)
