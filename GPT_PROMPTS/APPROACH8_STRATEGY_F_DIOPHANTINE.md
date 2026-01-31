# GPT Prompt: Strategy F -- Specializing Borel-Cantelli from a.e. theta to theta = log10(2)

## Role

You are a research mathematician specializing in metric number theory, Diophantine approximation, shrinking target problems, and the arithmetic of specific constants (logarithms of rationals). Your expertise includes Borel-Cantelli lemmas (first and second), Khintchine-type theorems, the Duffin-Schaeffer conjecture (now theorem), quantitative Borel-Cantelli (Sprindzhuk, Beresnevich-Velani), and effective equidistribution for specific irrationals. I need your help closing a specific gap: specializing a metric finiteness result to the specific value theta = log10(2).

## Problem Background

**The Conjecture.** The set A = {n >= 1 : 2^n has no digit 0 in base 10} is finite, with max element 86.

**What Is Proved.**
1. Density zero (elementary).
2. Metric finiteness (Borel-Cantelli): For Lebesgue-a.e. theta in [0,1), the set {m : N_m(theta) >= 1} is finite. Here N_m(theta) = #{j < L_m : frac(j*theta + c_m) in F_m} counts how many m-digit numbers of the form floor(10^{theta*(m+j)}) are zeroless.
3. Quasi-independence (Exp 32): The pair correlations mu(F_m cap (F_m - h*theta)) / mu(F_m)^2 are bounded by 1.58 uniformly in lag h and m.

**The Gap.** The Borel-Cantelli argument gives finiteness for a.e. theta. The gap is certifying that theta = log10(2) is not in the measure-zero exceptional set.

## The Metric Finiteness Proof

### Setup

- theta in [0,1) is the rotation parameter. The actual problem uses theta = log10(2) ~ 0.30103.
- F_m subset [0,1) is the "zeroless set" for m-digit numbers. mu(F_m) = rho_m ~ (9/10)^{m-1}.
- L_m = ceil(m/theta) ~ ceil(3.32*m) is the orbit length in the transition zone.
- N_m(theta) = sum_{j=0}^{L_m-1} 1_{F_m}(frac(j*theta + c_m(theta))).
- c_m(theta) = frac(m*theta) is the orbit offset.

### Borel-Cantelli (first lemma)

P(N_m >= 1) <= E[N_m] = L_m * rho_m ~ 3.3m * 0.9^{m-1}.

sum_{m=1}^{infinity} P(N_m >= 1) <= sum_{m=1}^{infinity} L_m * rho_m = sum m * 0.9^m * const < infinity.

By BC1: for a.e. theta, N_m(theta) >= 1 for only finitely many m. Equivalently, for a.e. theta, 2^n (computed with rotation theta instead of log10(2)) has a zero digit for all sufficiently large n.

### Why BC1 alone is insufficient

BC1 gives a.e. finiteness, but the exceptional set E = {theta : N_m(theta) >= 1 for infinitely many m} could have measure zero and still contain theta = log10(2). We need to show log10(2) is NOT in E.

### The quasi-independence data (Exp 32)

For the second Borel-Cantelli lemma (BC2), we need the events {N_m >= 1} to be "almost independent." Exp 32 confirmed quasi-independence of the indicator function 1_{F_m} under shifts by h*theta:

- mu(F_m cap (F_m - theta)) / mu(F_m)^2 <= 1.58 (lag 1)
- mu(F_m cap (F_m - h*theta)) / mu(F_m)^2 in [0.97, 1.04] for h >= 3

This gives Var(N_m) / E[N_m] ~ 1.26, close to the Poisson value of 1.

### What BC2 would give

If we could apply BC2 (the "divergence" direction): since sum P(N_m >= 1) = infinity... wait. Actually sum P(N_m >= 1) <= sum L_m * rho_m < infinity. So BC2 does not apply in the usual sense (we need the sum to diverge for BC2).

Actually, the correct framing is: BC1 says if sum P(A_m) < infinity then P(A_m i.o.) = 0. Here sum P(N_m >= 1) < infinity, so P(N_m >= 1 i.o.) = 0. This gives a.e. finiteness directly. No BC2 needed.

The problem is not "applying BC2" but rather "showing the specific theta = log10(2) is not exceptional."

## The Exceptional Set

Define E = {theta in [0,1) : N_m(theta) >= 1 for infinitely many m}. By BC1, mu(E) = 0.

### Question 1: Hausdorff Dimension of E

**What is the Hausdorff dimension of E?** If dim_H(E) < 1, then E is a "thin" set. If dim_H(E) = 0, then E is extremely thin. The Diophantine properties of theta = log10(2) (which has bounded-type-like CF with moderate partial quotients) should place it far from E.

More precisely: E is contained in limsup_{m -> infinity} {theta : N_m(theta) >= 1}. For each m, the set {theta : N_m(theta) >= 1} has measure <= L_m * rho_m ~ 3m * 0.9^m. By the mass transference principle (Beresnevich-Velani 2006), the Hausdorff dimension of E is related to the decay rate of these measures.

**Can you compute or bound dim_H(E)?**

### Question 2: Effective Borel-Cantelli

An effective (quantitative) Borel-Cantelli lemma would give: for theta outside a set of measure delta, N_m(theta) = 0 for all m >= M(delta). If we can show that log10(2) is outside this exceptional set of measure delta for some explicit delta and M...

**Is there a quantitative BC lemma that gives explicit bounds on the exceptional set?** For instance, the Sprindzhuk theorem or Beresnevich-Velani framework?

### Question 3: Diophantine Characterization of E

The exceptional set E consists of theta values where the orbit {frac(j*theta)} hits the shrinking targets F_m infinitely often. This is a shrinking target problem (Kurzweil 1955, Kim-Tseng 2007, Tseng 2008).

**Key result (Tseng 2008, arXiv:math/0702853):** For an irrational rotation by theta on the circle, the "monotone shrinking target property" (MSTP) holds for theta iff theta has bounded partial quotients (bounded type). theta = log10(2) does NOT have bounded partial quotients (the CF has a_13 = 18, and potentially larger partial quotients further out), but its partial quotients are moderate.

**However, our targets F_m are NOT monotone (F_{m+1} is not contained in F_m).** And they are not single intervals. Does the MSTP framework extend to:
- Unions of intervals?
- Cantor-dust targets?
- Non-monotone target sequences?

**If the MSTP or a variant holds for our targets:** then the conclusion is that theta hits F_m at most finitely often iff sum mu(F_m) < infinity (which is true). This would immediately give finiteness for ALL theta, not just a.e., resolving the conjecture.

But the MSTP typically requires bounded type, which log10(2) may not satisfy.

### Question 4: Using the Specific Arithmetic of log10(2)

theta = log10(2) = log(2)/log(10). This is a ratio of logarithms of small integers. Baker's theorem gives ||k*theta|| >= C/k^lambda with lambda = 1 and effective C.

**Key observation:** The exceptional set E is defined by the orbit hitting F_m. For theta = log10(2), the orbit point frac(j*theta) at index j = n - m is frac((n-m)*theta) where n is such that 2^n has m digits. The condition "frac(j*theta + c_m) in F_m" is equivalent to "2^n has all digits nonzero." So N_m(theta) is literally the count of m-digit zeroless powers of 2.

**The computational evidence is overwhelming:** N_m = 0 for all m from 28 to ~10^8/3.3 ~ 3*10^7. For theta to be in E, it would need N_m >= 1 for infinitely many m, meaning infinitely many zeroless powers of 2. The computational verification rules this out for all m up to ~10^7.

**Is there a Diophantine argument that leverages this computation?** For instance:
- If the next potential zeroless power of 2 after 2^86 would require m digits with m > 10^7, then the orbit would need to hit F_m with mu(F_m) < 0.9^{10^7} ~ 10^{-458000}. By Baker's theorem, the orbit points are spaced at distances >> 1/poly(m) apart. Can we show that no orbit point can be within distance 10^{-458000} of F_m for such large m?

### Question 5: The Quantitative Gap

The "gap" between what we have and what we need is:

- We have: P(N_m >= 1) <= L_m * rho_m ~ 3m * 0.9^m for a RANDOM theta.
- We need: N_m(theta_0) = 0 for theta_0 = log10(2) and all large m.
- The actual empirical error: |N_m - L_m*rho_m| < 11 for m = 2..27 (Exp 25).

**Is there a result that says:** if an irrational alpha has irrationality measure mu(alpha) = 2 (or mu(alpha) < infinity), and the targets B_m are unions of intervals with mu(B_m) -> 0 exponentially, then alpha hits B_m only finitely often?

The irrationality measure of log10(2) is 2 (almost all irrationals have measure 2, and log10(2) is not known to be exceptional). If mu(theta) = 2, then ||k*theta|| >> k^{-2-epsilon} for all epsilon, which gives very good Diophantine properties.

### Question 6: Convergence-Along-Subsequences Approach

Instead of proving N_m = 0 for all large m simultaneously, could we prove it along a subsequence of m values where F_m has particularly favorable structure? For instance:

- For m = q_n (convergent denominators of theta), the orbit has special equidistribution properties.
- For m such that L_m * rho_m < epsilon for some small epsilon, the expected count is tiny.

**If N_m = 0 for a subsequence m_k with m_k -> infinity, does this imply finiteness of the full set A?** Yes: if N_m = 0 for m >= M, then A subset {n : D(n) < M}, which is finite.

But we need N_m = 0 for ALL m >= M, not just a subsequence. Still, the subsequence approach might give a starting point for induction.

## Summary of What's Needed

The cleanest resolution would be a theorem of the form:

**Theorem (desired).** Let alpha be an irrational of finite type (irrationality measure mu(alpha) < infinity). Let (B_m) be a sequence of measurable subsets of [0,1) with sum mu(B_m) < infinity. Then the orbit {frac(j*alpha)}_{j >= 0} hits B_m for only finitely many m.

This would immediately resolve the conjecture since mu(log10(2)) = 2 and sum mu(F_m) < infinity.

**Is this theorem true? Is it known? Is it false?** If false, what additional conditions on B_m (beyond summable measure) are needed?

## Key Constants

- theta = log10(2) = 0.30102999566398...
- CF: [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117, ...]
- Irrationality measure: mu(theta) = 2 (expected, not proved exceptional)
- Baker bound: ||k*theta|| >= C_eff / k for effective constant C_eff
- rho_m = mu(F_m) ~ (9/10)^{m-1}
- L_m = ceil(m/theta) ~ ceil(3.32*m)
- sum L_m * rho_m < infinity (the series converges)
