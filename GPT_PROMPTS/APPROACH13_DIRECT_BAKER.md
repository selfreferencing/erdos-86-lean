# GPT Prompt: Direct Baker/Diophantine Approach to the Erdos 86 Conjecture

## Role

You are a research mathematician specializing in Baker's theorem on linear forms in logarithms, effective Diophantine approximation, and computational number theory. Your expertise includes effective irrationality measures for logarithms, the geometry of numbers, continued fraction theory, and applying Baker-type bounds to concrete problems in combinatorial number theory. I need your help completing a proof of a specific conjecture about powers of 2.

## Problem Background

**The Conjecture.** The set A = {n >= 1 : 2^n has no digit 0 in base 10} is finite, with max element 86.

**What Is Proved.**
1. Density zero (elementary).
2. For a.e. theta (in the metric sense), the orbit n*theta enters the "zeroless set" F_m only finitely often.
3. Computational verification: N_m = 0 for all m = 36..100, where N_m counts the number of n in the "transition zone" {m, m+1, ..., m + ceil(m/theta) - 1} such that 2^n has a zeroless m-digit prefix.
4. At most 9 distinct components of F_m are hit by the transition-zone orbit (Exp 30).
5. Carry automaton spectral radius for quasi-independence: sr_both/sr_input -> 9/10 (Exp 38).

**What Is NOT Proved.**
The specific theta = log10(2) has NOT been certified as "non-exceptional." The metric (a.e.) results cannot distinguish log10(2) from a potential counterexample.

## KEY INSIGHT FROM EXP 40: The L2 Route is Insufficient

A prior Fourier-analytic approach (Parseval identity) showed that ||R_m||_2 = O(m * 0.95^m) -> 0, where R_m(x) = N_m(x) - L_m * rho_m is the Birkhoff sum deviation. This gives metric finiteness (a.e. theta avoids F_m eventually).

However, Exp 40 revealed that **upgrading from L2 to the specific point x = m*theta is equivalent to the conjecture itself.** For m >= 50, E[N_m] < 1 and the L2-to-pointwise step is automatic. For m = 36..49, N_m = 0 empirically but E[N_m] > 0.5, so the L2 bound has no leverage. The Parseval approach proves metric finiteness but cannot certify the specific theta.

**Conclusion: A DIRECT Diophantine/Baker approach is needed.** The problem must be attacked through the arithmetic of log10(2), not through abstract functional analysis.

## The Direct Approach

### The Setup

Fix m >= 36. The transition zone contains L_m = ceil(m/theta) consecutive integers {m, m+1, ..., m + L_m - 1}. For each n in this range, 2^n has approximately m significant digits (in base 10).

**N_m = 0** means: for every n in the transition zone, 2^n contains at least one digit 0 among its first m digits.

**What does "first m digits of 2^n contain no zero" mean arithmetically?**

2^n has first m digits d_1 d_2 ... d_m iff there exists an integer k such that:
d_1 d_2 ... d_m * 10^k <= 2^n < (d_1 d_2 ... d_m + 1) * 10^k

Taking log10:
log10(d_1 d_2 ... d_m) + k <= n * log10(2) < log10(d_1 d_2 ... d_m + 1) + k

Let alpha = frac(n * log10(2)). Then alpha determines the significant digits of 2^n. Specifically, 2^n has first m digits equal to D iff:
log10(D) - floor(log10(D)) <= alpha < log10(D+1) - floor(log10(D+1))

(approximately, for D an m-digit integer).

The condition "all m digits of D are nonzero" defines a union of intervals for alpha. Each zeroless m-digit integer D = d_1 d_2 ... d_m (with all d_i in {1,...,9}) gives an interval of width approximately (1/D) * (1/ln(10)).

### The target intervals

For each zeroless m-digit integer D (there are 9^m of them, since each digit is 1..9), define:

I_D = [log10(D) mod 1, log10(D+1) mod 1)

The orbit point alpha_n = frac(n * theta) is in I_D iff 2^n has first m significant digits equal to D.

**N_m = 0** iff alpha_n is not in any I_D for any zeroless D, for all n in the transition zone.

### Baker's theorem application

If alpha_n = frac(n * theta) is in I_D, then there exists an integer k such that:

|n * log(2) - k * log(10) - log(D)| < log(1 + 1/D) < 1/D

This is a linear form in three logarithms: log(2), log(10), and log(D).

**Baker's theorem (1972)** gives: for algebraic numbers alpha_1, ..., alpha_n and integers b_1, ..., b_n with not all zero:

|b_1 * log(alpha_1) + ... + b_n * log(alpha_n)| > exp(-C * log(B))

where B = max(|b_i|) and C depends on the alpha_i and n.

For our application:
- alpha_1 = 2, alpha_2 = 10, alpha_3 = D (an integer)
- b_1 = n, b_2 = -k, b_3 = -1
- B = max(n, k, 1) ~ n (since k ~ n * 0.301)

Baker's bound gives:

|n * log(2) - k * log(10) - log(D)| > exp(-C * (log n)^3)

(for three logarithms, the exponent is (log B)^3 with current best bounds).

We need this to exceed 1/D ~ 10^{-(m-1)}:

exp(-C * (log n)^3) > 10^{-(m-1)}

i.e., C * (log n)^3 < (m-1) * log(10)

Since n ~ m/theta ~ 3.3m in the transition zone:

C * (log(3.3m))^3 < (m-1) * log(10)

For large m, the left side grows as (log m)^3 and the right side grows as m. So this inequality holds for all m >= m_0 for some effective m_0 depending on C.

### The problem with Baker

**The constant C depends on D.** Specifically, Baker's theorem involves the "logarithmic heights" of the algebraic numbers, and log(D) has height ~ log(D) ~ (m-1) * log(10). The constant C for three logarithms is approximately:

C ~ c * prod(log h_i) * log(log B)

where h_i are the heights. For our case:

C ~ c * log(1) * log(log 10) * (m-1) * log(10) * log(log n)

Wait, this needs more care. The key issue is:

**There are 9^m choices of D.** Baker's bound must hold for ALL of them simultaneously. Each D gives a different linear form, with a different Baker constant. The bound must be:

min_D |n * log(2) - k * log(10) - log(D)| > 10^{-(m-1)}

over all zeroless m-digit D and all n in the transition zone.

Since there are L_m ~ 3m values of n and 9^m values of D, the total number of inequalities is ~ 3m * 9^m. But Baker's bound for each individual inequality gives a lower bound that depends on D, specifically on the prime factorization of D and its size.

### The computational feasibility question

For moderate m (say m = 36..100), can Baker's theorem effectively certify that no n in the transition zone hits any zeroless D?

The issue is that for each pair (n, D), Baker gives:

|n * log(2) - k_D * log(10) - log(D)| > exp(-C(D) * (log n)^3)

where k_D is the integer nearest to n*theta - log10(D). The constant C(D) depends on D. For "nice" D (small prime factors), C(D) is moderate. For "generic" D, C(D) could be very large.

**But we don't need Baker for all D.** We only need to certify that frac(n*theta) is not in the union of all I_D. The union has total measure rho_m = (9/10)^{m-1}. If we can bound the distance from frac(n*theta) to the nearest I_D boundary, we might need Baker only for the CLOSEST D values.

## Experimental Data

### Exp 40 Part D: N_m for m = 2..100

The last m with N_m > 0 is m = 35 (N_m = 1). For m >= 36, N_m = 0. The conjecture is computationally verified through m = 100 (covering powers 2^n for n up to ~433).

### Exp 30: Danger cylinder census

For m = 2..27, the maximum number of F_m components hit by the transition-zone orbit is 9 (at m = 8, 9, 10). By m = 27, only 0 components are hit.

### Nearest misses for m >= 36

For the Baker approach, we need to know: how close does frac(n*theta) come to the zeroless intervals I_D for n in the transition zone and m >= 36?

This data would quantify the "Baker margin": how much room does Baker's lower bound need to cover?

## Questions for You

### Question 1: Effective Baker bounds for our linear forms

(a) **What is the best current effective lower bound for |n*log(2) - k*log(10) - log(D)|?** The linear form involves log(2), log(10) = log(2) + log(5), and log(D). For D with small prime factors (e.g., D = 2^a * 3^b * 5^c * 7^d), the form simplifies. For generic D, we have three "independent" logarithms.

(b) **What effective constant C arises?** Laurent's refinement of Baker (2008) gives sharper bounds than the original. For two logarithms, the exponent is ~(log B)^2. For three, ~(log B)^3. With n ~ 3m and B ~ 3m, we get C * (log(3m))^3 vs (m-1)*log(10). This holds for m >> C.

(c) **Can the 9^m choices of D be handled efficiently?** We don't need a separate Baker bound for each D. Instead, the union of intervals I_D has gaps. If the minimum gap between consecutive I_D intervals is bounded below (by some function of m), we only need the orbit to miss a single "macro-interval" of known width.

(d) **What is the effective m_0?** Given current Baker constants, what is the smallest m_0 such that Baker certifies N_m = 0 for all m >= m_0? If m_0 <= 36, the proof is complete (combined with computational verification).

### Question 2: Structure of the zeroless interval system

(a) **What is the gap structure of the union of I_D intervals?** The intervals I_D for zeroless D partition part of [0,1) into 9^m small intervals with gaps (the gaps correspond to integers D that contain a zero digit). What is the minimum gap width?

(b) **The "nearest zero digit" landscape.** For a generic alpha in [0,1), the distance to the nearest interval I_D with D zeroless is approximately (1 - rho_m) / (number of gaps) ~ 10^{-(m-1)} / 9. Can this be tightened?

(c) **Can the interval system be described by a finite automaton?** The intervals I_D for zeroless D have a natural hierarchical structure (Cantor dust). At each digit position, the allowed digits are {1,...,9}. This gives a tree of depth m with branching factor 9. Can the gap structure be computed recursively?

### Question 3: The danger cylinder approach (from APPROACH11)

If we can prove that the orbit hits at most C components of F_m, then we need Baker's bound for only C specific D values (those corresponding to the hit components). This drastically reduces the problem.

(a) **Can the danger cylinder bound be combined with Baker?** If at most 9 components are hit (empirical maximum), then we need Baker for at most 9 specific linear forms per m. Each form involves log(D_i) for a specific zeroless integer D_i. If these D_i have bounded complexity (e.g., bounded number of prime factors), Baker's constants are moderate.

(b) **What determines which components are "dangerous"?** The orbit point frac(n*theta) is in I_D iff D/10^{m-1} <= 10^{frac(n*theta)} < (D+1)/10^{m-1}. The "dangerous" D values are those closest to 10^{frac(n*theta)}. Since frac(n*theta) is approximately uniformly distributed, the dangerous D values should be approximately uniformly distributed among zeroless integers.

(c) **Is there a "worst-case" D for Baker?** Some D values might give weaker Baker bounds (larger C). Are these D values ever "dangerous" (close to the orbit)?

### Question 4: A purely computational certificate

(a) **For each m from 36 to some m_1, can we compute the minimum distance from the orbit to the zeroless intervals?** This would give a concrete list of "Baker margins" needed. If Baker's bound exceeds the maximum margin for m >= m_1, the proof is complete.

(b) **What is a realistic m_1?** Baker bounds typically give effective results for integers beyond 10^{10} or so. In our case, n ~ 3m, so m_1 ~ 10^{10}/3 is far too large for brute computation. But the Baker constant may be much better for our specific linear forms (involving only log 2, log 5, and log D).

(c) **Can interval arithmetic make this rigorous?** For each (n, D) pair, compute frac(n*theta) - log10(D) mod 1 using interval arithmetic (rigorous error bounds). If the interval doesn't contain zero, the orbit misses I_D. This makes the computational verification fully rigorous.

### Question 5: The role of the continued fraction of theta

(a) **The convergent denominators q_k of theta = log10(2) are:** 1, 3, 10, 93, 196, 485, 2136, ... The large partial quotient a_19 = 117 means there's a very good rational approximation p_19/q_19 with |theta - p_19/q_19| < 1/(117 * q_19^2).

(b) **Do the convergent denominators create "near misses"?** When n = q_k (a convergent denominator), frac(n*theta) is very close to 0 (or to 1). This means 2^{q_k} has significand very close to a power of 10. These are the most "dangerous" n values for the conjecture.

(c) **The convergent denominators in the transition zone.** For m = 36, the transition zone is n = 36..155. The convergent denominator q_4 = 196 is just outside this range. For m = 60, the zone is n = 60..259. The denominators q_4 = 196 and q_5 = 485 are relevant. For m = 100, the zone is n = 100..432. The denominator q_6 = 2136 is far outside.

(d) **Can the analysis focus on convergent denominators?** If the nearest miss is always at a convergent denominator, and Baker's bound for these specific n values is sufficient, the proof might be cleaner.

### Question 6: Connection to irrationality measures

(a) **Baker's theorem gives an effective irrationality measure for log10(2).** Specifically, for any integers p, q with q > 0:

|log10(2) - p/q| > q^{-mu}

where mu is an effective constant. The best known result (from Baker-type methods) gives mu = 2 + epsilon for theta = log10(2), matching the Roth-type bound.

(b) **How does the irrationality measure connect to our problem?** If frac(n*theta) is in I_D, then |n*theta - k - log10(D)| < 10^{-(m-1)} for some integer k. This gives:

|theta - (k + log10(D))/n| < 10^{-(m-1)}/n

This is NOT a rational approximation (log10(D) is irrational in general). So the standard irrationality measure doesn't directly apply. We need a bound on |theta - alpha/n| where alpha = k + log10(D) is an algebraic irrational.

(c) **Is this related to the "effective algebraic approximation" problem?** There's a body of work on effective bounds for |alpha - beta| where alpha, beta are specific algebraic numbers. Baker's theorem is the main tool. For our problem, we're asking how close n*theta can be to log10(D), which is a specific question about the distance between two real numbers defined by logarithms.

### Question 7: Finite verification strategies

(a) **Interval arithmetic verification.** For each m = 36..100 and each n in the transition zone, rigorously verify that frac(n*theta) is not in any I_D. This uses interval arithmetic for theta = log10(2) and the interval endpoints log10(D), log10(D+1).

(b) **How far can this be pushed?** With efficient interval arithmetic, can we verify m up to 200? 500? The transition zone size is L_m ~ 3m, and the number of zeroless D values is 9^m. But we don't need to check all D: we only need to check whether frac(n*theta) is in the complement of the zero-digit intervals. This is a single check per (n, m) pair.

(c) **The challenge of high-precision arithmetic.** For m = 100, we need to know frac(n*theta) to ~100 decimal places. Since n ~ 333, we need theta to ~102 decimal places. This is available (log10(2) is known to billions of digits). The computational cost is dominated by the m-digit string check, not the arithmetic.

(d) **Can the verification be made fully rigorous?** Using MPFR or similar libraries, the interval arithmetic can be made exact (no floating-point errors). This would give a computer-assisted proof that N_m = 0 for m = 36..m_max.

## What Would Constitute a Solution

**Best case:** An effective Baker-type bound showing that for all m >= m_0 (with m_0 computable), no n in the transition zone gives a zeroless m-digit prefix for 2^n. Combined with computational verification for m < m_0, this proves the conjecture.

**Good case:** A proof that the danger cylinder count is O(1), combined with Baker bounds for the specific "dangerous" D values. If the dangerous D values have bounded complexity (e.g., bounded number of prime factors), the Baker constants are moderate and the proof goes through.

**Partial result:** A rigorous (interval arithmetic) verification that N_m = 0 for m = 36..500 or higher. This strengthens the computational evidence dramatically and may suggest patterns for the theoretical proof.

## Key Constants

- theta = log10(2) = 0.30102999566398119521373889472449302676818...
- CF: [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117, ...]
- Convergent denominators: q_0=1, q_1=3, q_2=10, q_3=93, q_4=196, q_5=485, q_6=2136
- rho_m = (9/10)^{m-1}: 0.880 (m=2), 0.042 (m=30), 0.00003 (m=100)
- L_m = ceil(m/theta): 7 (m=2), 100 (m=30), 333 (m=100)
- Last m with N_m > 0: m = 35 (Exp 40)
- Last n with 2^n fully zeroless: n = 86 (known)
- Baker exponent for three logarithms: ~(log B)^3 (Laurent 2008)

## References

- Baker, "A sharpening of the bounds for linear forms in logarithms," Acta Arith. 21 (1972)
- Baker and Wustholz, "Logarithmic forms and group varieties," J. reine angew. Math. 442 (1993)
- Laurent, "Linear forms in two logarithms and interpolation determinants II," Acta Arith. 133 (2008)
- Matveev, "An explicit lower bound for a homogeneous rational linear form in the logarithms of algebraic numbers," Izv. Math. 64 (2000)
- Noda, "Upper Bounds for Digitwise Generating Functions of Powers of Two," arXiv:2510.18414 (2025)
- Bugeaud, "Linear forms in two and three logarithms and interpolation determinants," Journees Arithmetiques (2003)
