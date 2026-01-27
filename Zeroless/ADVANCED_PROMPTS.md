# Advanced Approach Prompts for Finiteness of Zeroless Powers of 2

## Context for all prompts

**The Erdos Problem**: Prove that the set E = {n in N : 2^n has no digit 0 in base 10} is finite.

**The 86 Conjecture** (stronger): 2^86 is the largest such power. This is computationally verified for n = 87..302 in Lean 4 with `native_decide`. But our goal here is the WEAKER statement: |E| < infinity, by any route.

**Current state**: We have a Lean 4 formalization that proves the 86 Conjecture conditional on one axiom (`no_zeroless_k_ge_91`): for k >= 91 digits, every 2^n has a zero. Proving this axiom (or finding any route to finiteness of E) is an open problem.

---

## What has been tried and killed (11 directions, 12 independent analyses)

We have systematically explored and eliminated the following proof strategies. **DO NOT re-derive these results.** Use them as constraints on any new approach.

### 1. Digit-by-digit / forced-tail counting (KILLED)
**Why it fails**: Each digit level k has period T_k = 4*5^(k-1) residue classes mod 10^k. Among these, 4*4.5^(k-1) are zeroless-compatible. The net growth factor per level is 5*(9/10) = 4.5 > 1. Survivor counts GROW exponentially rather than decaying. This has been confirmed from 6 independent angles (combinatorial counting, transfer operator eigenvalues, Fourier obstruction, SAT certificates, covering congruences, automaton formulation).

### 2. Multiplicative Fourier on (Z/5^k Z)* (KILLED)
**Why it fails**: The density of zeroless-compatible residues mod 5^k is exactly 1.0 for all k. Every unit mod 5^k is zeroless-compatible. The zeroless constraint is completely invisible to the 5-adic structure alone.

### 3. Mod 2^k density (KILLED)
**Why it fails**: Similarly, density mod 2^k = 1.0 for all k (tested to k=25). The constraint is invisible to 2-adic structure alone.

### 4. CRT factorization (KILLED)
**Why it fails**: The zeroless constraint lives ONLY in the joint mod-10^k structure, where density = (9/10)^(k-1). It cannot be factored via CRT into independent mod-2^k and mod-5^k components.

### 5. S-unit / Subspace Theorem (KILLED)
**Why it fails**: A zeroless k-digit number is a sum of k S-unit terms (S = {2,5}) with bounded coefficients. The Subspace Theorem requires O(1) terms, but k ~ 0.301*n grows with n. The only plausible compression (run-length encoding of constant-digit blocks) requires bounded-length runs, which zeroless does not force. The condition is positive-entropy (9^k possibilities vs k^t for bounded S-unit sums). Two independent analyses confirm no viable compression exists.

### 6. Senge-Straus / Stewart two-bases technology (KILLED)
**Why it fails**: These results bound the count of integers with at most r nonzero digits in two multiplicatively independent bases. Zeroless is the OPPOSITE condition: ALL digits nonzero, i.e., maximally non-sparse. Complementation (10^k - 1 - N) doesn't create sparsity. A naive v_2 argument ("v_2(2^n) = n but v_2 of a digit sum should be small") fails because carries raise p-adic valuations arbitrarily (e.g., 16 = 6 + 10, where v_2(6) = 1 but v_2(16) = 4).

### 7. Baker / Matveev linear forms in logarithms (KILLED)
**Why it fails**: The truncation identity 2^n = 10^m * q + T_m yields a linear form |n*log(2) - m*log(10) - log(q)| = O(T_m/10^m*q). But q = floor(2^n/10^m) has height ~2^n. Matveev's lower bound gives exp(-C*n*log(n)), which is too weak to contradict the upper bound exp(-c*n). The fundamental tradeoff: making the linear form small requires large q, but controlled q gives a non-small form. The 5-adic Baker alternative is also blocked: zeroless is a residue-avoidance condition, not a smallness condition on a p-adic linear form.

### 8. Doubling automaton (KILLED)
**Why it fails**: The digit-doubling map is a 2-state carry transducer with transition matrix [[4,4],[4,5]], dominant eigenvalue ~8.53. Only one dangerous pair exists: (carry=0, digit=5), which creates a carry. But iterated composition blows up the state space exponentially. The automaton formulation is isomorphic to digit-by-digit counting (direction 1).

### 9. Finite computation bootstrap (KILLED)
**Why it fails**: The period T_k = 4*5^(k-1) is too large to enumerate for k >= 20. The Hensel lift tree is supercritical (branching factor 4.5 > 1), so the tree has exponentially many branches. Suffix depth reaches 115 at n=7931, confirming the tree has long branches and cannot be pruned by finite computation.

### 10. Borel-Cantelli / discrepancy (KILLED as currently formulated)
**Why it fails**: The heuristic gives expected ~0.0025 hits beyond k=91 digits (sum of 3.32*(9/10)^(k-1) over k >= 91). But proving "0 hits" for a DETERMINISTIC orbit requires discrepancy of order (9/50)^k. The best available bounds (Erdos-Turan, Weyl) give ~5^(-k/2) at best, exponentially weaker. Tseng (2008) proves that shrinking-target results fail for general irrational rotations, blocking the standard approach.

### 11. Additive Fourier on Z/10^k Z (KILLED as a standalone approach)
**Why it fails**: The maximum normalized Fourier coefficient of the zeroless set mod 10^k is ~1/9 (coming from the mod-5^k component), which does NOT decay with k. Standard exponential sum bounds cannot overcome this permanent obstruction.

---

## The precise mathematical gap

**What we know**: The orbit n |-> 2^n mod 10^k visits the zeroless residues (those whose base-10 digits are all in {1,...,9}) with asymptotic density (9/10)^(k-1). For a k-digit power of 2, we need k ~ n*log_10(2), giving ~3.32 values of n per digit level. The expected number of zeroless 2^n with >= 91 digits is sum_{k>=91} 3.32*(9/10)^(k-1) ~ 0.0025, strongly suggesting finiteness.

**What we don't know**: How to make this rigorous. Specifically, we lack ANY of the following (any one would suffice):

1. **Exponential equidistribution**: A bound showing that for the coupled system (2^n mod 5^k, {n*log_10(2)}) on (Z/5^k Z)* x [0,1), the discrepancy of the orbit {1, 2, ..., N} decays faster than (9/10)^k. The best known bounds decay as 5^(-k/2), which is exponentially too weak.

2. **Normality of 2^n in base 10**: A proof that 2^n is normal (or even just "not abnormally avoiding 0") in base 10 for all large n. This is wide open. It is not even known whether 2^n contains the digit 7 for infinitely many n.

3. **A shrinking-target theorem for digit-cylinder families**: For the irrational rotation alpha = log_10(2), a result showing that the orbit n*alpha mod 1 hits shrinking targets of measure ~(9/10)^{f(n)} (where f(n) ~ 0.301*n) only finitely often. Tseng (2008) shows this fails for general targets, but digit-cylinder targets have special algebraic structure (they're unions of intervals with endpoints at rational multiples of powers of 10) that might be exploitable.

4. **An independence result**: A proof that the events "digit j of 2^n is nonzero" for j = 1, ..., k are sufficiently independent (e.g., negatively correlated or satisfying a mixing condition) that their joint probability decays exponentially. Even weak pairwise decorrelation results are unknown for powers of 2.

5. **Any route to finiteness of E**: We do NOT need the exact cutoff 86. We do not need a good bound. Even proving |E| < 10^{10^{100}} or that E is contained in {0, ..., N_0} for some computable N_0 would be a breakthrough of the first order.

### Precise Open Problem Statement

**Open Problem (The Erdos Zeroless Powers Problem)**:
Let E = {n in N : the decimal representation of 2^n contains no digit 0}. Prove that E is finite.

Equivalently: prove that for all sufficiently large n, the number 2^n contains at least one digit 0 in base 10.

This is equivalent to: prove that the sequence 2^n mod 10^k avoids the "all-nonzero" residue set S_k (|S_k| = 4*4.5^(k-1) out of T_k = 4*5^(k-1) classes) for all k >= K_0 and all n with 2^n having exactly k digits.

The heuristic expected number of counterexamples beyond 91 digits is ~0.0025. The problem is "morally true" but sits at the intersection of dynamics, number theory, and combinatorics in a way that no existing technique can reach.

---

## PROMPT F1: Furstenberg-Type Intersection Rigidity

### Goal
Determine whether Furstenberg's intersection/joinings machinery, or its modern extensions (Host-Kra, Einsiedler-Katok-Lindenstrauss), can yield finiteness of the zeroless powers of 2.

### Background
Furstenberg's x2-x3 conjecture (1967) states that the only Borel probability measure on [0,1] invariant under both x -> 2x mod 1 and x -> 3x mod 1 is Lebesgue measure. While still open in full generality, partial results exist:
- Rudolph (1990): If the measure has positive entropy for one map, it's Lebesgue.
- Host (1995): Joinings of x2 and x3 are essentially trivial.
- Einsiedler-Katok-Lindenstrauss (2006): Higher-rank rigidity in homogeneous dynamics.

The relevance: our problem involves the interaction of multiplication by 2 (the map n -> n+1 on exponents, or x -> 2x on [0,1] via {n*log_10(2)}) with the base-10 digit structure (controlled by both 2 and 5). The zeroless condition is a "digit constraint" that should be destroyed by the mixing of these two independent structures.

### Questions

1. **Furstenberg x2-x5 connection**: The zeroless constraint involves the joint behavior of 2^n modulo powers of 2 and modulo powers of 5. Can the fact that 2 and 5 are multiplicatively independent be leveraged via Furstenberg-type rigidity? Specifically:
   - The orbit of {n*log_10(2)} under the rotation by log_10(2) is equidistributed (Weyl).
   - The orbit of 2^n mod 5^k is periodic with period 4*5^(k-1).
   - Can the COUPLING of these two dynamics (archimedean and non-archimedean) be shown to satisfy some rigidity theorem?

2. **Entropy considerations**: The zeroless set S_k at level k has cardinality 4*4.5^(k-1), hence entropy h = log(4.5)/log(5) per digit level in the 5-adic component. This is strictly less than the maximal entropy log(5)/log(5) = 1. Furstenberg-type results often use the gap between actual and maximal entropy. Can the entropy deficit (1 - log(4.5)/log(5)) ~ 0.063 be used?

3. **Joinings formulation**: Define:
   - mu_1 = the measure on T = R/Z given by the orbit {n*log_10(2)} (archimedean, equidistributed)
   - mu_2 = the measure on Z_5^* given by the orbit 2^n mod 5^k (5-adic, periodic)
   - mu_joint = the joint distribution of (mu_1, mu_2) on T x Z_5^*
   For the zeroless constraint, we need the joint measure to avoid a product-measurable set of measure (9/10)^k at level k. Can joinings theory show that mu_joint is "close to product" in a sufficiently strong sense?

4. **The Einsiedler-Fish approach**: Einsiedler and Fish (2010) proved results about sumsets of x2-x3 invariant sets. Their method uses the product structure of Z_2 x Z_3 (analogous to our Z_2 x Z_5 via CRT). Can their "expansion" results show that the zeroless set, being invariant under a suitable action, must have zero measure in the product?

5. **Key obstacle assessment**: The standard Furstenberg machinery requires a MEASURE that is jointly invariant. Our problem involves a SINGLE ORBIT (of the integer n), not a measure. Can the orbit be embedded in a suitable measure-theoretic framework? What measure on T x Z_5^* x Z_2 would capture the zeroless constraint?

### What has been killed (do not retry)
- CRT factorization: the constraint is invisible mod 2^k and mod 5^k separately.
- Weyl equidistribution alone: gives polynomial discrepancy, need exponential.
- Borel-Cantelli with standard discrepancy: Tseng (2008) blocks shrinking targets.

### Deliverable
(a) A concrete formulation of how Furstenberg/joinings/rigidity machinery would apply to this specific problem, identifying the precise dynamical system, the invariant measure, and the rigidity theorem that would be invoked, OR
(b) A clear explanation of why this machinery cannot reach the problem, identifying the specific hypothesis that fails.

### References
- Furstenberg: "Disjointness in ergodic theory" (1967)
- Rudolph: "x2 and x3 invariant measures" (1990)
- Host: "Nombres normaux, entropie, translations" (1995)
- Einsiedler, Katok, Lindenstrauss: "Invariant measures and the set of exceptions to Littlewood's conjecture" (2006)
- Einsiedler, Fish: "Rigidity of measures invariant under the action of a multiplicative semigroup of polynomial growth on T" (2010)
- Hochman, Shmerkin: "Local entropy averages and projections of fractal measures" (2012)
- Lindenstrauss: "Invariant measures and arithmetic quantum unique ergodicity" (2006)

---

## PROMPT F2: Additive Combinatorics and Exponential Sum Methods

### Goal
Determine whether exponential sum methods (Bourgain, Green-Tao, Wooley) or additive combinatorics can prove finiteness of zeroless powers of 2, bypassing the 4.5^k barrier.

### Background
The 4.5^k barrier arises from analyzing digit structure one level at a time. Additive combinatorics methods sometimes circumvent such barriers by exploiting GLOBAL structure (e.g., sumset growth, Freiman-Ruzsa theory, or exponential sum cancellation across multiple scales simultaneously).

The key exponential sum is:
S_k(alpha) = sum_{a in S_k} e(a * alpha)
where S_k is the set of zeroless residues mod 10^k (|S_k| = 9^k for full zeroless set, or 4*4.5^(k-1) for the orbit-restricted set), and e(x) = exp(2*pi*i*x).

The zeroless count for k-digit 2^n equals:
(1/10^k) * sum_{t=0}^{10^k - 1} S_k(t/10^k) * e(-t * 2^n / 10^k)

which is an exponential sum over the "Fourier dual" of the zeroless set evaluated at the orbit point 2^n.

### Questions

1. **Bourgain-type approach**: Bourgain (2005, 2010) proved results about the distribution of {2^n * alpha} for Diophantine alpha, using exponential sum estimates that go beyond Weyl's inequality. His methods achieve SUBEXPONENTIAL discrepancy bounds in some settings. Can Bourgain's multilinear exponential sum technology give discrepancy bounds of order exp(-c*k) for the zeroless counting problem? What is the best discrepancy bound achievable by current methods for the orbit 2^n mod 10^k?

2. **The sumset structure of S_k**: The zeroless set S_k mod 10^k has a product structure:
   S_k = {d_0 + d_1*10 + ... + d_{k-1}*10^{k-1} : each d_i in {1,...,9}}
   This is a GENERALIZED arithmetic progression (a sum of k intervals, each of length 9, at exponentially spaced positions). Freiman-Ruzsa theory bounds the structure of sets with small sumsets. S_k has |S_k + S_k| ~ |S_k|^{log(18)/log(9)} ~ |S_k|^{1.315}, indicating moderate additive structure. Can this structure be exploited?

3. **Multi-scale analysis**: Instead of analyzing one digit level k at a time (which gives the 4.5 barrier), can we analyze multiple levels simultaneously? For example, consider the constraint "digits k through k+m are all nonzero" as a multi-scale event. The joint probability of this event over different scales might decay faster than the product of marginals if there is sufficient mixing between scales.

4. **The circle method**: The Hardy-Littlewood circle method writes the count of representations as a contour integral. For our problem:
   #{n <= N : 2^n is zeroless with k digits} = integral_0^1 (sum_{n: 2^n has k digits} e(n*alpha)) * (sum_{m in S_k} e(-m*alpha)) dalpha
   The major arcs contribute the "expected" count ~3.32*(9/10)^(k-1). The minor arc estimate requires bounding the exponential sum sum_{n ~ k/log_10(2)} e(n*alpha) * e(-2^n * alpha). This is a TYPE II sum in the Vaughan/Heath-Brown sense. Can modern bounds for such sums (e.g., via Wooley's efficient congruencing or decoupling) give a minor arc bound of o(1) * (major arc contribution)?

5. **Maynard's digit work**: James Maynard (Fields Medal 2022) proved results about primes with restricted digits. His method handles "missing digit" constraints by showing sufficient exponential sum cancellation. Our problem is different (we want to show that 2^n is NOT missing-digit for large n, whereas Maynard shows that primes CAN be missing-digit). But Maynard's exponential sum machinery might be adaptable. Specifically, Maynard bounds sums of the form sum_p e(p*alpha) restricted to numbers with digits in a set D. We need bounds of the form sum_n 1_{2^n in S_k} = sum_n prod_j 1_{digit_j(2^n) != 0}. Can Maynard's sieve-theoretic decomposition of the digit constraint be adapted?

6. **Green-Tao / nilsequences**: The Green-Tao theorem on primes in arithmetic progressions uses nilsequence technology to handle "structured" obstructions. The orbit 2^n mod 10^k is a nilsequence of step 1 (a linear sequence on a torus). Can higher-order uniformity norms (U^s norms) detect cancellation that Fourier analysis misses? Note that the permanent 1/9 Fourier obstruction (killed direction 11) lives at the U^1 level. Perhaps U^2 or U^3 norms see additional cancellation.

### What has been killed (do not retry)
- Standard Fourier analysis on Z/10^k Z: permanent 1/9 obstruction.
- Weyl equidistribution alone: polynomial discrepancy.
- CRT factorization: invisible mod 2^k and mod 5^k separately.
- Borel-Cantelli with standard discrepancy: Tseng (2008) blocks it.

### Deliverable
(a) A concrete exponential sum estimate that, if true, would imply finiteness of E, together with an assessment of whether current technology can prove it, OR
(b) A clear identification of the exponential sum that needs to be bounded, with a precise comparison between what is needed and what current methods achieve.

### References
- Bourgain: "Exponential sum estimates over subgroups of Z_q* ..." (2005)
- Bourgain: "On the distribution of the residues of small multiplicative subgroups of F_p" (2010)
- Maynard: "Primes with restricted digits" (Inventiones, 2019)
- Green, Tao: "The primes contain arbitrarily long arithmetic progressions" (2008)
- Wooley: "The cubic case of the main conjecture in Vinogradov's mean value theorem" (2016)
- Bourgain, Demeter, Guth: "Proof of the main conjecture in Vinogradov's mean value theorem" (2016)
- Harman: "Prime-Detecting Sieves" (Princeton, 2007)
- Freiman: "Foundations of a structural theory of set addition" (1973)

---

## PROMPT F3: p-adic Analytic Methods (Strassmann, Weierstrass, Mahler)

### Goal
Determine whether p-adic analytic methods can prove that the set of n for which 2^n is zeroless (base 10) is finite, using the 5-adic structure of the orbit.

### Background
The orbit 2^n mod 5^k is periodic with period T_k = 4*5^(k-1) (this is the multiplicative order of 2 in (Z/5^k Z)*). The zeroless condition mod 10^k is equivalent (via CRT) to: the unique a in {0,...,10^k - 1} satisfying a = 0 mod 2^k and a = 2^n mod 5^k has all base-10 digits in {1,...,9}.

The set of units u in Z/5^k Z such that CRT(0 mod 2^k, u mod 5^k) is zeroless is a subset W_k of (Z/5^k Z)*. This set has |W_k| = 4*4.5^(k-1). In the projective limit, we get a subset W of Z_5^* (the 5-adic units). The 86 conjecture is equivalent to: the orbit {2^n mod 5^k : n >= 87} avoids W_k for all k >= 91.

The 5-adic exponential of 2 is well-defined: since 2 is a unit in Z_5, we can write 2 = omega * <2> where omega is a (4th) root of unity and <2> is in 1 + 5*Z_5. The map n -> 2^n restricted to n = r mod 4 (for fixed r) is a p-adic analytic function of n via the 5-adic logarithm/exponential: 2^n = omega^r * exp_5(n * log_5(<2>)).

### Questions

1. **Strassmann's theorem application**: For fixed residue class n = r mod 4, the function f_r(n) = 2^n is a 5-adic analytic function. For each k, define g_{r,k}(n) = indicator that 2^n mod 5^k is in W_k (the zeroless-compatible set). This indicator is NOT itself analytic, but can it be expressed as a finite sum of analytic functions whose zeros can be controlled by Strassmann's theorem?

   More precisely: for each zeroless-compatible residue w in W_k, the equation 2^n = w mod 5^k is equivalent to exp_5(n * log_5(<2>)) = omega^{-r} * w mod 5^k, which is a congruence for a 5-adic analytic function. Strassmann's theorem says this has at most M_k zeros (where M_k is the "Strassmann bound" determined by the 5-adic valuations of the Taylor coefficients). What is M_k? Does it grow slower than |W_k| = 4*4.5^(k-1)?

2. **The Strassmann bound computation**: For the function f(x) = exp_5(x * log_5(<2>)) - w (where w is a 5-adic unit), the Taylor expansion around 0 is:
   f(x) = (<2>^0 - w) + log_5(<2>) * x + (log_5(<2>))^2 / 2! * x^2 + ...
   The 5-adic valuation of the n-th coefficient is v_5(log_5(<2>)^n / n!). Since log_5(<2>) has v_5 = 1, this is n - v_5(n!) = n - (n - s_5(n))/(5-1) where s_5(n) is the digit sum of n in base 5. So v_5(c_n) = n - (n - s_5(n))/4 = (3n + s_5(n))/4. The Strassmann bound M is the largest index where the minimum valuation is attained. This should be small (likely M = O(1) for generic w), giving O(1) solutions per w per residue class. But there are |W_k| ~ 4.5^k residues w. Total bound: O(4.5^k) solutions per digit level k. Since there are ~3.32 values of n per level, we'd need 4.5^k << 3.32, which fails spectacularly.

   Is this analysis correct? If so, Strassmann gives a MUCH weaker bound than needed (it counts solutions to INDIVIDUAL congruences, of which there are too many).

3. **Krasner analytic / Amice transform approach**: Instead of applying Strassmann term-by-term to each w in W_k, can we construct a SINGLE p-adic analytic function whose zeros are exactly the n for which 2^n is zeroless? The key would be to find a p-adic measure mu on Z_5 such that:
   mu({u in Z_5^* : CRT(0 mod 2^k, u mod 5^k) is zeroless}) = (the zeroless mass at level k)
   and then consider the Amice transform F(s) = integral_{Z_5^*} <u>^s d mu(u), a p-adic analytic function whose zeros correspond to n with 2^n zeroless. If this function has finitely many zeros (by Weierstrass preparation or Strassmann), we'd be done. But does such a function exist? The zeroless condition is a BASE-10 condition, mixing the 2-adic and 5-adic structures, so encoding it purely 5-adically may be impossible.

4. **p-adic Weierstrass preparation**: If we can write the "zeroless indicator" as a p-adic analytic function F(s) on Z_p (or an open subset), then Weierstrass preparation gives F(s) = p^a * u(s) * P(s) where P is a polynomial and u is a unit. The degree of P bounds the number of zeros. What is the structure of F, and can deg(P) be bounded independently of k?

5. **Iwasawa theory connection**: The 5-adic analytic structure of 2^n mod 5^k is closely related to Iwasawa theory for the cyclotomic Z_5-extension. The Kubota-Leopoldt p-adic L-function encodes arithmetic information about the tower Z/5^k Z. Can Iwasawa-theoretic methods detect the zeroless condition? The zeroless set W_k in Z/5^k Z is NOT a congruence condition (it depends on the base-10 representation, mixing 2 and 5), so it may not fit into the standard Iwasawa framework.

6. **The fundamental obstacle**: Strassmann's theorem is POWERFUL for bounding zeros of a SINGLE p-adic analytic function. Our problem is that the zeroless condition at level k involves |W_k| ~ 4.5^k separate residue classes, and we cannot combine them into a single analytic function without losing control of the zero count. Is this the essential reason p-adic methods fail, or is there a way around it?

### What has been killed (do not retry)
- 5-adic Baker: blocked because zeroless is avoidance (residue set), not closeness (small linear form).
- CRT factorization: the constraint is invisible mod 5^k alone (density 1.0).
- Strassmann applied term-by-term to each w in W_k: gives O(4.5^k) bound, much weaker than needed.

### Deliverable
(a) A construction of a p-adic analytic function whose zeros correspond to zeroless 2^n, with an analysis of whether its zero count can be bounded, OR
(b) A clear explanation of why p-adic analytic methods cannot reach this problem, identifying the specific point where the base-10 digit condition defeats the p-adic framework.

### References
- Strassmann: "Uber den Wertevorrat von Potenzreihen im Gebiet der p-adischen Zahlen" (1928)
- Robert: "A Course in p-adic Analysis" (Springer, 2000), Ch. 6
- Amice: "Les nombres p-adiques" (1975)
- Koblitz: "p-adic Numbers, p-adic Analysis, and Zeta-Functions" (Springer, GTM 58)
- Washington: "Introduction to Cyclotomic Fields" (Springer, GTM 83)
- Serre: "Abelian l-adic representations and elliptic curves" (1968)
- Kubota, Leopoldt: "Eine p-adische Theorie der Zetawerte" (1964)
- Colmez: "Fonctions d'une variable p-adique" (Asterisque 330, 2010)

---

## Summary: The Landscape of Approaches

| Direction | Status | Why it fails / what it needs |
|-----------|--------|------------------------------|
| Digit-by-digit | KILLED | 4.5^k barrier (growth > 1) |
| Multiplicative Fourier | KILLED | Density 1.0 mod 5^k |
| Mod 2^k density | KILLED | Density 1.0 mod 2^k |
| CRT factoring | KILLED | Invisible to factors |
| S-unit / Subspace | KILLED | Positive entropy, no compression |
| Two-bases (Senge-Straus) | KILLED | Zeroless is non-sparse |
| Baker / Matveev | KILLED | Height too large |
| Doubling automaton | KILLED | Isomorphic to digit counting |
| Finite bootstrap | KILLED | Period too large, tree supercritical |
| Borel-Cantelli / discrepancy | KILLED (standard) | Tseng blocks shrinking targets |
| Additive Fourier | KILLED (standalone) | 1/9 permanent obstruction |
| **Furstenberg rigidity** (F1) | **KILLED** | System is Kronecker (rank-1, zero entropy, no mixing). Rudolph/Host/EKL need positive entropy under higher-rank expanding actions. Only joining is product (eigenvalue mismatch), but product equidistribution gives no shrinking-target control. |
| **Bourgain / exponential sums** (F2) | **KILLED** | Requires controlling incomplete sums of length N ~ k with modulus 5^k (log-time regime). Korobov: no cancellation. Bourgain-Chang: needs N ~ q^delta, have N ~ log(q). Maynard: lower bounds for dense sets, not upper bounds for sparse orbits. Nilsequences: dynamics is 1-step, U^s adds nothing beyond Fourier. |
| **p-adic Strassmann** (F3) | **KILLED** | Zeroless condition at level k is a union of ~4.5^k 5-adic open balls (clopen set). No nonzero analytic function can vanish on an open ball. Product encoding has Weierstrass degree ~4.5^k. Mahler series need degree ~5^k. Iwasawa requires character structure; W_k is defined by digit cylinders. |

All 14 directions have been tested and killed across 18 independent analyses (9 prompt pairs).
Each direction fails for a distinct structural reason, but they converge on the same underlying gap:

**The problem requires exponential-scale quantitative control of a deterministic orbit
on a coupled archimedean + non-archimedean system, and no existing mathematical
framework provides such control.**

The problem likely requires genuinely new mathematics. The most precise formulation of
what is missing: a "log-time cancellation theorem" for incomplete exponential sums
sum_{n <= ck} e(h * 2^n / 5^k), showing nontrivial decay as k -> infinity when the
sum length N ~ k is logarithmic in the modulus 5^k. No current technique achieves
any cancellation in this regime.

---

## M3 Method: Meta-Level Prompts

Since all 14 M1-level directions are killed, the search has escalated to higher abstraction
levels via the **M3 method** (recursive meta-prompt generation). See:

**META_PROMPTS.md** (companion document)

This contains 9 prompts at three abstraction levels:
- **M2 (meta-meta)**: Method Discovery -- what TYPE of tool could work? (M2-A, M2-B, M2-C)
- **M3 (meta-meta-meta)**: Problem Topology -- what is the structure of the search space? (M3-A, M3-B)
- **M4 (meta-meta-meta-meta)**: Innovation Archaeology -- what class of innovation is needed? (M4-A, M4-B, M4-C)
- **Synthesis**: One-page integration of all findings

Recommended execution: M2-C -> M2-A -> M2-B -> M3-A -> M3-B -> M4-A -> M4-B -> M4-C -> Synthesis.
Each prompt should be paired (two independent AI systems) with the same kill criterion as M1.
