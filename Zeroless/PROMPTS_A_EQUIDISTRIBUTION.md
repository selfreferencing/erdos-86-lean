# Prompt Set A: Equidistribution and Exponential Sums

## Context for All Prompts

These prompts are informed by a comprehensive computational and theoretical analysis of the 86 Conjecture (2^86 is the largest power of 2 with no digit 0 in base 10). Seven computational experiments and 16 independent AI analyses have converged on a single conclusion:

**The problem is purely about equidistribution of 2^n mod 10^k.**

Every other approach has been ruled out:
- Carry dynamics: memoryless (Dobrushin coefficient = 0)
- Digit correlations: i.i.d. uniform to within 0.001
- Survivor tree: zero death rate, perfect 4.5 branching at every level through k=9
- Block renormalization: branching factor exactly 4.5^B, no reduction
- Global carry invariants: no quantity separates zeroless from non-zeroless
- Fourier: permanent obstruction (max coefficient ~1/9, not decaying)
- S-units/Subspace Theorem: dead (positive entropy, growing number of terms)
- Baker's method: no reduction to linear forms in logarithms possible

The problem reduces to: **improve the exponential sum bound for Sum_{n=1}^{N} e(2^n / 10^k) from exp(-c * k^{1/3}) cancellation to exp(-0.105 * k) cancellation.**

---

## Prompt A1: The Exponential Sum Gap

### For: Analytic number theorist specializing in exponential sums

You are an expert in exponential sum estimates, particularly for sequences involving exponential functions modulo growing moduli.

**The problem**: Prove that for all sufficiently large n, the decimal expansion of 2^n contains at least one digit 0. Equivalently, prove that the set E = {n : 2^n has no zero digit in base 10} is finite.

**What has been established computationally and theoretically**:

1. No zeroless 2^n exists for n = 87..50000 (verified computationally).
2. The problem reduces entirely to equidistribution. Specifically, we need to show that 2^n mod 10^k is "sufficiently equidistributed" among residue classes for k growing as ~0.3n.
3. The survivor set (residues mod 10^k with all nonzero digits) has density (9/10)^{k-1} and contains exactly 4 * 4.5^{k-1} elements out of the period T_k = 4 * 5^{k-1}. The survivor tree has zero death rate and perfect 4.5 branching -- no structural weakness.
4. The digit-level carry chain is perfectly memoryless (Dobrushin coefficient = 0). Digits of 2^n are empirically i.i.d. uniform on {0,...,9} with all correlations below 0.001.
5. The heuristic: for digit count k, about 3.32 values of n produce k-digit powers of 2, and the probability of all k digits being nonzero is (9/10)^{k-1}. The expected number of zeroless 2^n with >= 91 digits is ~0.0025.

**The quantitative gap**: The equidistribution of 2^n mod 10^k follows from irrationality of log_10(2). The best effective bounds come from exponential sum methods:

- **Korobov-type bounds**: For the sum S_k(N) = Sum_{n=1}^{N} e(2^n / 10^k), the best known cancellation gives |S_k(N)| << N * exp(-c * k^{1/3}) for some constant c > 0.
- **What we need**: To prove the conjecture, we need |S_k(N)| << N * (9/10)^k or equivalently exp(-0.105 * k) cancellation, where the bound holds uniformly for k up to ~0.3N.
- **The gap**: The exponent is k^{1/3} (known) vs k (needed). This is not a constant-factor gap but a qualitative difference in the rate of cancellation.

**Questions**:

1. The modulus 10^k = 2^k * 5^k has a very specific factorization. By CRT, 2^n mod 10^k = CRT(0 mod 2^k, 2^n mod 5^k) for n >= k. So the non-trivial content is entirely in 2^n mod 5^k. The sum becomes: S_k(N) = Sum_{n=1}^{N} e(2^n / 5^k) (up to phase factors from the 2^k component). Does the specific structure of 2 mod 5 (a primitive root mod 5, with multiplicative order 4 * 5^{k-1} mod 5^k) give any leverage beyond generic Korobov bounds?

2. The sequence 2^n mod 5^k is periodic with period T_k = 4 * 5^{k-1}. Within one period, it visits each residue class coprime to 5 exactly once (since 2 is a primitive root mod 5^k). So the exponential sum over one period is a complete character sum: Sum_{n=0}^{T_k - 1} e(2^n / 5^k) = Sum over all units mod 5^k of e(unit / 5^k). This is a Ramanujan-type sum. Can the explicit evaluation of this complete sum (which should give cancellation) be used to bootstrap bounds for incomplete sums?

3. The Bourgain-Chang bound for exponential sums Sum e(a * g^n / p) for g a primitive root mod p gives square-root cancellation for intervals of length > p^{1-epsilon}. Our situation has p = 5^k (prime power, not prime) and we need cancellation for intervals of length ~3k (about 3 values of n per digit count). Is there a Bourgain-Chang analogue for prime power moduli that could give sufficient cancellation for very short intervals?

4. Alternatively, Korobov's method uses bounds on double sums and Vinogradov-type estimates. For our specific base (2 mod 5), the doubling map x -> 2x mod 5^k is an automorphism of the multiplicative group (Z/5^k Z)*. This group is cyclic of order 4*5^{k-1}. Does the specific group structure (cyclic, with generator 2) give any special cancellation properties beyond what's available for generic generators?

5. A completely different angle: instead of bounding the exponential sum, could we use the STRUCTURE of the survivor set? The survivor set at level k is not just "random" -- it has the specific form {r mod 10^k : all digits of r are in {1,...,9}}. This set can be expressed as an intersection of congruence conditions: for each position j, r mod 10^{j+1} is NOT in {m * 10^j : m in Z} (i.e., digit j is not 0). Could a sieve-theoretic approach, bounding the probability that 2^n avoids ALL of these conditions simultaneously, work?

6. What is the current best result for the problem: "for all large n, at least one digit of 2^n equals some specific value d"? Is d=0 the hardest case, or are all digit values equally hard? (Note: d=0 has the special property that the last digit of 2^n is never 0, which gives a mild head start.)

**Deliverable**: Either (a) a strategy sketch for closing the k^{1/3} to k gap in the exponential sum exponent, exploiting the specific structure of 2 mod 5^k, or (b) a clear explanation of why this gap is fundamental and what would need to change (new techniques, conjectures) to close it.

---

## Prompt A2: The Discrepancy Approach

### For: Specialist in uniform distribution theory and discrepancy

You are an expert in uniform distribution modulo 1, discrepancy theory, and the distribution of exponential sequences.

**The problem**: Show that the sequence {n * log_10(2)} (mod 1) is sufficiently well-distributed that the first k digits of 2^n cannot all avoid 0 for k large enough (k ~ 0.3n).

**Key established facts**:

1. The sequence {n * alpha} with alpha = log_10(2) is equidistributed mod 1 (Weyl). But we need JOINT equidistribution of the k fractional parts that determine the k digits of 2^n.
2. The k-th digit from the right of 2^n is determined by 2^n mod 10^{k+1} (and thus by 2^n mod 5^{k+1} via CRT).
3. The problem is equivalent to: the point (2^n mod 5, 2^n mod 5^2, ..., 2^n mod 5^k) in the product space Z/5 x Z/5^2 x ... x Z/5^k must avoid a specific "forbidden" set (digits equal to 0) of density (1/10)^something at each coordinate.
4. Computationally: digits of 2^n are i.i.d. uniform to extremely high precision. All correlations < 0.001.
5. The first-zero position j(n) has strong modular structure: 38% of its variance is explained by n mod 2500 = n mod (4 * 5^4). This means the 5-adic orbit structure significantly predicts where the first zero appears.

**The specific question about discrepancy**:

The discrepancy D_N of the sequence {2^n / 5^k} (mod 1) for n = 1, ..., N satisfies:
- D_N >= c / N (Erdos-Turan lower bound, since the sequence has finite period T_k)
- D_N <= C * exp(-c' * k^{1/3}) (Korobov, via exponential sum bounds)

For the conjecture, we need the proportion of n in {1,...,N} with 2^n mod 10^k in the survivor set to be close to (9/10)^{k-1}. This requires:
- D_N(5^k) << (9/10)^k, i.e., discrepancy for modulus 5^k decays exponentially in k.

But Korobov gives only exp(-c*k^{1/3}) decay. The question:

1. Is there a multidimensional discrepancy result that could help? The constraint is on k SIMULTANEOUS digit positions. A bound on the joint discrepancy of (2^n mod 5, 2^n mod 5^2, ..., 2^n mod 5^k) that exploits the COMPATIBILITY between these (the natural projections: reducing mod 5^j gives mod 5^{j-1}) could potentially do better than treating each level independently.

2. The metric theory of uniform distribution gives: for ALMOST ALL alpha, the discrepancy of {2^n * alpha} is O(N^{-1+epsilon}). But log_10(2) is specific, not generic. Are there any results for specific algebraic or transcendental numbers that give better-than-Korobov discrepancy for exponential sequences?

3. The lacunary sequence perspective: {2^n * alpha} is a lacunary sequence (ratio between consecutive terms is 2, which is > 1). For lacunary sequences, the CLT holds (Erdos-Gal): the distribution of partial sums is Gaussian. But we need a LARGE DEVIATIONS result: the probability of ALL k digits being nonzero simultaneously. Is there a large deviations principle for lacunary sequences that could give the needed exponential decay?

4. Could a RECURSIVE approach work? The point 2^n mod 5^{k+1} determines 2^n mod 5^k (by reduction). So the "does digit k+1 equal 0?" question is a CONDITIONAL one given the answer at level k. This gives a martingale structure. Is there a martingale convergence theorem that implies the product of (conditional probability of nonzero at level j) must converge to 0?

5. The equidistribution at level k requires N >> T_k = 4 * 5^{k-1} to "see" all residues. But the number of n with digit count k is only about 3.32. So we're in the EXTREME short sum regime: far fewer samples than the period. In this regime, equidistribution results are trivially insufficient. How do number theorists handle this ultra-short regime? Is the problem fundamentally that we have too few n values per digit count k to apply equidistribution?

**Deliverable**: An assessment of which discrepancy/equidistribution tools come closest to the needed bound, and a precise identification of where each tool falls short.

---

## Prompt A3: The Complete Character Sum

### For: Algebraic number theorist or specialist in character sums over finite groups

**The problem** (stated algebraically):

Let G_k = (Z/5^k Z)* be the multiplicative group mod 5^k. This is cyclic of order phi(5^k) = 4 * 5^{k-1}, generated by g = 2.

Define the "zeroless set" Z_k subset of G_k as the set of units u mod 5^k such that CRT(0 mod 2^k, u mod 5^k) has no digit 0 when written in base 10 with k digits. This set has |Z_k| = 4 * 4.5^{k-1} elements (computationally verified through k=9).

The conjecture is equivalent to: for all sufficiently large k, the element g^n = 2^n mod 5^k is NOT in Z_k for any n with floor(n * log_10(2)) + 1 = k (i.e., 2^n has exactly k digits).

**What makes this hard**: There are approximately 3.32 values of n giving k-digit powers, but |G_k| = 4 * 5^{k-1} grows exponentially. So we need to show that ~3 specific elements of a group of size ~4 * 5^{k-1} all miss a set of density ~(9/10)^{k-1}.

**Questions about the algebraic structure of Z_k**:

1. **Character sum representation**: The indicator function 1_{Z_k} can be expanded in characters of G_k. Since G_k is cyclic, its characters are chi_j(g^n) = e(j * n / (4 * 5^{k-1})) for j = 0, ..., 4*5^{k-1}-1. The Fourier transform hat{1_{Z_k}}(j) = (1/|G_k|) * Sum_{u in Z_k} e(-j * ind_g(u) / |G_k|) gives the character sum coefficients. What is known about the distribution of these Fourier coefficients? Do they decay, or is there a persistent obstruction?

   **Known**: The Fourier spectrum of the zeroless set mod 10^k has max coefficient ~1/9 (this is the "Fourier obstruction" from our analysis). This means the character sums do NOT decay with k. Is this the complete picture, or are there subtleties with the multiplicative vs additive structure?

2. **The zeroless set as a combinatorial object**: Z_k is defined by k independent conditions (each digit nonzero). Each condition removes ~1/10 of the elements. If the conditions were INDEPENDENT in the group-theoretic sense, the density would be exactly (9/10)^k. Computationally, the density is (9/10)^{k-1} (not (9/10)^k, because the first digit is forced nonzero by being a unit). Are the digit conditions approximately independent when viewed through the lens of character sums?

3. **Lifting structure**: Z_k and Z_{k+1} are related by the natural projection G_{k+1} -> G_k. Each element of Z_k lifts to exactly 4 or 5 elements of Z_{k+1} (we computed this: zero death rate, 50/50 split between 4 and 5 children). This is the "perfect tree" structure. Can this lifting property be used to construct an inductive argument? Specifically: if we could show that for each u in Z_k, the conditional probability that a random lift to G_{k+1} lands in Z_{k+1} is at most 9/10, then the density bound follows by induction.

4. **Connection to p-adic analysis**: The projective limit of the G_k gives the group of 5-adic units Z_5*. The zeroless set Z_k defines a clopen subset of Z_5* (via the topology). The question becomes: does the sequence 2^n in Z_5* eventually leave this clopen set? This is a question about the 5-adic dynamics of multiplication by 2. Is there a p-adic analytic approach (e.g., p-adic measures, Iwasawa theory analogues) that could address this?

5. **Explicit computation request**: For k = 1, 2, 3, 4, what are the Fourier coefficients hat{1_{Z_k}}(j) for all j? Is there a pattern in how these coefficients evolve with k? Specifically, does the maximum non-trivial coefficient remain ~1/9, or does it change?

**Deliverable**: An algebraic characterization of the zeroless set Z_k within the cyclic group G_k, including its character sum expansion, and an assessment of whether the algebraic structure provides any route to proving that the orbit {2^n} eventually exits Z_k.

---

## Prompt A4: The Ultra-Short Sum Problem

### For: Analytic number theorist working on short character sums or short exponential sums

**The core difficulty** of the 86 Conjecture, distilled:

For each digit count k, there are approximately 3.32 values of n such that 2^n has exactly k decimal digits. We need to show that at least one of these ~3 values satisfies: "2^n mod 10^k has a zero digit."

The zero-digit condition excludes a set of density (9/10)^{k-1} among residues mod 10^k. So if the ~3 values were random, the probability that ALL avoid zero is approximately ((9/10)^{k-1})^3.32 = (9/10)^{3.32(k-1)}, which is tiny for large k.

But the values are NOT random. They are consecutive elements of the orbit n -> n+1 in the periodic sequence 2^n mod 5^k (period T_k = 4 * 5^{k-1}). Specifically, for k-digit powers, the relevant n values are approximately n_0, n_0+1, n_0+2 where n_0 = ceil((k-1)/log_10(2)).

**The problem is thus**: Show that among ~3 consecutive elements of the orbit of 2 in (Z/5^k Z)*, at least one falls outside the zeroless set Z_k (density ~(9/10)^{k-1}).

**Experimental finding**: Consecutive orbit elements have POSITIVELY correlated zerolessness. The ratio P(both n and n+1 are zeroless mod 10^k) / P(n is zeroless)^2 grows with k:
- k=1: 1.00, k=2: 1.05, k=3: 1.10, k=4: 1.16, k=5: 1.22, k=6: 1.28, k=7: 1.35, k=8: 1.43

So the naive independence estimate UNDERESTIMATES the survival probability by a growing factor.

**Questions**:

1. This is essentially a "short character sum" problem: estimate Sum_{n=n_0}^{n_0+2} 1_{Z_k}(2^n mod 5^k) where the sum has only ~3 terms. Standard exponential sum methods give non-trivial bounds only for sums of length >> sqrt(period). With period ~5^k and sum length ~3, we are absurdly far below the Polya-Vinogradov threshold. Is this problem provably out of reach for character sum methods?

2. The positive correlation between consecutive orbit elements comes from the carry chain: 2^{n+1} = 2 * 2^n, and doubling preserves trailing nonzero digits with elevated probability (the carry-persistence effect). Can this correlation be BOUNDED? Specifically, is there a theorem that the correlation ratio P(pair)/P(single)^2 is bounded by some function of k, or could it grow without bound?

3. Instead of fixing k and looking at ~3 values of n, could we fix n and look at ALL digit positions simultaneously? For a given n, 2^n has k ~ 0.3n digits, and we need at least one to be 0. This is a different formulation: instead of "short sum, large modulus," it's "one value, many conditions." Is this formulation more tractable?

4. The Erdos-Kac philosophy suggests that multiplicative functions behave like random variables. Can a version of Erdos-Kac for digit distributions give a probabilistic result like "for all but finitely many n, 2^n has a digit 0"?

5. Is the problem easier if we don't insist on EVERY large n, but instead ask for DENSITY? I.e., prove that the set of n with 2^n zeroless has density 0. (This is weaker than finiteness but might be more accessible.)

**Deliverable**: An honest assessment of whether the "~3 terms out of period ~5^k" short-sum problem is tractable with any known or foreseeable technique, and if not, what weaker results might be provable.

---

## Prompt A5: The 5-adic Dynamics Perspective

### For: Specialist in p-adic dynamics or arithmetic dynamics

**Setup**: Consider the map T: Z_5* -> Z_5* defined by T(x) = 2x (multiplication by 2 in the 5-adic integers). The orbit of 1 under T gives the sequence 2^n. The "zeroless condition" at precision k is: the natural image of x in (Z/5^k Z)* lies in the set Z_k of units whose CRT lift to Z/10^k Z has all nonzero digits.

**The conjecture**: The orbit {T^n(1) : n >= 0} eventually leaves the clopen set Z = projlim Z_k (the set of 5-adic integers whose base-10 expansion has no zero digit, interpreting the 5-adic integer via CRT with powers of 2).

**Experimental findings about the dynamics**:

1. The first-zero position j(n) (how many trailing nonzero digits 2^n has) has mean ~11 and is strongly correlated with n mod T_k (38% of variance explained by n mod 2500 at k=5).
2. The autocorrelation of j(n) at lag 1 is 0.328 (significant), with periodic oscillation at period 20 = T_2.
3. The maximum observed suffix depth is 115 (at n=7931 out of n tested to 50000). Record growth is slower than geometric model predicts.

**Questions**:

1. The map T is an isometry of Z_5* (since |2|_5 = 1). The orbit {2^n} is dense in Z_5* (since 2 is a topological generator). Density implies the orbit comes arbitrarily close to any point. The zeroless set Z has zero Haar measure (since its density at level k is (9/10)^{k-1} -> 0). Does density of the orbit combined with zero measure of Z immediately imply the orbit eventually leaves Z? NOT in general (dense orbits can stay in full-measure sets and still visit measure-zero sets infinitely often). But is there a quantitative equidistribution result for isometric orbits in Z_5* that would suffice?

2. The map T on G_k = (Z/5^k Z)* is a cyclic permutation (since 2 generates G_k). The "return time" to Z_k is the smallest m > 0 such that 2^m * u is in Z_k (for u in Z_k). What is the distribution of return times? If the mean return time grows faster than the period, then eventually 2^n cannot return to Z_k from outside.

3. The wandering rate: define W(k) = |{n in [0, T_k) : 2^n mod 10^k is zeroless}| = |Z_k| = 4 * 4.5^{k-1}. The fraction is W(k)/T_k = (9/10)^{k-1}. This is the "time spent in Z_k" per period. The conjecture says that for large k, the specific n-values corresponding to k-digit powers do not land in Z_k. Is there a dynamical systems result (e.g., Birkhoff-type) that converts the decaying sojourn fraction into an eventual exit for specific orbit segments?

4. Can the 5-adic logarithm help? The 5-adic log gives an isomorphism from a subgroup of Z_5* to 5*Z_5 (the "log" linearizes multiplication into addition). Under this isomorphism, the orbit 2^n maps to n * log_5(2). Does the zeroless set Z_k have a nice description in "log coordinates"? If so, the problem might reduce to a p-adic analogue of the equidistribution problem for linear sequences.

5. Are there results in p-adic Diophantine approximation that give effective bounds on how well the orbit {n * alpha} (for alpha = log_5(2) in Q_5) approximates given targets in Z_5? This would be a p-adic analogue of the Thue-Siegel-Roth theorem, applied to our specific setting.

**Deliverable**: An assessment of whether p-adic dynamical methods can convert the zero-measure / dense-orbit combination into a finiteness proof, identifying the key quantitative step needed.
