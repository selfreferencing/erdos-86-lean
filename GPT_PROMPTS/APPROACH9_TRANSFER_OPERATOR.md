# GPT Prompt: Transfer Operator Spectral Gap for Zeroless Powers of 2

## Role

You are a research mathematician specializing in transfer operators, spectral theory of matrices and operators, symbolic dynamics, and the arithmetic of multiplicative sequences modulo prime powers. Your expertise includes Perron-Frobenius theory, spectral gaps for Markov chains, Ruelle transfer operators, and the digit dynamics of exponential sequences (powers of 2 modulo 10^m). I need your help determining whether a specific finite-dimensional transfer operator has a spectral gap.

## Problem Background

**The Conjecture.** The set A = {n >= 1 : 2^n has no digit 0 in base 10} is finite, with max element 86.

**What Is Proved.**
1. Density zero (elementary, survival rate (23/25)^m).
2. Metric finiteness (Borel-Cantelli): for a.e. rotation parameter, the orbit hits the zeroless set only finitely often.
3. The gap: certifying theta = log10(2) is not exceptional.

**Why Transfer Operators.** The digit structure of 2^n mod 10^m is governed by a finite-state automaton. The orbit 2^m, 2^{m+1}, ..., 2^{m+T_m-1} mod 10^m (with T_m = 4*5^{m-1}) visits each residue class exactly once. The digits of 2^n mod 10^m are determined by the residue class, and the "next digit" operation (going from m digits to m+1 digits) is a transfer operation.

**Noda's Framework (arXiv:2510.18414).** Hideaki Noda defined a transfer operator for this problem:

M_m[h] is a matrix in C^{2^{m-1} x 2^m} defined by:
- Entry (i, t) = h(j) if t = 10i + j mod 2^m for some digit j in {0,...,9}, else 0.
- This encodes: "append digit j to state i, reduce mod 2^m, weight by h(j)."
- h: {0,...,9} -> C is a weight function on digits.

For the zeroless problem, h = 1_{nonzero}: h(0) = 0, h(d) = 1 for d = 1,...,9.

Noda proved:
- **Lemma 1 (Parity structure):** Column sums of M_m[h] equal E = sum_{even d} h(d) or O = sum_{odd d} h(d), depending on column parity.
- **Proposition 2:** lim sup Psi_m(h) <= log(max{E,O}/5) where Psi_m is the normalized log generating function over the orbit.
- **Proposition 3:** When E = O, lim Psi_m(h) = log(E/5) = log((1/10)*sum h(d)).

For h = 1_{nonzero}: E = 4 (digits 2,4,6,8), O = 5 (digits 1,3,5,7,9). So max{E,O}/5 = 1, giving Psi <= 0, meaning the fraction of zeroless orbit elements is at most (9/10)^m * (1 + o(1)).

**What Noda does NOT do:** Spectral analysis. He explicitly states: "This note confines itself to combinatorial and matrix-theoretic aspects and does not pursue analytic or dynamical interpretations." A spectral gap for M_m[1_{nonzero}] would directly imply equidistribution of the zeroless indicator along the orbit, potentially closing the conjecture.

## CRITICAL UPDATE: Dirichlet Polynomial Rewrite of Fourier Coefficients

A prior analysis (Approach 6A) established a connection between the circle Fourier coefficients of the zeroless indicator 1_{F_m} and Kempner-type Dirichlet polynomials. Specifically:

**The Dirichlet polynomial rewrite.** Let N_m = {m-digit zeroless integers} (the set of integers in [10^{m-1}, 10^m) with all digits nonzero). Then the circle Fourier coefficient satisfies:

hat{1_{F_m}}(k) = (1/ln 10) * sum_{n in N_m} n^{-1-it_k} + O(k * (9/100)^m)

where t_k = 2*pi*k / ln 10. The main term is a **twisted Dirichlet polynomial** over the zeroless integers, evaluated at s = 1 + it_k.

**Why this matters for transfer operators.** The set N_m has a recursive structure: an m-digit zeroless integer is 10*a + d where a is an (m-1)-digit zeroless integer and d in {1,...,9}. This recursion is exactly the digit-appending operation that Noda's transfer operator M_m encodes. The transfer operator should therefore provide a recursion for the twisted Dirichlet polynomial sum_{n in N_m} n^{-s}, connecting the spectral theory of M_m to the analytic behavior of this Dirichlet series.

**The Kempner connection.** The Kempner series sum_{n zeroless} 1/n converges to approximately 23.10. More generally, the Dirichlet series D(s) = sum_{n zeroless} n^{-s} converges for Re(s) > 0 (since the zeroless integers have density zero). The transfer operator should control the analytic continuation and pole structure of D(s), which in turn controls the Fourier coefficients hat{1_{F_m}}(k) and hence the Weyl sum that governs the conjecture.

**Experimental context.** Experiments 36 and 37 established:
- |hat{1_{F_m}}(k)| = C(k) * (9/10)^{m-1} where C(k) is stable across m for m >= 4.
- The triangle-inequality bound on the Weyl sum (bounding each Fourier mode separately) diverges due to harmonic-sum structure. Phase cancellation or a direct dynamical argument is needed.
- A coboundary analysis showed the low-frequency part (|k| <= poly(m)) of the Weyl sum is already controlled. The bottleneck is the high-frequency tail, where the Dirichlet polynomial structure may provide additional decay or cancellation beyond the naive 1/k bound.

## The Transfer Operator in Detail

### The Orbit Structure

2^n mod 10^m for n >= m cycles with period T_m = 4*5^{m-1}. The orbit visits exactly the residues that are coprime to 5 (since 2^n is never divisible by 5) and have the correct 2-adic valuation. The orbit set is:

Omega_m = {2^n mod 10^m : m <= n < m + T_m}

with |Omega_m| = T_m = 4*5^{m-1}.

### The Digit Transition

Going from m digits to m+1 digits: if 2^n mod 10^m = r, then 2^n mod 10^{m+1} = r + d*10^m for some digit d in {0,...,9}. The digit d is determined by r and n (more precisely, by the higher-order bits of 2^n).

The transition from the residue class viewpoint: the orbit element r at level m lifts to an element r' at level m+1 with r' mod 10^m = r and the (m+1)-th digit being determined.

### The Generating Function

Noda defines:
Psi_m(h) = (1/m) * log((1/|Omega_m|) * sum_{omega in Omega_m} prod_{j=1}^{m} h(omega_j))

where omega_j is the j-th digit of omega. This is the log-average of the product weight h(d_1)*...*h(d_m) over the orbit.

For h = 1_{nonzero}: prod h(d_j) = 1 if all digits nonzero, 0 otherwise. So:
exp(m * Psi_m) = (# zeroless elements in Omega_m) / |Omega_m| = Z_m / T_m

where Z_m is the number of zeroless orbit elements.

### Connection to the Conjecture

N_m (zeroless powers of 2 with m digits) counts how many of the L_m ~ 3.3m transition-zone orbit elements are zeroless. The full orbit has T_m ~ 0.8*10^m elements, of which Z_m are zeroless. The fraction Z_m/T_m ~ (9/10)^m decays, but this alone does not prove N_m = 0 (the transition zone could be biased toward zeroless elements).

**A spectral gap would show** that the zeroless indicator is equidistributed along the orbit, meaning the transition-zone count N_m ~ L_m * Z_m/T_m ~ L_m * rho_m -> 0, which forces N_m = 0 for large m.

## Questions for You

### Question 1: Spectral Gap for M_m[1_{nonzero}]

Define the transfer operator T_m: C^{Omega_m} -> C^{Omega_{m-1}} by:

(T_m f)(r) = sum_{r' in Omega_m, r' mod 10^{m-1} = r} 1_{nonzero}(d_m(r')) * f(r')

where d_m(r') is the m-th digit of r'. This maps functions on the m-digit orbit to functions on the (m-1)-digit orbit, weighted by the zeroless indicator.

Equivalently, using Noda's matrix M_m = M_m[1_{nonzero}]:

T_m = M_m restricted to orbit elements.

**Does T_m have a spectral gap?** Specifically:
- The leading eigenvalue is (9/10) * 5^{m-1}/5^{m-2} ... actually, we need to be more careful about normalization.
- After normalizing so the leading eigenvalue is 1, is the second eigenvalue strictly less than 1?
- Is there a UNIFORM spectral gap (independent of m)?

### Question 2: The Normalized Operator

Define the normalized operator:
L_m = (1/rho_eff) * T_m

where rho_eff is chosen so L_m has leading eigenvalue 1 (i.e., L_m preserves the total "zeroless mass"). The spectral gap is:

gap_m = 1 - |lambda_2(L_m)|

where lambda_2 is the second-largest eigenvalue.

**If gap_m >= c > 0 uniformly in m,** then for any initial distribution concentrated on a set of measure delta within the orbit, the zeroless indicator decorrelates exponentially: after O(1/c * log(1/delta)) steps, the weighted measure is within O(exp(-c*steps)) of the equilibrium.

**Can you compute or bound the spectral gap?** For small m (m = 2,3,4), the operator T_m acts on spaces of dimension 4*5^{m-2}, which is 4 (m=2), 20 (m=3), 100 (m=4). These are small enough for explicit computation.

### Question 3: The Parity Structure and Spectral Decomposition

Noda's Lemma 1 shows the column sums of M_m[h] depend only on parity (E for even columns, O for odd). This means M_m has a block structure with respect to the parity decomposition.

**Does this block structure give information about the spectrum?** Specifically:
- The "parity-balanced" subspace (where the function is constant on parity fibers) is an invariant subspace.
- The "parity-imbalanced" subspace (where the function changes sign on parity fibers) may have a different spectral radius.
- The spectral gap might come from the gap between the parity-balanced eigenvalue and the parity-imbalanced eigenvalue.

**The parity imbalance in the problem:** E = 4, O = 5 for h = 1_{nonzero}. The ratio O/E = 5/4 means odd residues are more "fertile" (produce 5 zeroless children vs 4). This creates a parity bias in the orbit. Does this bias show up as a spectral gap?

### Question 4: Markov Chain Interpretation

The orbit of 2^n mod 10^m, viewed from the m-th digit backward, is (approximately) a Markov chain. The digit d_j of 2^n depends on n mod 10^j, and the transition probabilities from d_j to d_{j+1} are determined by the multiplication-by-2 map on Z/10^{j+1}Z.

**Is this Markov chain ergodic?** If so, the digit distribution converges to a stationary measure, and the spectral gap of the transition matrix controls the mixing time.

Maynard (Inventiones 2019) used a Markov process comparison for his restricted-digit primes result: "moment estimates obtained by comparison with a Markov process." His Markov process may be exactly this digit transition chain.

**Can we adapt Maynard's Markov comparison to our setting?** His result shows that the digit indicator for restricted-digit PRIMES has the right distribution. Our problem is about restricted-digit POWERS OF 2, which have a much more rigid orbit structure (deterministic, periodic) than primes (pseudo-random).

### Question 5: Connection to Equidistribution

A spectral gap for the transfer operator implies exponential mixing, which implies equidistribution. Specifically:

If T_m has spectral gap c, then for any "test function" g on the orbit:

|sum_{j in transition zone} g(2^{m+j} mod 10^m) - (L_m / T_m) * sum_{all orbit} g(omega)| <= exp(-c * something) * ||g||

Taking g = 1_{zeroless}, the left side is |N_m - L_m * Z_m / T_m| = |N_m - L_m * rho_m * (1 + o(1))|.

**The key question:** does the exponential mixing bound give |N_m - L_m*rho_m| < 1 for large m?

The transition zone has L_m ~ 3m elements out of T_m ~ 0.8*10^m total. The "time" in the Markov chain is m (number of digits), not L_m. The mixing time needs to be O(m) or less for the transition zone to be well-mixed.

**What is the effective mixing time of this chain, and how does it compare to the transition zone length?**

### Question 6: Computational Verification for Small m

For m = 2: T_m = 20, the orbit is {2, 4, 8, 16, 32, 64, 28, 56, 12, 24, 48, 96, 92, 84, 68, 36, 72, 44, 88, 76} mod 100. The transfer operator T_2 acts on C^4 (the residues mod 10 in the orbit: {2, 4, 6, 8}).

**Can you write out the 4x4 transfer matrix for m=2 and compute its eigenvalues?** This would give the spectral gap explicitly for the smallest nontrivial case.

For m = 3: T_m = 100, orbit mod 1000. The transfer matrix is 20x20. Still computable.

For m = 4: T_m = 500, orbit mod 10000. Transfer matrix is 100x100.

**Do the eigenvalues show a consistent spectral gap as m increases?**

### Question 7: Transfer Operator Recursion for the Twisted Dirichlet Polynomial

The Dirichlet polynomial rewrite gives hat{1_{F_m}}(k) ~ (1/ln 10) * sum_{n in N_m} n^{-1-it_k}. The set N_m has recursive structure: n in N_m iff n = 10*a + d with a in N_{m-1} and d in {1,...,9}. So:

sum_{n in N_m} n^{-s} = sum_{a in N_{m-1}} sum_{d=1}^{9} (10a + d)^{-s}

**Does the transfer operator M_m provide a useful recursion for this sum?** Specifically:

(a) Define the "twisted" transfer operator M_m^{(s)}: the (i,t) entry is (10i + j)^{-s} (instead of h(j)) when t = 10i + j mod 2^m. Can the spectrum of M_m^{(s)} control the growth of sum_{n in N_m} n^{-s} as m -> infinity?

(b) At s = 1 + it_k with t_k = 2*pi*k/ln 10, the sum becomes the Fourier coefficient (up to normalization). The transfer operator at this specific "frequency" parameter should have a spectral radius that controls |hat{1_{F_m}}(k)|. Can you determine whether this spectral radius gives decay beyond the naive (9/10)^{m-1} * C(k) bound? Even a logarithmic improvement in C(k) (e.g., C(k) = o(1/k)) would break the harmonic-sum barrier.

(c) For the standard (untwisted) case s = 1, the sum is sum_{n in N_m} 1/n, which is the m-th partial Kempner sum. The full Kempner series converges to ~23.10. Does the transfer operator at s = 1 have a spectral gap that explains this convergence, and does the gap persist for s = 1 + it with t != 0?

### Question 8: Meromorphic Continuation of the Zeroless Dirichlet Series

Define the Dirichlet series D(s) = sum_{n : all digits of n are nonzero} n^{-s}. This converges for Re(s) > 0 (since the zeroless integers have logarithmic density zero, actually density ~ C * (log N)^{-delta} for some delta > 0 related to the base-10 structure).

(a) **Does D(s) have meromorphic continuation to Re(s) > -epsilon for some epsilon > 0?** If so, what are its poles? The digit-product structure (each zeroless n is determined by its digits d_1,...,d_m in {1,...,9}) suggests a factorization or functional equation. The transfer operator M_m should encode this structure.

(b) **Poles on the line Re(s) = 0.** The behavior of D(it) for real t controls the Fourier transform of the zeroless counting function. If D(s) has no poles on Re(s) = 0 except possibly at s = 0, this would give strong equidistribution results for the zeroless indicator.

(c) **Connection to the Hurwitz zeta function.** The sum sum_{d=1}^{9} (10a + d)^{-s} resembles a truncated Hurwitz zeta sum. Specifically, sum_{d=0}^{9} (10a + d)^{-s} = (10a)^{-s} * sum_{d=0}^{9} (1 + d/(10a))^{-s}. For the zeroless case, the d = 0 term is dropped. Does this Hurwitz connection give analytic continuation tools?

(d) **The key question for the conjecture.** If the transfer operator M_m^{(1+it)} has spectral radius strictly less than 9/10 for all t != 0, then |hat{1_{F_m}}(k)| decays FASTER than (9/10)^{m-1} for k != 0. This extra decay, even by a factor of m^{-epsilon}, would make the Weyl sum convergent and close the conjecture. Is there a spectral gap between the t = 0 and t != 0 cases?

## What Would Constitute a Solution

**Best case (spectral gap route):** A proof that the transfer operator T_m[1_{nonzero}] has a spectral gap >= c > 0 uniformly in m, with the mixing time O(m) or less. Combined with L_m ~ 3m (the transition zone length), this would show N_m ~ L_m * rho_m + O(exp(-c*m)) = o(1), forcing N_m = 0 for large m.

**Best case (Dirichlet polynomial route):** A proof that the twisted transfer operator M_m^{(1+it)} has spectral radius strictly less than 9/10 for all t != 0, giving |hat{1_{F_m}}(k)| = o((9/10)^m / k) for k != 0. This would make the Weyl sum convergent and directly prove N_m = L_m * rho_m + o(1) = o(1).

**Good case:** An explicit computation showing the spectral gap for m = 2,...,10, with a clear pattern suggesting uniform gap. Alternatively, computation of the spectral radius of M_m^{(1+it_k)} for several values of k and m, showing it is strictly below 9/10 with a consistent margin.

**Partial result:** A proof that the Markov chain interpretation gives exponential mixing for the digit distribution of 2^n, or a meromorphic continuation of D(s) with controlled poles, without fully connecting to the transition-zone count N_m. Either would be valuable as a step toward the conjecture.

## Key Constants

- theta = log10(2) = 0.30102999566398...
- T_m = 4*5^{m-1} (orbit period)
- L_m = ceil(m/theta) ~ ceil(3.32*m) (transition zone length)
- rho_m ~ (9/10)^{m-1} (zeroless measure)
- Z_m = # zeroless orbit elements at level m
- E = 4 (even zeroless digits: 2,4,6,8)
- O = 5 (odd zeroless digits: 1,3,5,7,9)
- Parity survival rates: even parents -> 4 children, odd parents -> 5 children
- Noda's Proposition 2: Psi_m <= log(max{E,O}/5) = 0

## References

- Noda, "Upper Bounds for Digitwise Generating Functions of Powers of Two," arXiv:2510.18414 (2025)
- Maynard, "Primes with restricted digits," Invent. math. 217: 127-218 (2019)
- Lagarias, "Ternary expansions of powers of 2," arXiv:math/0512006
- Banks, Conflitti, Shparlinski, "Character sums over integers with restricted g-ary digits," Illinois J. Math. 46 (2002)
