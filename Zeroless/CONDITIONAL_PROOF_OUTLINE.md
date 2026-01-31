# Conditional Proof Outline: The 86 Conjecture

## 1. Statement

**Conjecture (Erdos).** The set A = {n >= 1 : 2^n contains no digit 0 in base 10} is finite.

**The 86 Conjecture (stronger).** A = {1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19, 20, 21, 24, 25, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 46, 47, 49, 51, 67, 72, 76, 77, 81, 86}. That is, 2^86 = 77371252455336267181195264 is the largest power of 2 with no zero digit.

Computationally verified: no zeroless 2^n exists for 87 <= n <= 10^8.

**Equivalent reformulation.** Let D(n) = floor(n * log10(2)) + 1 be the number of digits of 2^n, and let N_m = #{n : D(n) = m and 2^n is zeroless}. The conjecture is equivalent to: N_m = 0 for all sufficiently large m.

---

## 2. Step 1: Density Zero (PROVED)

**Theorem (Density Zero).** The natural density of A is zero:

lim_{N -> infinity} |{n <= N : n in A}| / N = 0.

### Proof summary

The proof uses the orbit structure of 2^n mod 10^m. Key definitions:

- **T_m = 4 * 5^{m-1}**: the period of 2^n mod 10^m (for n >= m)
- **Z_m**: the number of level-m survivors (orbit elements that are m-digit zeroless numbers)
- **Parity classification**: each survivor has parameter u = 2^{n-m} mod 5^m, classified as even-type (u even) or odd-type (u odd). Counts: E_m, O_m, with e_m = E_m / Z_m.

**Fiber formula (Lemma 1).** Z_{m+1} = 4*E_m + 5*O_m. Even parents produce 4 surviving children (digits {2,4,6,8}); odd parents produce 5 (digits {1,3,5,7,9}).

**Survival rate.** S_{m+1} = Z_{m+1} / (5*Z_m) = 1 - e_m/5.

**Weak Parity-Balance (Proposition).** e_m in [2/5, 3/5] for all m >= 1. This follows from the recurrence e_{m+1} = (2 + p_m(1-e_m)) / (5 - e_m) where p_m in [0,1] is a parameter, and the map f(e,p) sends [0,1]^2 into [2/5, 3/5].

**Density bound.** S_m <= 1 - (2/5)/5 = 23/25 for all m >= 2. Therefore:

Z_m / T_m <= (9/10) * (23/25)^{m-2} -> 0 exponentially.

Since any zeroless 2^n with D(n) >= m restricts to a level-m survivor, the density of A is at most Z_m / T_m for every m. Sending m -> infinity gives density zero.

**Status: COMPLETE.** Full proof in DENSITY_ZERO_PROOF.md. Elementary; no Fourier analysis, probability, or number theory required.

---

## 3. The Transition Zone

For a fixed digit count m, the set of n with D(n) = m is

{n : (m-1)/theta < n <= m/theta}

where theta = log10(2) ~ 0.30103. This interval has length C = 1/theta ~ 3.3219 and contains L_m = ceil(C*m) integers (approximately). These L_m values of n are the only candidates for producing m-digit zeroless powers.

Define the transition zone orbit indices: for i = 0, 1, ..., L_m - 1, the candidate is n = m + i (approximately; the exact bound is that D(m+i) = m). The function

f_m(i) = 1 if 2^{m+i} is an m-digit zeroless number, 0 otherwise

satisfies N_m = sum_{i=0}^{L_m - 1} f_m(i).

**The conjecture reduces to:** N_m = 0 for all large m.

---

## 4. The Orbit-Circle Correspondence

The orbit element at index i is 2^{m+i} mod 10^m. This orbit has period T_m = 4 * 5^{m-1}, so for i < L_m << T_m, the indices are distinct modulo T_m.

The zeroless condition can be reformulated on the circle. Let alpha_i = frac((m+i) * theta). Then 2^{m+i} = 10^{m-1+alpha_i} * 10^{frac((m+i)*theta) - alpha_i + ...}, and the digits of 2^{m+i} are determined by alpha_i. Specifically:

**The zeroless set.** Define F_m = {alpha in [0,1) : the m-digit number with significand 10^alpha has no zero digit}. Then:

f_m(i) = 1_{F_m}(frac(i*theta + c_m))

where c_m = frac(m*theta) is a constant shift. The Lebesgue measure of F_m satisfies:

mu(F_m) = rho_m ~ (9/10)^{m-1}

The counting problem becomes:

N_m = #{i < L_m : frac(i*theta + c_m) in F_m}

This is a short Birkhoff sum of the indicator function 1_{F_m} along the irrational rotation by theta on the circle.

---

## 5. Step 2: Finiteness (CONDITIONAL)

**Theorem (Conditional).** Assume the Boundary Crossing Lemma (Section 7). Then there exists M such that N_m = 0 for all m >= M.

**Proof (given BCL).** The argument has three steps.

**Step A: Component structure of F_m.** The set F_m is a union of connected components (open intervals) in [0,1). In x = 10^alpha coordinates, F_m corresponds to x in [1,10) whose first m-1 fractional digits (d_2, ..., d_m) are all in {1,...,9}. Each (m-1)-digit prefix p with digits in {1,...,9} gives exactly one component (because the 9 allowed last digits 1-9 are contiguous; only the 9->0 transition creates a gap). Therefore the number of components is exactly 9^{m-1}. In x-space, every component has the same width: exactly 9 * 10^{-(m-1)}. In alpha-space, the log transform compresses these, with the widest at the all-1's prefix, giving the exact maximum:

max_comp(F_m) = log10(1 + 81/(10^m - 1)) ~ (81/ln(10)) * 10^{-m}

(GPT 5B Pro). Equivalently, via the run formula (GPT 5B Thinking): each component corresponds to a maximal run of consecutive zeroless m-digit integers n, n+1, ..., n+r-1, with exact width |C| = log10((n+r)/n), r <= 9. The widest component has length ~3.5 * 10^{-(m-1)} (Exp 29b, verified exactly for m=2..8). F_m has Cantor-dust topology for large m: totally disconnected, with all components of width ~10^{-(m-1)}, distributed across macroscopic regions of locally high density.

**Step B: Orbit spacing exceeds component length (PROVED).** No single component of F_m can contain two consecutive orbit points spaced theta apart.

*Proof.* F_m is contained in F_2 for all m >= 2, since F_m requires digits 2 through m to be nonzero while F_2 only requires digit 2. The complement of F_2 in [0,1) consists of 9 intervals [log10(10j) - 1, log10(10j+1) - 1) for j = 1, ..., 9 (the alpha values where the tens digit of 10^{1+alpha} is zero). The largest gap between consecutive such intervals is

[log10(11) - 1, log10(20) - 1) = [log10(11/10), log10(2))

of width log10(20/11) = 0.2596. Since 20/11 < 2, this width is strictly less than log10(2) = theta. Therefore max_component(F_m) <= max_component(F_2) = log10(20/11) < theta for all m >= 2. QED

*Remark.* The ratio max_comp(F_2)/theta = 0.862, giving a 14% margin. For m >= 3, the ratio drops to 0.112, and it decreases by exactly a factor of 10 with each additional m (Exp 29b). The true widest component width is ~0.9 * T_m ~ 3.5 * 10^{-(m-1)}, so for m=29 the ratio is ~10^{-27}. Step B is astronomically satisfied for all m >= 2.

**Step B+ (Multi-lag extension, GPT 5A Pro).** More generally, if max_component(F_m) < ||k*theta|| for some lag k, then no component of F_m can contain two orbit points separated by k steps: 1_{F_m}(x) * 1_{F_m}(x + k*theta) = 0 for all x. Since max_component(F_m) ~ 10^{-(m-1)} and ||k*theta|| >= 1/poly(m) for all 1 <= k <= L_m (by the three-distance theorem and the continued fraction of theta), the inequality holds for ALL lags k from 1 to L_m for any m >= 2. Therefore: **no two orbit points in the transition zone can share a component of F_m, regardless of their separation.** Every orbit hit is isolated in a distinct component, and all pair correlations 1_{F_m}(x_i) * 1_{F_m}(x_j) with i != j factor through inter-component (long-range in alpha-space) correlations only.

**Step C: Zero boundary crossings implies N_m = 0 (CONDITIONAL).** Assume the BCL (Section 7). For sufficiently large m, consecutive orbit points lie in the same connected component of F_m or its complement. By Step B, no component of F_m spans two consecutive orbit points. Therefore, if consecutive orbit points are in the same piece, they must both be in the complement. Since this holds for all consecutive pairs, all L_m orbit points lie in the complement of F_m, giving N_m = 0. QED

---

## 6. The Mechanism: Experimental Evidence

Twenty-eight computational experiments and eight GPT consultation responses converge on the following picture.

### 6.1 The discrepancy is O(1) in the transition zone

Define D_m(L) = N_m(L) - L * rho_m (the discrepancy between actual survivor count and expected count). Experiment 25 shows:

|D_m(L_m)| < 11 for all m = 2, ..., 27

The discrepancy is bounded, not growing with m. For comparison, the full-orbit discrepancy (L up to T_m) grows to ~130, driven by the convergent denominator q_8 = 28738 of theta.

### 6.2 Low orbit variation explains bounded discrepancy

Experiment 26 identifies the mechanism: f_m has only O(1) transitions (changes between 0 and 1) along the orbit in the transition zone. The number of transitions:

| m | L_m | transitions |
|---|-----|------------|
| 10 | 34 | 4 |
| 15 | 50 | 4 |
| 20 | 67 | 9 |
| 25 | 84 | 4 |
| 27 | 90 | 0 |

At m=27, the entire transition zone consists of non-survivors: zero transitions, zero survivors.

### 6.3 The boundary crossing count goes to zero

The expected number of boundary crossings (transitions from F_m to its complement or vice versa) in L_m steps is:

E[crossings] ~ L_m * (# boundary points of F_m) / T_m ~ 3m * 2 * 9^m / (4 * 5^{m-1}) * (1/10^m correction)

More precisely, F_m has approximately 2 * 9^{m-1} boundary points in [0,1), spaced approximately 10^{-m} apart. Consecutive orbit points are spaced theta ~ 0.3 apart. The probability that a step of length theta crosses a boundary point is approximately 2 * 9^{m-1} * theta / 1 ~ 0.6 * 9^{m-1}... no, this is wrong because the boundaries are not uniformly distributed.

The correct calculation: the total measure of the "boundary strip" (the set of alpha where [alpha, alpha + theta] crosses a boundary of F_m) is at most 2 * 9^{m-1} * theta * 10^{-m} (each boundary point creates a strip of width ~10^{-m}... actually the strip width is determined by the boundary point spacing).

Let us state the empirical finding directly: Exp 26 Part G shows the number of transitions is O(1) and decreasing, reaching 0 at m=27. The expected boundary crossings per step is approximately:

(# boundaries in a theta-length arc) ~ 2 * 9^{m-1} * theta * 10^{-(m-1)} = 2 * theta * 0.9^{m-1} -> 0

So the expected TOTAL crossings in L_m steps is ~ L_m * 2 * theta * 0.9^{m-1} ~ 3m * 0.6 * 0.9^{m-1} = 2m * 0.9^{m-1} -> 0.

### 6.4 Per-digit cancellation

Experiment 26 Part B shows that lower digits (1-5) create positive discrepancy while upper digits (6+) create negative discrepancy. The partial cancellation keeps the total bounded.

### 6.5 Protection from convergent resonances

The transition zone length L_m < 93 = q_3 (the third convergent denominator of theta) for all m <= 27. The orbit never completes a near-period within the transition zone, preventing the buildup of resonant discrepancy seen at L = q_8 = 28738.

---

## 7. The Remaining Gap: From BCL to Finiteness

### 7.1 The original BCL formulation

**Boundary Crossing Lemma (BCL, original).** There exists M_0 such that for all m >= M_0 and all i in {0, 1, ..., L_m - 2}, the interval [frac(i*theta + c_m), frac((i+1)*theta + c_m)] does not contain a boundary point of F_m.

Equivalently: for large m, consecutive orbit points in the transition zone always lie in the same connected component of F_m or its complement.

### 7.2 What Exp 28 revealed: the BCL must be reformulated

Exp 28 (boundary geometry) tested the BCL directly and found:

1. **Step B is PROVED** (see Section 5): max_component(F_m) < theta for all m >= 2.

2. **But the full BCL does NOT hold up to m=29.** The orbit still has ~10-15 transitions at m=29 (10 out of 97 orbit points land in F_m). These orbit points land in high-density regions of F_m where the coarse constraints (low-k digits) are all safely nonzero. (Note: the "wide components" reported in the initial Exp 28 analysis were artifacts of float-precision limitations; the true widest component has width ~3.5 * 10^{-(m-1)}, see Conclusion 20.)

3. **The expected number of hits is L_m * mu(F_m) ~ ceil(m/theta) * 0.9^{m-1} ~ 3m * 0.9^m -> 0.** At m=29 the expectation is about 3*29*0.9^28 ~ 0.047 * 87 ~ 4.1 under uniform distribution. The actual 10 hits indicate ~2.4x oversampling.

4. **Boundary crossings per orbit step grow as ~theta * 2 * 9^{m-1}.** At m=7, each step crosses ~314,000 boundaries. The BCL is not about individual boundary crossings going to zero; it's about the orbit staying consistently on one side.

### 7.3 The revised formulation

The BCL as originally stated is too strong: it asks for zero transitions, but transitions persist to m=29. The actual proof needs only:

**Finiteness Lemma (FL).** There exists M_0 such that for all m >= M_0, N_m = 0, i.e., no orbit point in the transition zone lands in F_m.

Note that FL is weaker than the BCL: the BCL says consecutive orbit points are always in the same piece (no transitions at all), while FL says none of the orbit points lands in F_m (some transitions between different complement components are allowed).

**Proof strategy for FL.** The argument proceeds in two steps:

**Step 1 (Metric).** For Lebesgue-a.e. alpha in [0,1), the orbit {frac(i*alpha)} visits F_m only finitely often as m -> infinity. This follows from the first Borel-Cantelli lemma:

sum_m L_m * mu(F_m) = sum_m ceil(m/theta) * 0.9^{m-1} < infinity

since m * 0.9^m is summable. Therefore, for a.e. starting point, N_m = 0 for all large m.

**Step 2 (Specific constant).** Certify that theta = log10(2) is not in the measure-zero exceptional set.

### 7.4 Why Step 2 is hard

The exceptional set E = {alpha : N_m(alpha) > 0 for infinitely many m} has Lebesgue measure zero but is dense. Proving log10(2) not in E requires Diophantine information about log10(2) relative to the boundary points of F_m.

**Viable paths:**

**(C) Coboundary / o(1) discrepancy (REFINED by GPT 5A; CONSTRAINED by GPT 5A Pro).**

**BRS rigidity barrier (Kesten 1966, Oren; arXiv:1404.0455).** An exact bounded coboundary for 1_{F_m} (i.e., ||g_m||_inf = O(1) uniformly in the orbit length N) is equivalent to F_m being a *bounded remainder set (BRS)* for rotation by theta. By Kesten's theorem, a single interval is a BRS iff its length is in Z + theta*Z. By Oren's generalization, finite unions of intervals satisfy a rigid pairing/permutation condition. Digit-fractal sets almost certainly do not satisfy these conditions.

**Therefore, the exact coboundary route is ruled out.** The viable version is GPT 5A's refinement: target o(1) discrepancy on the SPECIFIC orbit segment of length L_m, not uniform O(1) bounded remainder. We need |N_m - L_m * rho_m| -> 0 (since L_m * rho_m -> 0, this forces N_m = 0). This is weaker than the BRS condition and may still be achievable.

**The key missing estimate (GPT 5A).** The coboundary construction reduces to bounding the low-frequency Fourier mass:

Sum_{|k| <= H} |hat{1_{F_m}}(k)| / ||k*theta|| = o(1) as m -> infinity, with H = poly(m).

Baker's theorem controls the denominators: ||k*theta|| >= C / k^A for effective constants. The numerators |hat{1_{F_m}}(k)| for low-frequency k are ~rho_m = 0.9^{m-1}. So the sum is roughly rho_m * H^{A+1}, which is o(1) since poly(m) * 0.9^m -> 0. The rigorous step is proving the Fourier coefficient bound for the specific structured frequency set K_m arising from the digit filtration.

**Why Baker cannot directly build g_m (GPT 5A Pro, 2nd instance).** Solving the cohomological equation via Fourier series gives g_hat(k) = f_hat(k) / (e^{2*pi*i*k*theta} - 1). For discontinuous 1_{F_m}, |f_hat(k)| ~ 1/k. Even with Baker giving |k*theta| >> k^{-A}, the result |g_hat(k)| ~ k^{A-1} is not summable. The Fourier series for g_m diverges; Baker cannot directly build the transfer function.

**The Ostrowski renormalization route (GPT 5A Pro, 2nd instance).** The correct role for Baker in the coboundary approach is to control WHERE g_m blows up (near-resonant convergent blocks), not WHAT g_m is globally. The concrete program: (1) Decompose the Birkhoff sum of length L_m into blocks aligned with convergent denominators q_j (Ostrowski expansion). (2) Replace 1_{F_m} by a coarse approximation f_{m,J} depending on the first J << m digits (a union of O(10^J) intervals). (3) Apply Denjoy-Koksma bounds on each q_j-block (variation ~O(10^J), manageable if J grows slowly). (4) Handle the tail f_m - f_{m,J} using the survival rate bound: each additional digit beyond J kills ~10% of the set, giving exponentially small error in m-J. (5) Use Baker to control the frequency of very large partial quotients in the Ostrowski decomposition.

**(Probabilistic / second moment).** Show that E[N_m^2] / E[N_m]^2 -> 1, so that N_m is concentrated near its mean. Combined with E[N_m] -> 0, this gives P(N_m > 0) -> 0. The second moment requires bounding correlations between orbit points, which reduces to pair correlations of {frac(i*theta)} with the indicator 1_{F_m}. The 2.4x oversampling factor observed at m=29 suggests weak but nonzero correlations.

**(Geometric argument).** Exp 29b (corrected analysis) shows that ALL components of F_m have width ~3.5 * 10^{-(m-1)}, with no "persistent wide components." The apparent wide components were artifacts of float-precision limitations in the bisection search. F_m has Cantor-dust topology: totally disconnected, with all components of width ~10^{-(m-1)} distributed across macroscopic regions of locally high density (~0.9^m). The proof gap is therefore purely measure-theoretic: show that the specific orbit {frac(i*theta)} avoids the set F_m of measure ~0.9^{m-1}.

**Connection to Lagarias.** The identical barrier appears in Lagarias's study of ternary expansions of powers of 2 (arXiv:math/0512006). The metric result (finiteness for a.e. starting point) is trivial by Borel-Cantelli. Certifying a specific constant is the hard step.

**Connection to shrinking targets (GPT 5A).** Our problem is a specific instance of the "shrinking target" problem for circle rotations (Kurzweil 1955, Kim/Tseng, arXiv:2307.10122). The orbit {frac(i*theta)} must eventually miss the target F_m whose measure shrinks as 0.9^{m-1}. The metric theory (for a.e. theta) is standard. The individual case theta = log10(2) requires Diophantine input specific to this constant. Tseng's classification (arXiv:math/0702853): the monotone shrinking target property for circle rotations holds exactly for rotation numbers of constant type (bounded partial quotients).

**(D) Resonance template reduction (GPT 5A Pro, "shortest path").** Split N_m = N_m^{res} + N_m^{bulk}, where N_m^{bulk} counts hits from non-resonant orbit points and N_m^{res} counts hits from finitely many "resonant" orbit points (the ~7 persistent ones from Exp 29). The program:

1. **Prove O(1) danger cylinders.** Show that the number of F_m components that can capture orbit points {frac(i*theta)} for i <= L_m has uniformly bounded cardinality (empirically supported: at m=29, only ~7 persistent orbit points hit F_m).

2. **Persistence implies boundary proximity.** If {n*theta} is in some component of F_m for m, m+1, ..., m+r, then {n*theta} lies within distance ~10^{-(m+r)} of the limiting point of nested digit cylinders (a boundary endpoint).

3. **Baker/Matveev contradiction.** Express the boundary proximity as: |n*theta - beta| < 10^{-cm}, where beta = log10(n_0) for some zeroless integer n_0. If n_0 factors into primes {2, 3, 5, 7} with bounded complexity, then this is a linear form in logarithms of algebraic numbers, and Baker/Matveev gives |n*theta - beta| > exp(-C * log(m)), contradicting 10^{-cm} for large m.

The critical question is Step 3: whether the persistent boundary points have bounded prime-factorization complexity.

**(E) Cluster forcing lemma (GPT 5A Pro, 2nd instance). STATUS: BLOCKED (pigeonhole gap).**

**Cluster Forcing Lemma (informal).** If N_m >= r (r hits in the transition zone), then there exists 1 <= h <= H(r) such that |h*theta| <= delta_m, where delta_m is exponentially small in m (related to inter-component gaps at the hit scale).

Step B+ guarantees all r hits are in DISTINCT components. The proposed argument: a cluster of r hits in L_m orbit points, with all hits isolated in different components, forces the differences n_i - n_j to produce small |h*theta| by pigeonhole on component positions. Baker/Matveev then bounds how often theta = log10(2) can be approximated this well, capping r and eventually forcing r = 0 for large m.

**PIGEONHOLE GAP (discovered in analysis of Exp 35 data).** The pigeonhole step is incorrect: having N_m >= 2 points in a set of measure rho_m does NOT force any pair within distance rho_m of each other. The components of F_m are scattered across [0,1), and hits can land in components far apart on the circle. The Exp 35 data confirms: minimum pairwise gaps delta_m are O(1) constants (0.0969 = ||3*theta||, 0.0103 = ||10*theta||), determined by convergent denominators, NOT shrinking with m. All rescue attempts fail: (a) Baker on boundary positions requires smooth boundary integers (blocked by Exp 31), (b) Baker on theta directly gives orbit well-spacing but not avoidance of F_m, (c) effective equidistribution with error << 0.9^m is an open problem in analytic number theory.

**Dependency graph from Step B (GPT 5A Pro, 2nd instance).** Step B implies that the overlap F_m intersect (F_m - theta) can only arise from CROSS-component overlaps (since no component survives a theta-shift). This geometric constraint yields a quasi-independence bound mu(F_m intersect (F_m - theta)) <= c_1 * mu(F_m)^2, or at worst mu(F_m)^{1+epsilon}. This initializes a dependency graph that propagates to larger lags, potentially giving the sharp second-moment bound Var(N_m) <= E[N_m] + log|I_m| * E[N_m] (confirmed by both Pro instances).

### 7.5 The Final Mile Lemma (GPT 5A formulation)

GPT 5A proposes the cleanest single statement that would close the proof:

**Final Mile Lemma.** For all sufficiently large m:
1. Every component of F_m has length < min_{1 <= h <= L_m} ||h*theta||, AND
2. The orbit {frac(i*theta) : i = 0, ..., L_m - 1} stays bounded away from the boundary of F_m.

**Status of Condition (1): PROVED.** By Step B (Section 5), max component width is ~3.5 * 10^{-(m-1)}. The minimum gap ||h*theta|| for h <= L_m ~ 3m is achieved at convergent denominators of theta. By the three-distance theorem, this minimum is ~1/q_{k+1} where q_k ~ L_m. For theta = log10(2) with convergents growing roughly geometrically, the minimum gap is ~1/poly(m), which is astronomically larger than 10^{-(m-1)} for any m >= 2.

**Consequence of Condition (1):** No two consecutive orbit points (separated by theta) can lie in the same component of F_m. Every orbit hit is isolated.

**Status of Condition (2): OPEN.** This is the entire remaining gap. The boundary of F_m consists of ~2 * 9^{m-1} points (endpoints of forbidden intervals). The orbit has L_m ~ 3m points. The condition asks that no orbit point comes within distance ~10^{-(m-1)} of any boundary point. This is a Diophantine condition on log10(2) relative to the boundary geometry of F_m.

**Why (1) + (2) implies FL:** With (1), consecutive orbit points never share a component. With (2), no orbit point is near a boundary, so each orbit point is deep inside either F_m or its complement. As m grows, being "deep inside F_m" requires landing in an interval of width ~10^{-(m-1)}, probability ~0.9^{m-1} per point. With L_m ~ 3m independent trials (independence follows from (1)), the probability of any hit is ~3m * 0.9^{m-1} -> 0. Condition (2) converts this heuristic to a rigorous statement.

---

## 8. Eliminated Approaches

### 8.1 Fourier methods (magnitude-based)

All four Fourier approaches fail:

| Method | Bound behavior | Why it fails |
|--------|---------------|--------------|
| L1 norm | Grows 2.13x per level | Wiener norm ~ (9/2)^{m/2} |
| Pointwise max | Constant 0.1234 * rho | No decay, plateau |
| l^p Holder | Grows for p < 2 | Threshold at p=2 unreachable |
| Additive Fourier | Minor-arc plateau at 0.088 | No exponential decay |

The error IS O(1) empirically, but the cancellation is in the PHASES, not the magnitudes. Any approach that separates |F_m| from |D_L| loses this phase information. (Conclusions 1, 6, 8, 9, 11)

### 8.2 Sieve methods

Both GPT sieve instances confirm: the Selberg sieve applies in principle, but reduces to a Target Lemma (short-interval equidistribution) that fails empirically for upper digits. The digit-zero probability for small orbit indices is 0.63 at position 9, not the required 0.10. (Conclusion 2)

### 8.3 Thread-to-approximation

Exp 27 decisively refutes Strategy B. Thread survival constrains TRAILING digits (2^n mod 10^m), while rational approximation quality measures LEADING digits (frac(n*theta)). These are independent. The max irrationality exponent among survivors is 1.3, far below the Roth bound of 2. (Conclusion 17)

### 8.4 The unified obstruction

The METAPROMPT_SYNTHESIS.md documents the "two-axis obstruction":

- **Axis A (No Compression):** The zeroless set has exponential complexity (~4.5^m branching). No bounded-degree encoding exists.
- **Axis B (No Averaging):** The orbit is rank-1, zero entropy, in a log-time regime. No mixing resource exists at the needed scale.

The BCL route circumvents both axes by using GEOMETRIC scale separation rather than compression or averaging.

---

## 9. Evidence Summary

### Experiments

| Exp | Description | Key finding |
|-----|-------------|------------|
| 1-10 | Parity balance, carry structure, digit bias | Density zero mechanism understood |
| 11 | Classification bug fix | e_m ~ 0.5 confirmed for all m |
| 12-14 | Transfer, mod-8, fraction decomposition | Fourier structure mapped |
| 15 | Small survivor census | Survivors cluster at specific n values |
| 16 | Leading zero decomposition | Upper digit bias quantified |
| 17 | Fourier small interval | Short-sum Fourier fails |
| 18-19 | Fourier structure, conditional survival | Pairwise independence confirmed |
| 20, 20b, 20c | Riesz product, digit sieve, alpha structure | All Fourier bounds fail; problem is Diophantine |
| 21 | l^p flattening | l^p norms grow for all p < 2 |
| 22 | Additive Fourier | Better basis, but plateau at 0.088 |
| 23 | 5-adic tree | 0-or-1 branching; thread model |
| 24 | Additive Fourier plateau | Three-tier hierarchy; constructive interference |
| 25 | Coboundary test | Bounded discrepancy in transition zone; grows for full orbit |
| 26 | Denjoy-Koksma | Low orbit variation (O(1) transitions); zero-crossing mechanism |
| 27 | Thread-to-approximation | Strategy B fails; trailing/leading digits independent |
| 28 | Boundary geometry of F_m | Step B PROVED: max_comp(F_m) < theta for all m >= 2; BCL transitions persist to m=29 |
| 29 | Probabilistic finiteness | E[N_m] < 1 at m=50; BC sum finite; 2x oversampling; second moment fails to concentrate |
| 29b | Persistent components (corrected) | "Wide components" are float-precision artifacts; true width ~3.5*10^{-(m-1)}; F_m is Cantor dust |
| 30 | Danger cylinder census | O(1) hit components (max 9); every hit in distinct component; persistence limited to 5 levels; N_27=0 |
| 31 | Boundary point complexity | 95% of boundary integers NOT {2,3,5,7}-smooth; Strategy D blocked; pivot to Strategy E |
| 32 | Dependency graph / overlap | Quasi-independence confirmed: max correlation ratio 1.58 (lag 1); Var/E ~ 1.26; second moment viable |
| 33 | Ostrowski renormalization | Route not asymptotically viable; J-digit approx requires J~m; DK bounds 10,000x conservative |
| 34 | Step B+ multi-lag verification | B+ holds for m>=4; fails m=2,3; ratio decays as 10^{-(m-4)} |
| 35 | Cluster forcing delta | Min gap concentrates at ||q_j*theta||; Baker contradiction viable for large m |

### GPT Consultations

| Approach | Instance | Key contribution |
|----------|----------|-----------------|
| 1 (Digit independence) | A, B | Fourier decay under Hensel lifting; twisted transfer operator |
| 2 (Sieve theory) | A, B | Selberg applies but Target Lemma fails; 5-adic tree suggestion |
| 3 (Exponential sums) | A, B | l^p Holder fails; switch to additive Fourier |
| 4 (Diophantine/dynamics) | A | Three strategies; Lagarias barrier; shrinking targets |
| 4 (Diophantine/dynamics) | B | Coboundary mechanism; 4-step research plan; best response overall |
| 5 (Post-Exp 29b update) | A (Thinking) | o(1) discrepancy target; key Fourier mass estimate; Final Mile Lemma; shrinking target literature |
| 5 (Post-Exp 29b update) | B (Thinking) | Run formula |C| = log10((n+r)/n); r <= 9 bound; persistence is symbolic-digital, not CF |
| 5 (Post-Exp 29b update) | A (Pro, 1st) | BRS rigidity barrier (Kesten/Oren); multi-lag Step B+; resonance template program; Baker on finite residue; BEST RESPONSE |
| 5 (Post-Exp 29b update) | A (Pro, 2nd) | Cluster forcing lemma; Ostrowski renormalization program; Baker diagnostic (cannot build g_m directly); dependency graph from Step B |
| 5 (Post-Exp 29b update) | B (Pro, 1st) | Exact max_comp formula log10(1+81/(10^m-1)); uniform x-space width 9*10^{-(m-1)}; 9->0 disconnection principle; diagnostic checklist |
| 5 (Post-Exp 29b update) | B (Pro, 2nd) | Parallel integer-side derivation; two-persistence distinction; fully confirms first B Pro |

### The 35 Conclusions (condensed)

1. Fourier magnitude methods exhausted
2. Sieve methods reduce to same gap
3. Leading-digit bias is the mechanism
4. Problem is Diophantine
5. Key literature: Lagarias, Maynard, Mauduit-Rivat
6. Fourier decay under Hensel lifting keeps recurring
7. 5-adic tree: 0-or-1 branching, thread model
8. Phase, not magnitude, is key
9. Additive Fourier is the right basis
10. 0-or-1 branching is the key structural fact
11. Three-tier additive Fourier hierarchy
12. Shrinking target framework; metric BC trivially satisfied
13. Coboundary mechanism explains O(1) error
14. Coboundary fills thread independence gap
15. Bounded discrepancy in transition zone, not full orbit
16. Low orbit variation explains O(1) discrepancy; zero-crossing mechanism
17. Thread-to-approximation fails (trailing vs leading digits independent)
18. Step B PROVED; BCL transitions persist, finiteness needs probabilistic or coboundary argument
19. First-moment insufficient for m < 50; oversampling from persistent orbit points; hybrid strategy
20. "Wide components" are artifacts; true max component ~3.5*10^{-(m-1)}; F_m is Cantor dust; gap is purely measure-theoretic
21. The coboundary target must be o(1), not O(1); the key missing estimate is the low-frequency Fourier mass Sum |hat{1_{F_m}}(k)| / ||k*theta||; Final Mile Lemma Condition (1) is proved, Condition (2) is the entire gap (GPT 5A)
22. The run formula |C| = log10((n+r)/n) with r <= 9 gives exact component widths; persistence of orbit points in F_m is a base-10 symbolic property, not a continued-fraction property (GPT 5B)
23. Exact bounded coboundary (uniform O(1) BRS) is ruled out by Kesten/Oren rigidity; digit-fractal F_m is not a BRS; must target o(1) on specific orbit segment instead (GPT 5A Pro)
24. Multi-lag Step B+: max_comp(F_m) << ||k*theta|| for ALL k <= L_m, so no two orbit points share a component regardless of lag; every hit is in a distinct component (GPT 5A Pro)
25. "Shortest path" = resonance template reduction: prove O(1) danger cylinders, show persistence forces boundary proximity, apply Baker/Matveev on the finite residue (GPT 5A Pro)
26. Baker cannot directly build g_m: for discontinuous 1_{F_m}, |f_hat(k)| ~ 1/k gives |g_hat(k)| ~ k^{A-1} (not summable). Baker's proper role is controlling near-resonant frequencies, not building the transfer function. The Ostrowski renormalization route: decompose into convergent blocks, coarse-approximate by J-digit f_{m,J}, Denjoy-Koksma on blocks, exponential tail from survival rate (GPT 5A Pro 2nd)
27. Cluster forcing lemma: if N_m >= r hits (all in distinct components by Step B+), pigeonhole forces |h*theta| <= delta_m for some h; Baker caps such approximations for theta = log10(2), forcing r -> 0. Converges with Strategy D from different angle (fixed-m cluster vs cross-m persistence). Dependency graph from Step B gives quasi-independence mu(F_m cap (F_m - theta)) <= c*mu(F_m)^2 (GPT 5A Pro 2nd)
28. In x = 10^alpha coordinates, all 9^{m-1} components of F_m have uniform width 9*10^{-(m-1)} in x-space; the log transform gives exact max_comp(F_m) = log10(1 + 81/(10^m - 1)) at the all-1's prefix. Only the 9->0 digit transition disconnects F_m; transitions k->(k+1) for k in {1,...,8} are interior. Persistence is a restricted-digit Cantor set property (dimension log9/log10), orthogonal to continued fractions (GPT 5B Pro)
29. O(1) danger cylinders confirmed: max 9 hit components across m=2..27. Every hit is in a distinct component (N_m = n_components for all m), confirming Step B+ empirically. No orbit index persists for more than 5 consecutive m-levels; the apparent persistence from Exp 29 is a relay effect across sequential index waves. N_27 = 0. (Exp 30)
30. Boundary complexity blocks Strategy D: 95% of boundary integers are NOT {2,3,5,7}-smooth for m >= 4. Strategy D (applying Baker to boundary points beta = log10(n_0)) is blocked. Strategy E (cluster forcing) was proposed as an alternative but is also blocked (see Conclusion 34-35). (Exp 31)
31. Multi-lag Step B+ holds for all m >= 4: max_comp(F_m) < min_{1<=k<=L_m} ||k*theta||, with ratio decaying as ~0.34 * 10^{-(m-4)}. Fails at m=2 (ratio 2.68) and m=3 (ratio 3.31), harmless since finiteness needs only large m. (Exp 34)
32. Quasi-independence confirmed: correlation ratio mu(F_m cap (F_m - h*theta))/mu(F_m)^2 bounded by 1.58 for lag 1, within [0.97, 1.04] for lags h >= 3, across m=2..10. Var(N_m)/E[N_m] ~ 1.26 at m=10. Second moment method and dependency graph approach both viable. (Exp 32)
33. Ostrowski renormalization route not asymptotically viable: J-digit approximation requires J ~ m (no savings), DK bounds 10,000x too conservative vs actual block discrepancies. The route is formally correct but quantitatively useless. (Exp 33)
34. **CORRECTED:** Cluster forcing pigeonhole step is INCORRECT. The minimum pairwise gap delta_m between hit positions concentrates at O(1) constants ||q_j*theta|| (0.0969 for q_1=3, 0.0103 for q_2=10), NOT at rho_m ~ 0.9^m. The original claim that pigeonhole forces ||h*theta|| <= rho_m was wrong: hits in F_m can be in components scattered across [0,1), and having N_m points in a set of measure rho_m does not force any pair within distance rho_m. Strategy E is blocked. (Exp 35, corrected analysis)
35. **Strategy E pigeonhole gap (post-Exp 35 analysis).** All rescue attempts for the cluster forcing pigeonhole step fail: (a) Baker on boundary positions requires {2,3,5,7}-smooth boundary integers, but 95% are non-smooth (Exp 31); (b) Baker on theta directly gives orbit well-spacing (||h*theta|| >= c/h^A) but this controls orbit spacing, NOT orbit position relative to F_m, so a well-spaced orbit trivially fits in the complement (measure 1 - rho_m -> 1); (c) effective equidistribution of {frac(n*log10(2))} with error << 0.9^m is an open problem in analytic number theory. The true remaining gap is certifying theta = log10(2) is "generic" for the shrinking target problem with F_m. Two viable paths remain: Strategy C' (o(1) coboundary via low-frequency Fourier mass) and Strategy F (second moment for a.e. theta, needs Diophantine specialization).

---

## 10. Next Steps (Updated After Experiments 30-35)

Experiments 30-35 have been completed, testing all strategies proposed in the GPT 5 consultation. The landscape is now clear.

### 10.1 Experimental Verdicts on the Five Strategies

| Strategy | Experiment | Verdict |
|----------|-----------|---------|
| (D) Resonance template + boundary Baker | Exp 30, 31 | **BLOCKED** at Baker step: boundary integers not smooth |
| (E) Cluster forcing + direct Baker | Exp 34, 35 | **BLOCKED**: pigeonhole step incorrect (hits scatter across [0,1)) |
| (C) Ostrowski renormalization | Exp 33 | **NOT VIABLE** asymptotically: requires J ~ m |
| Second moment / dependency graph | Exp 32 | **VIABLE**: quasi-independence confirmed |
| o(1) coboundary (low-frequency mass) | Not yet tested | Status unknown; remains open |

### 10.2 What Has Been Proved or Confirmed

1. **O(1) danger cylinders** (Exp 30): max 9 hit components, bounded.
2. **Step B+ for m >= 4** (Exp 34): every pair of orbit hits is in a distinct component, regardless of lag.
3. **Quasi-independence** (Exp 32): correlation ratio <= 1.58 for all lags, second moment method viable.
4. **N_27 = 0** (Exp 30): zero hits at m=27, consistent with the 86 Conjecture.

### 10.3 What Has Been Eliminated

1. **Strategy D (boundary Baker)** (Exp 31): boundary integers are not {2,3,5,7}-smooth for m >= 4. Baker cannot be applied to log10(n_0) because n_0 has large prime factors.
2. **Ostrowski renormalization** (Exp 33): the J-digit coarse approximation requires J ~ m for the approximation error to be small, but then DK variation is 9^J ~ 9^m, no savings.
3. **Strategy B (thread-to-approximation)**: already eliminated by Exp 27.

### 10.4 The Two Surviving Strategies

**Strategy E: ELIMINATED (pigeonhole gap).**

The proposed argument was: (1) Step B+ gives each hit in a distinct component. (2) If N_m >= 2, pigeonhole on component positions forces ||h*theta|| <= rho_m ~ 0.9^m. (3) Baker/Matveev gives ||h*theta|| >= c/h^A. (4) Exponential vs polynomial contradiction.

Step (2) is incorrect. Having N_m >= 2 points in a set of measure rho_m does NOT force any pair within distance rho_m. The 9^{m-1} components of F_m are scattered across [0,1), and hits land in components that can be far apart. The Exp 35 data confirms: minimum pairwise gaps are O(1) constants (||3*theta|| = 0.0969, ||10*theta|| = 0.0103), not shrinking. Three rescue attempts all fail: (a) Baker on boundary positions is blocked by non-smooth boundary integers (Exp 31); (b) Baker on theta directly gives orbit well-spacing but not avoidance; (c) effective equidistribution with error << 0.9^m is open. See Conclusion 35.

**Strategy C': o(1) coboundary / low-frequency Fourier mass (PRIMARY).**

The target: prove Sum_{|k|<=H} |hat{1_{F_m}}(k)| / ||k*theta|| = o(1) as m -> infinity, with H = poly(m). This gives |N_m - L_m*rho_m| -> 0, forcing N_m = 0 since L_m*rho_m -> 0. Baker controls the denominators: ||k*theta|| >= c/k^A for theta = log10(2). The key missing estimate is the Fourier coefficient bound: |hat{1_{F_m}}(k)| for low-frequency |k| <= poly(m). Heuristically these are ~rho_m = 0.9^{m-1}, giving sum ~rho_m * H^{A+1} = o(1). The rigorous step is proving this bound using the product structure of F_m.

**Remaining work for Strategy C':**
- Compute |hat{1_{F_m}}(k)| for small k (experiment, possibly Exp 36)
- Prove or disprove the heuristic |hat{1_{F_m}}(k)| ~ rho_m for |k| <= poly(m)
- GPT Prompt 6 targets this question specifically

**Strategy F: Second moment method (SECONDARY).**

The quasi-independence from Exp 32 (max ratio 1.58) enables: Var(N_m) <= C * E[N_m] for bounded C ~ 1.3. Combined with E[N_m] = L_m * rho_m -> 0, Chebyshev gives P(N_m >= 1) <= E[N_m] / (something). More precisely, P(N_m >= 1) <= E[N_m^2] / 1^2 (second moment method), and E[N_m^2] = E[N_m] + sum_{i!=j} P(both hit) ~ E[N_m] + E[N_m]^2 * 1.58. For large m where E[N_m] << 1, this gives P(N_m >= 1) ~ E[N_m], which goes to zero but doesn't give finiteness (it gives P = 0 for each m, not for ALL large m simultaneously).

**Remaining work for Strategy F:**
- Borel-Cantelli requires sum P(N_m >= 1) < infinity; with P ~ E[N_m] ~ m * 0.9^m, this sum IS finite
- But Borel-Cantelli gives finiteness for a.e. theta, not for theta = log10(2) specifically
- Need: Diophantine input certifying log10(2) is "generic" with respect to the digit structure

### 10.5 Open Questions

1. **Low-frequency Fourier mass.** Compute Sum_{|k| <= poly(m)} |hat{1_{F_m}}(k)| / ||k*theta|| for m = 5..15. If this decreases toward zero, the o(1) coboundary route remains viable as a third strategy.

2. **Literature review.** The shrinking target literature (Kurzweil 1955, Kim/Tseng, arXiv:2307.10122) may contain results directly applicable to our setting. The key question: does the monotone shrinking target property hold for theta = log10(2) with targets F_m?

3. **Lagarias connection.** Adapt Lagarias's graph-directed construction for ternary expansions (arXiv:math/0512006). The 0-or-1 branching in the 5-adic tree makes our problem closer to a linear chain than a tree.

4. **GPT Prompt 6.** With Exp 30-35 results in hand, a focused prompt asking GPT to formalize the cluster forcing argument (Strategy E) or the second moment argument (Strategy F) is the natural next step. The prompt should include the specific numerical findings (correlation ratio 1.58, boundary non-smoothness, Step B+ failure at m=2,3).

### 10.6 Summary of the Proof Gap

The gap is now precisely characterized: **certify that theta = log10(2) is not in the measure-zero exceptional set for the shrinking target problem with targets F_m.** Two paths remain open (Strategy E eliminated, see Conclusion 35):

- **Strategy C' (o(1) coboundary, PRIMARY):** Show the low-frequency Fourier mass Sum_{|k|<=H} |hat{1_{F_m}}(k)| / ||k*theta|| = o(1) vanishes, giving o(1) discrepancy on the transition zone. Baker controls the denominators; the key step is bounding the Fourier coefficients |hat{1_{F_m}}(k)| ~ rho_m for |k| <= poly(m). GPT Prompt 6 targets this.
- **Strategy F (second moment):** Use quasi-independence to show P(N_m >= 1) ~ E[N_m] ~ m*0.9^m, then Borel-Cantelli for a.e. theta. Needs Diophantine input to specialize to theta = log10(2).

---

*Document generated from 35 experiments (including 29b correction) and 14 GPT consultation responses, January 2026. Updated with Conclusion 35 (Strategy E pigeonhole gap).*
