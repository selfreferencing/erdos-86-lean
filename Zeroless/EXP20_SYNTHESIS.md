# Experiment 20/20b/20c Synthesis: Riesz Product Structure and the Path to Finiteness

## Executive Summary

Three experiments (20, 20b, 20c) investigated the Riesz product structure of the survivor indicator and discovered that **the finiteness gap is not a Fourier analysis problem at all**. The critical finding is:

1. All Fourier-based approaches fail (L1 bound, pointwise bound, Erdos-Turan, discrepancy).
2. The actual mechanism ensuring finiteness is deterministic: for each candidate n with D(n) = m, the value alpha = frac(n * log10(2)) determines a specific leading-digit pattern, and for m >= 27, every such alpha produces at least one zero digit.

The problem reduces to a Diophantine question about the sequence {n * log10(2)} and its interaction with the digit structure of 10^alpha.

---

## Part I: What the Fourier Analysis Reveals

### The max non-DC Fourier coefficient stabilizes
**max|hat(f_m)(r)| / rho_m = 0.12341 for all m >= 4.**

This ratio is constant. The dominant coefficient always occurs at frequency j = 5^{m-2} (5-adic valuation m-2), with j/T = 0.05. The top 10 coefficients all have v_5 = m-2.

### Perfect lacunary structure confirmed
Each digit indicator g_j has Fourier support exactly on multiples of stride_j = 5^{m-1-j}. Off-stride coefficients are zero to machine precision. The supports are nested (not multiplicatively lacunary).

### All Fourier bounds fail

| Method | Bound | Trend | Verdict |
|--------|-------|-------|---------|
| L1 norm | sum |F(j)| * |D_L(j)| | Grows 2.13x/level | FAILS |
| Pointwise | max|F|/rho = 0.1234 | Constant, not decaying | FAILS |
| Erdos-Turan | D_m * Z_m | Grows | FAILS |
| Discrepancy | D_m * C*m | Goes to 0 | WRONG QUANTITY |

The Fourier error bound is ~258x larger than the actual error at m=9, and the gap grows exponentially. The signed error is O(1) but the bound is O(2^m). Phase cancellation is massive but uncontrolled.

### Why Fourier fails: fundamental obstacle
The Fourier approach bounds |S_m cap [0,L)| by decomposing f_m into frequency components. But the frequencies that matter (v_5 = m-2) have the same number of terms as the full orbit, so no dimension reduction is possible. The problem is that f_m is a product of m conditions, and while the product creates massive cancellation in the global Fourier coefficients (compression ratio 10^{-7} at m=8), this cancellation doesn't translate into a usable pointwise bound.

---

## Part II: What Actually Kills Small Orbit Indices

### The bias is real and grows with digit position
For small orbit indices (i < C*m), the probability that digit j is zero is dramatically higher than 1/10 for upper digits:

At m=9, L=30:
| Digit | P(0|small) | P(0|large) | Bias |
|-------|-----------|-----------|------|
| 1 | 0.000 | 0.000 | 0.00 |
| 2 | 0.067 | 0.100 | -0.03 |
| 3 | 0.133 | 0.100 | +0.03 |
| 6 | 0.333 | 0.100 | +0.23 |
| 9 | 0.633 | 0.100 | +0.53 |

The bias grows roughly linearly with digit position. This is the leading-zero mechanism from Exp16, now quantified at the digit level.

### The kill pattern is top-heavy
When sieving small indices digit by digit (Part C, Exp20b), the upper digits kill disproportionately. At m=9, digit 6 kills 26% of survivors (vs expected 10%), digit 9 kills 25%. Lower digits kill at or below the expected 10%.

### The error evolves non-monotonically during sieving
The error |S_k cap [0,L)| - L*rho_k starts at 0 (after digit 1, which never kills), becomes positive after digit 2, then becomes increasingly negative as upper digits impose their bias. The error/main ratio reaches -0.30 at step m, meaning the actual count is 30% below the main term.

---

## Part III: The Deterministic Structure

### Alpha determines everything
For n with D(n) = m, the value alpha = frac(n * log10(2)) determines the full leading-digit structure of 2^n. The orbit element is 2^n = 10^{m-1} * 10^alpha, so:
- Leading digit = floor(10^alpha) (in {1,...,9})
- Second digit = floor(10^{alpha+1}) mod 10
- k-th digit from top = floor(10^{alpha+k-1}) mod 10

### The alpha sequence has period structure
The candidates n for each m have alpha values spaced by log10(2) ~ 0.30103:
- alpha(n+1) = alpha(n) + log10(2) (mod 1)

So for 3-4 candidates at each level, the alphas are {alpha_0, alpha_0 + 0.301, alpha_0 + 0.602, alpha_0 + 0.903 mod 1}.

### Zeroless requires ALL digits of 10^alpha to be nonzero
2^n is zeroless iff the m-digit decimal expansion of 10^{m-1+alpha} has no zero digit. Since the leading digit (floor(10^alpha)) is always 1-9, this is automatic for position m. The constraint is on the remaining m-1 digits.

For 10^alpha with alpha in [0,1), the k-th digit from the top is floor(10^{alpha+k-1}) mod 10. This digit is zero iff frac(10^{alpha+k-1}) lies in a specific interval of length 1/10 (approximately).

### The zero-digit set for 2^n
For fixed m, define the "zero set" for digit k:
Z_k = {alpha in [0,1) : floor(10^{alpha+k-1}) mod 10 = 0}

The zero-free set (all digits nonzero) is:
F = [0,1) \ (Z_1 union Z_2 union ... union Z_{m-1})

2^n is zeroless iff alpha(n) = frac(n * log10(2)) is in F.

For small m, F is large enough that alpha(n) can land in it. For large m, F shrinks (each Z_k removes ~1/10 of the remaining measure), and F is approximately (9/10)^{m-1} in measure. Since the alpha values are spaced by log10(2) ~ 0.301, having 3-4 candidates means the probability of ALL missing F is (1 - (9/10)^m)^3 ~ 1 - 3*(9/10)^m -> 1.

### Evidence: no zeroless powers exist after n=86
From Exp20c Part B, the "any_zeroless" column shows YES up to m=26 (n=86), then NO for all m = 27 through 60 (and beyond, computationally verified to much larger n).

---

## Part IV: The Path to a Proof

### Approach A: Measure-theoretic (heuristic argument, not rigorous)
The set F of zero-free alphas has measure ~(9/10)^m. The 3-4 candidate alphas are quasi-random (equidistributed by Weyl). The probability of hitting F is ~3 * (9/10)^m -> 0. This is the Borel-Cantelli heuristic that GPT and the literature (Dumitru) invoke.

**Gap:** Proving the equidistribution of {n * log10(2)} within F requires showing that F does not correlate with the orbit structure. This is exactly the horizontal equidistribution problem.

### Approach B: Direct Diophantine (most promising for a proof)
The zero-free set F can be described explicitly as a union of intervals in [0,1). For the k-th digit to be nonzero, we need:
frac(10^{alpha+k-1}) not in [0, 0.1) union [1.0, 1.1) union ... [9.0, 9.1)
Wait, the digit is floor(10^{alpha+k-1}) mod 10 = 0 iff frac(10^{alpha+k-1} / 10) * 10 is in [0,1), which is...

Actually, the digit is simpler: the k-th digit from the left of 10^alpha is floor(10^alpha * 10^{k-1}) mod 10. This equals 0 iff frac(10^{alpha+k-1}) is in one of the intervals [j/10, (j+1)/10) where the digit equals 0, which happens when frac(10^{k-1+alpha}) is in [0, 0.1).

No wait. 10^alpha is a real number in [1, 10). Its k-th digit from the left is floor(10^{k-1} * 10^alpha) mod 10 = floor(10^{k-1+alpha}) mod 10. This is 0 iff frac((k-1+alpha) * log10(10)) has... no, this is circular.

Let me think more carefully. 2^n = 10^{n*log10(2)} = 10^{(m-1) + alpha} where alpha = frac(n * log10(2)). So x = 10^{m-1+alpha}. The digits of x in base 10 are determined by alpha alone (the m-1 factor just shifts the decimal point).

The k-th digit from the LEFT of x is: floor(x / 10^{m-k}) mod 10 = floor(10^alpha * 10^{k-1}) mod 10.

This digit is 0 iff floor(10^{alpha + k - 1}) mod 10 = 0, which means 10^{alpha+k-1} mod 10 is in [0, 1). Since 10^{alpha+k-1} = 10^{k-1} * 10^alpha, and 10^alpha in [1,10), we have 10^{alpha+k-1} in [10^{k-1}, 10^k).

In this range, floor(t) mod 10 = 0 iff t is in [10*j, 10*j+1) for some integer j. The fraction of [10^{k-1}, 10^k) covered by such intervals is 10^{k-1} * (1/10) / (10^k - 10^{k-1}) = (10^{k-2}) / (9 * 10^{k-1}) = 1/90.

Hmm, that gives P(digit k = 0) = 1/9 in Benford measure for k >= 2 (the Benford second-digit formula). Actually the well-known result is:

P(d-th digit from left = 0) = sum_{j=10^{d-1}}^{10^d - 1} log10(1 + 1/(10j)) for d >= 2.

For d=2: sum_{j=10}^{99} log10(1 + 1/(10j)) ~ 0.1197 (not 1/10).

The point is: for Benford-distributed numbers, the probability of ANY specific digit being 0 is slightly above 0.1 for d >= 2. But the digits are NOT independent (they're correlated through the common alpha).

### Approach C: Computational verification + the finite check
**The pragmatic path:** Since no zeroless 2^n exists for n > 86 up to n ~ 10^8 or beyond (computationally verified), and the heuristic probability of finding one decreases exponentially, the conjecture is "morally certain." A rigorous proof would require either:

1. An explicit computation showing that for all alpha in the orbit {frac(n * log10(2)) : n >= 87}, the m-digit expansion of 10^{(m-1)+alpha} has at least one zero, OR
2. A measure-theoretic argument showing the zero-free set F is too small and too "spread out" (high discrepancy) to be hit by the quasi-random sequence {n * log10(2)}.

### What a GPT prompt for the final step should contain
Given that all Fourier/sieve/exponential-sum approaches have failed computationally, the next GPT prompt should focus on:

1. **Diophantine approximation to log10(2)**: The quality of rational approximations p/q to log10(2) controls how close frac(n * log10(2)) can get to specific target values. If log10(2) has bounded partial quotients in its continued fraction, there are limits on how well the orbit can avoid the zero-digit regions.

2. **The geometry of the zero-free set F**: F is a fractal-like subset of [0,1) defined by the intersection of m conditions on 10^{alpha+k}. Its Hausdorff dimension and measure are well-studied (related to Cantor-like constructions). The key question: is F too small and too fragmented to be hit by any arithmetic progression of spacing log10(2)?

3. **Schmidt's Subspace Theorem / p-adic methods**: These tools constrain how well algebraic numbers can approximate specific patterns in digit expansions. Since log10(2) is transcendental, the Thue-Siegel-Roth theorem gives |log10(2) - p/q| >> q^{-2-epsilon}, which limits how long the orbit can stay near a zero-free region.

---

## Part V: Convergence with GPT's Sieve Analysis (Approach 2A and 2B)

Two independent GPT sieve theory responses reach the SAME conclusion from the opposite direction. Both show:

1. The Selberg sieve applies to our digit-position sieve in principle
2. The entire sieve approach reduces to a **Target Lemma**: proving power-saving discrepancy for digit-zero sets in [0, L)
3. The Target Lemma asks: |#{n < L : n in K_j} - (1/10)L| << L^{1-delta}

**Our Exp 20b Part D shows this Target Lemma is FALSE for upper digits.** P(digit 9 = 0 | i < 30) = 0.63, not the required ~0.10. The bias is massive and goes in the direction that HELPS finiteness (more zeros = fewer survivors), but standard sieves require the estimate both ways.

### Response 2B: Structural refinements

GPT Instance B adds three insights beyond the basic sieve diagnosis:

**Chain simplification.** Because T_j | T_{j+1}, we have lcm(T_j : j in J) = T_{max J} for any subset J. All intersection patterns live on only m scales, not the exponentially many moduli that arise in multiplicative sieves. This means the Selberg quadratic form reduces to a sum over m levels.

**Explicit error anatomy.** The chain-adapted Selberg bound takes the form:
|S_m intersect [0,L)| <= L * 0.9^{m-1} + sum_{j=2}^{m} 0.9^{m-j} * Delta_j([0,L))
where Delta_j is the discrepancy of the initial interval mod T_j. The weight 0.9^{m-j} means late levels (large j) dominate the error, confirming our Exp 20b observation that upper digits control the sieve.

**5-adic tree/automaton alternative.** The T_{j+1} = 5*T_j chain defines a 5-ary refinement tree of admissible residues. If the survival rate along the "small index" branch drops below 1/5 at a positive fraction of levels, the minimal survivor index grows exponentially, exceeding Cm. This bypasses both sieve remainder terms and Fourier analysis, working directly with the 5-adic tree structure. It connects naturally to the alpha-based formulation from Exp 20c.

This convergence from two independent directions (computation and abstract sieve theory) confirms the diagnosis: **the finiteness gap is fundamentally about horizontal equidistribution at logarithmic scale**, and it cannot be resolved by any known off-the-shelf method. The problem requires either:

- A Diophantine argument about the orbit {frac(n * log10(2))} avoiding a shrinking set, OR
- A "Fourier decay under Hensel lifting" lemma (suggested by both GPT instances for Approach 1 and confirmed by both GPT Approach 2 instances) that would simultaneously give short-interval discrepancy and high-order pseudo-independence, OR
- A 5-adic tree/automaton argument showing survival rate < 1/5 along the small-index branch (suggested by GPT 2B)

---

## Part VI: GPT Approach 3 (Exponential Sums) and the l^p Flattening Test

GPT Approach 3A proposed a Holder inequality strategy: replace the failing l^1 bound with an l^p bound (p > 1) on hat(b_m), paired with l^q (q = p/(p-1) > 2) on the Dirichlet kernel. The key prediction was the "Bottleneck Lemma": ||hat(b_m)||_p << 5^{-kappa*m} for some kappa > 1/q.

**Experiment 21 refutes this prediction.** The l^p norms GROW for all p in (1,2):

| p   | kappa (fitted) | Growth/level | Verdict |
|-----|----------------|-------------|---------|
| 1.0 | -0.490         | 2.13x       | GROWS   |
| 1.1 | -0.401         | 1.84x       | GROWS   |
| 1.2 | -0.327         | 1.62x       | GROWS   |
| 1.5 | -0.170         | 1.29x       | GROWS   |
| 2.0 | -0.030         | 1.05x       | ~FLAT   |

The l^2 norm stabilizes near 0.49 (consistent with Parseval: ||b_m||_2^2/T = rho(1-rho)). But the threshold at p=2 requires kappa > 0.5, far from the observed ~0.

The Holder bounds are actually WORSE than the l^1 bound (10-20x larger at m=10) because the l^q norm of the Dirichlet kernel (q > 2) grows faster than the l^p advantage on hat(b_m).

### Diagnosis: the cancellation is in the phases

The error IS O(1) empirically, but no product-of-norms inequality can capture this. The cancellation comes from the PHASES of F_m(j) * D_L(j), not from the magnitudes of either factor. Any approach that separates |F_m| from |D_L| loses this phase information.

This eliminates the l^p/Holder strategy and all other norm-based approaches in the multiplicative Fourier basis.

### GPT 3B: Switch to additive Fourier (Exp 22)

GPT Response 3B identified a fundamental issue: our multiplicative DFT (on the orbit group Z/T_m Z) is the WRONG Fourier basis for this problem. The digit condition is additive-digital, visible in additive characters e(au/5^m). Switching to additive Fourier on Z/5^m Z:

- Makes f_m a standard "digital function" in the Mauduit-Rivat sense
- Decomposes N_m(L) = sum_a hat(f)(a) * S_L(a) where S_L(a) is an exponential sum along powers
- Matches the Maynard template: (digit Fourier) x (sequence sum)
- Produces a SMALLER l^1 norm (58.2 vs 159.2 at m=8, ratio 0.37)

**Exp 22 tests the additive minor-arc decay prediction.** The max|hat(f)(a)|/rho by depth k = m - v_5(a):

| k | max ratio |
|---|-----------|
| 1 | 0.2154 |
| 2 | 0.0959 |
| 3-9 | ~0.0877 (plateau) |

There is a meaningful drop from k=1 to k=2 (factor 2.25x) but then the coefficients PLATEAU at ~0.088*rho. This is NOT the exponential decay GPT predicted (R^2 = 0.36 for the exponential fit, driven entirely by k=1,2).

The additive framework is genuinely better than the multiplicative one, but the minor-arc coefficients hit a floor rather than decaying. A proof in this framework would need to exploit major-arc structure (where S_L(a) is controllable via periodicity) rather than relying on minor-arc Fourier decay.

---

## Part VII: The 5-adic Tree (Exp 23)

Experiment 23 tested GPT 2B's 5-adic tree/automaton suggestion and found a remarkably clean structure.

### The tree is not a tree past level 3

From level 4 onward, every admissible node has either 0 or 1 admissible children. Never 2 or more. The 5-adic "tree" is actually a collection of single threads that terminate stochastically, with death probability ~0.1 per level (matching generic behavior).

### The finiteness mechanism is combinatorial

Start with L ~ 3.3m threads at level 3. Each thread dies independently with prob ~0.1 per level. After m-3 levels, expected survivors ~ L * 0.9^{m-3} ~ 3.3m * 0.9^m -> 0.

At m=25, 13/25 levels have survival rate < 1/5 (GPT 2B's criterion). At m=30, 18/30 do.

### Small-index branching equals generic branching

Part E shows NO difference between small-index and generic branching rates (both ~0.9). The leading-digit bias does NOT manifest as reduced branching. This means the mechanism is purely the counting argument: L threads, m levels, each with ~10% death rate.

### The rigorous gap

Making this rigorous requires proving the thread deaths are sufficiently independent. Two threads at the same level correspond to orbit indices differing by < L, so their digit patterns are correlated through the orbit structure. The deaths are NOT fully independent, but the correlation decays with distance in the orbit, and our pairwise independence results (Exp 19) suggest the correlation is weak enough.

### Minimal survivor index

The minimal survivor hovers at 0.6-0.9 * L for m <= 26, then crosses above L at m=27 (matching the known last zeroless power 2^86 at m=26). It dips back below at m=30-34. The oscillation is expected: the minimal survivor is a random variable with mean ~L*(1-0.9^m) and fluctuations of order sqrt(L).

---

## Part VIII: Additive Fourier Plateau Investigation (Exp 24)

Exp 24 investigated why the additive Fourier max coefficients plateau at ~0.0877 for deep minor arcs.

### Three-tier hierarchy

The spectrum is not a simple plateau. It has three tiers:
- k=1 (shallowest minor arc): ratio = 0.2154 (stabilized, same as multiplicative max 0.1234 rescaled)
- k=2: ratio = 0.0959
- k=3: ratio = 0.0894, k=4: 0.0888, k>=5: converging to ~0.0877

Each tier represents a different 5-adic structural regime. The first nonzero 5-adic digit of the frequency a determines the tier; subsequent digits produce diminishing corrections.

### d <-> 5-d symmetry

Frequencies whose leading nonzero 5-adic digit is d give the SAME max ratio as those with digit 5-d. This follows from hat(f)(-a) = overline(hat(f)(a)) for real-valued f. Digits 1 and 4 always achieve higher maxima than digits 2 and 3.

### Constructive interference in the Riesz product

Individual digit indicators g_r each have max|hat(g_r)|/rho_r ~ 0.2 = 1/5. If the argmax frequencies were unrelated, the product would decay as 0.2^m. Instead, the actual max|hat(f_m)|/rho = 0.2154, constant. The ratio (actual/product) grows as 5^m, meaning the dominant Fourier modes of different g_r are ALIGNED, creating coherent addition.

### Transfer matrix amplification

The transfer ratios |phi_r(d*5^{r-1}+a')|/|phi_{r-1}(a')| have max values >> 1 (up to 35.8 at d=4, r=5). This means specific frequency-digit combinations AMPLIFY the Fourier coefficient at each step. The mean ratio is < 1 (contractive on average), but the specific argmax frequency rides the amplifying direction at each step, maintaining the plateau indefinitely.

### The plateau constant is NOT a simple fraction

4/45 = 0.0889 is close but 1.4% too high. No tested closed-form expression matches 0.0877. The constant may be transcendental, determined by the specific interaction between the maps u -> 2^{m-r}*u mod 5^r and the digit-zero intervals.

---

## Conclusions

1. **Fourier magnitude methods are exhausted in the multiplicative basis.** Four approaches (pointwise decay, L1 bounds, discrepancy, l^p Holder) all fail. Switching to additive Fourier (Exp 22) produces a cleaner spectrum with lower l^1 norm, but the minor-arc coefficients plateau at ~0.088*rho rather than decaying exponentially. No norm-based bound works in either basis.

2. **Sieve methods reduce to the same gap.** GPT's sieve analysis confirms that the Selberg sieve applies but its Target Lemma (short-interval equidistribution) fails empirically for upper digits.

3. **The leading-digit bias is the mechanism.** Small orbit indices have a deterministic bias toward zero in their upper digits, caused by the orbit element being literally too small to fill all digit positions uniformly.

4. **The problem is now Diophantine.** Proving finiteness requires showing that the sequence {frac(n * log10(2))} cannot indefinitely avoid the shrinking zero-free set F. This is a question about the Diophantine properties of log10(2) and the geometry of restricted-digit sets.

5. **The most promising literature**: Lagarias "Ternary Expansions of Powers of 2", Maynard "Primes with Restricted Digits", Mauduit-Rivat, and Schmidt's subspace theorem applications to digit problems.

6. **One technical ingredient keeps recurring**: "Fourier decay under Hensel lifting" (or equivalently, the twisted transfer operator for the digit-zero indicator as 5-adic level increases). This appears in GPT Approach 1 (both instances), GPT Approach 2 (both instances), and our Exp 20 transfer analysis (Part C). If proven, it simultaneously resolves the Fourier decay, sieve distribution, and digit independence questions.

7. **The 5-adic tree reveals the mechanism.** Exp 23 shows the 5-adic "tree" is actually single threads (0-or-1 branching past level 3), each dying with prob ~0.1 per level. Finiteness reduces to: L ~ 3.3m threads, m levels, ~10% death rate => expected survivors ~ m * 0.9^m -> 0. The rigorous gap: proving thread deaths are sufficiently independent (correlation through orbit structure).

8. **Phase, not magnitude, is the key.** Exp 21 shows that the error cancellation in sum F_m(j) * D_L(j) cannot be captured by ANY product-of-norms inequality. The cancellation is in the phases, which arise from the digit factorization structure. A proof must exploit phase coherence directly, not bound magnitudes.

9. **Additive Fourier is the right basis.** GPT 3B correctly identified that the digit condition is additive-digital, best analyzed via additive characters on Z/5^m Z. The additive l^1 norm is 37% of the multiplicative l^1 at m=8 and the spectrum has cleaner 5-adic structure. The additive major/minor arc framework (Maynard template) is the natural setting, even though the specific minor-arc decay prediction fails.

10. **The 0-or-1 branching is the key structural fact.** Past level 3, each admissible 5-adic node has at most 1 admissible child. This means the problem reduces from a tree-survival question to a thread-survival question: L independent threads, each dying with prob ~0.1 per level. This is a much simpler probabilistic model than the full tree, and the independence structure may be provable via the primitive-root / CRT arguments already in hand.

11. **The additive Fourier spectrum has three-tier hierarchical structure (Exp 24).** The plateau at ~0.0877 is actually the bottom of a three-tier hierarchy: k=1 gives max ratio 0.2154, k=2 gives 0.0959, k=3 gives 0.0894, and k>=5 converges to ~0.0877. There is a d <-> 5-d symmetry (digits 1,4 equivalent; digits 2,3 equivalent). The Riesz product structure creates CONSTRUCTIVE interference at dominant frequencies: individual factors contribute max ratio ~0.2 = 1/5, but their product stabilizes at 0.2154 rather than decaying as 0.2^m. Transfer matrix max ratios exceed 1 (up to 35.8), meaning specific frequency directions are AMPLIFIED at each digit level. This explains why magnitude-based bounds cannot decay to zero.

12. **The problem is a shrinking target problem, and the metric case is trivially solved (GPT 4A).** The first Borel-Cantelli lemma immediately gives: for a.e. starting point, the irrational rotation orbit hits only finitely many F_m (since sum |F_m| = sum 0.9^m < infinity). The entire difficulty is certifying that alpha = log10(2) is not exceptional. This is precisely the barrier Lagarias identified for ternary expansions of powers of 2 (arXiv:math/0512006). Three concrete bridge strategies:
    - **(B) Thread-to-approximation**: survival to depth m in the 5-adic tree forces an exponentially good rational approximation to log10(2), which contradicts known irrationality measure bounds. The 0-or-1 branching makes this plausible.
    - **(C) Bounded remainder / coboundary**: the empirical O(1) error is the signature of bounded remainder sets. If the digit indicator can be decomposed as a coboundary for the rotation, telescoping gives bounded discrepancy, and rho_m * L -> 0 forces zero hits.
    - **(A) Exceptional parameter set**: prove the set of lambda with infinitely many zeroless lambda*2^n has Hausdorff dimension < 1, then exclude lambda = 1.

13. **The coboundary mechanism is the correct explanation for O(1) error (GPT 4B).** The O(1) error we observe is the signature of 1_{F_m} being approximately a coboundary g_m - g_m*T for the rotation T = R_theta. Telescoping gives |sum_{j<L} f(T^j x) - L*mu(F_m)| <= 2*|g_m|_inf + L*|epsilon_m|. Once L*mu(F_m) < 1/2 (which happens since m*0.9^m -> 0), zero hits are forced. The required Diophantine input is NOT global bounded type, but a restricted small-divisor bound: |k*theta| >= k^{-A} for k in the structured frequency set K_m arising from the digit filtration. Baker-type linear forms in logarithms provide exactly this kind of restricted irrationality measure for theta = log10(2). This is the most promising path to a complete proof.

14. **The coboundary strategy also fills the thread independence gap.** The 5-adic tree's 0-or-1 branching creates a martingale difference / filtration structure. Bounded discrepancy from the coboundary decomposition proves the necessary "transversality" of digit-level sigma-algebras to the rotation, effectively establishing thread death independence without requiring statistical independence. This connects Exp 23 (thread model) to Exp 20/21 (O(1) error) through a single mechanism.

15. **CRITICAL REFINEMENT (Exp 25): Bounded discrepancy holds in the transition zone but NOT for the full orbit.** The max discrepancy over the full orbit grows to ~100-130 (driven by the convergent denominator q_8 = 28738 of log10(2)). But the transition zone discrepancy (L <= C*m) remains bounded in [-11, 0] for all m = 2..27. The finiteness argument only needs the transition zone bound. The mechanism: the transition zone is too short to encounter convergent-denominator resonances. For m <= 27, L_trans < q_3 = 93, so the orbit hasn't completed enough of a near-period to build up large discrepancy. This weakens the required lemma: we need RESTRICTED bounded discrepancy (for L <= C*m), not uniform bounded discrepancy. This is more realistic and connects to standard Denjoy-Koksma estimates for short Birkhoff sums.

16. **WHY the transition zone discrepancy is O(1): low orbit variation (Exp 26).** The standard Denjoy-Koksma bound uses circle variation V(f_m) ~ 9^m, giving a useless bound. Exp 26 identifies the true mechanism: the function f_m has only O(1) transitions (0-to-1 or 1-to-0 changes) along the orbit ordering in the transition zone. At m=27, there are ZERO transitions in 90 steps (the entire zone is non-survivors). This happens because F_m has ~9^m boundary points spaced ~10^{-m} apart, while the L ~ 3m orbit points are spaced ~1/3 apart, so the expected boundary crossings are ~ 3m * 9^m * 10^{-m} = 3m * 0.9^m -> 0. Three converging explanations: (a) low orbit variation bounds the Birkhoff sum directly; (b) per-digit cancellation between lower digits (positive disc) and upper digits (negative disc) keeps the total O(1); (c) the transition zone is shorter than the first dangerous convergent q_3 = 93. The proof target is now sharper: for large m, the orbit in the transition zone crosses zero boundaries of F_m, so either ALL L points are survivors (impossible since no component of F_m spans a length-0.3 arc) or NONE are (giving N_m = 0 = finiteness). Making this rigorous requires showing log10(2) avoids the measure-zero set of alpha-values where boundary crossings occur.

17. **Strategy B (thread-to-approximation) FAILS: survival does not force good rational approximation (Exp 27).** Survivors have approximation quality |n*theta - p| that is statistically indistinguishable from generic n values (ratio ~ 0.9-1.1 across all m). The max irrationality exponent among survivors is mu ~ 1.3, far below the Roth bound of 2. The core issue is a category error: thread survival constrains TRAILING digits of 2^n (a 10-adic condition on 2^n mod 10^m), while rational approximation quality measures LEADING digits (frac(n*theta) = frac(log10(2^n))). These are essentially independent. Knowing all trailing digits tells you nothing about how close n*log10(2) is to an integer. The remaining viable strategies are: (C) coboundary/bounded remainder (supported by Exp 25-26); and Exp 26's zero-boundary-crossing geometric argument. A modified Strategy B might work at the collective level: asking whether the EXISTENCE of any survivor in [m, m+L) forces a constraint, rather than whether individual survivors force good approximation.

18. **Step B of the BCL is PROVED: no component of F_m spans two consecutive orbit points (Exp 28).** The proof is elementary: F_m is a subset of F_2 for all m >= 2, and the largest connected component of F_2 has width log10(20/11) = 0.2596 < theta = log10(2) = 0.3010. Therefore max_component(F_m) < theta for all m >= 2, with 14% margin. The bound tightens to ratio 0.112 at m=3 and 0.012 at m=4. Moreover, the true widest component width is ~0.9 * T_m ~ 3.5 * 10^{-(m-1)} (see Conclusion 20), so for m >= 2 the bound is astronomically stronger than needed. However, the full BCL (zero transitions in the transition zone) does NOT hold up to m=29: the orbit still has ~10-15 transitions between inside/outside F_m at m=29, with 10/97 orbit points landing in F_m. The finiteness proof needs a probabilistic or measure-theoretic argument showing that the expected number of hits (L * mu(F_m) ~ m * 0.9^m -> 0) eventually forces zero actual hits.

19. **First-moment probabilistic arguments are quantitatively insufficient for m < 50 (Exp 29).** E[N_m] = L_m * mu(F_m) = ceil(m/theta) * 0.9^{m-1} first drops below 1 at m=50. The Borel-Cantelli sum is finite (332.7), confirming N_m = 0 a.e. eventually. But the actual N_m for theta = log10(2) shows two phases: undersampling (ratio ~0.7x) for m < 20, then oversampling (~2x) for m=20-30. The oversampling comes from ~7 persistent orbit points (alpha ~ 0.567, 0.353, 0.868, 0.674, 0.588, 0.878, 0.511) that land in high-density regions of F_m for 13-19 consecutive m values. The second moment does NOT concentrate (N_m^2/E^2 up to 6.4 at m=24), so variance-based methods fail. A hybrid strategy may work: coboundary/bounded discrepancy for m < 80, then Markov's inequality (E[N_m] < 0.72 with 2x factor) for m >= 80.

20. **The "persistent wide components" of F_m do not exist: F_m is Cantor dust for large m (Exp 29b).** The bisection-based component search in Exp 28 had two bugs: (a) exponential doubling skipped over narrow gaps, finding distant boundaries instead of nearest ones; (b) for m > ~15, true component widths (~10^{-(m-1)}) are below float precision (~10^{-16}), making micro-gaps invisible. The TRUE widest component of F_m has width ~0.9 * T_m, where T_m = 10/(10^{alpha_opt} * 10^{m-1} * ln(10)) ~ 3.5 * 10^{-(m-1)}. This was verified analytically for m=2..8: the width/T_m ratio is 0.900 for m >= 4, with the optimal alpha ~ 0.049 (where all digits are near 1). For m=29, the true widest component has width ~3.5e-28, NOT 1.77e-6. What appeared as a "wide component" is a dense cloud of ~10^22 micro-components with Cantor-dust topology (totally disconnected). This has major proof implications: Step B is trivially satisfied (every component is ~10^{-(m-1)} << theta), consecutive orbit points NEVER share a component for any m >= 2, and the entire proof gap reduces to a purely measure-theoretic question about {frac(i*theta)} hitting a set of measure ~0.9^{m-1}.

21. **The coboundary target must be o(1) discrepancy, not O(1); the Final Mile Lemma identifies the exact gap (GPT 5A).** GPT 5A (Thinking) correctly identifies that the coboundary approach requires |N_m - L_m*rho_m| -> 0 (not just boundedness), since L_m*rho_m -> 0 and we need N_m = 0 eventually. The key missing estimate is the low-frequency Fourier mass: Sum_{|k|<=H} |hat{1_{F_m}}(k)| / ||k*theta|| = o(1) with H = poly(m). Baker's theorem controls the denominators; the question is bounding the numerators for the specific structured frequency set K_m. The "Final Mile Lemma" gives the cleanest formulation: (1) every component of F_m has length < min_{h<=L_m} ||h*theta|| [PROVED by Step B + Cantor dust], AND (2) the orbit stays bounded away from boundary(F_m) [OPEN: the entire remaining gap]. The problem is a specific instance of the "shrinking target" problem for circle rotations (Kurzweil 1955, Kim/Tseng, arXiv:2307.10122). The metric case (a.e. theta) is trivial; certifying theta = log10(2) is the open Diophantine question.

22. **The run formula gives exact component widths; persistence is a symbolic-digital property (GPT 5B).** Each connected component of F_m corresponds to a maximal run of consecutive zeroless m-digit integers n, n+1, ..., n+r-1, with exact width |C| = log10((n+r)/n). Since among any 10 consecutive integers one ends in 0, the run length r <= 9, giving the clean uniform bound max_comp(F_m) <= 9/(10^{m-1} * ln(10)) = O(10^{-(m-1)}). This is an alternative (and more elementary) proof of the exponential component width decay established in Exp 29b. The "persistence" of orbit points in F_m across many m values is a base-10 symbolic property (whether the digits of 10^alpha avoid 0 for many positions), not a continued-fraction property of alpha. This confirms that the CF of theta enters only indirectly through discrepancy/equidistribution control, not through direct characterization of persistent components.

23. **Exact bounded coboundary is ruled out by BRS rigidity (GPT 5A Pro).** An exact bounded coboundary for 1_{F_m} (||g_m||_inf = O(1) uniformly in orbit length N) is equivalent to F_m being a bounded remainder set (BRS) for rotation by theta. By Kesten's theorem (1966), a single interval is a BRS iff its length is in Z + theta*Z. By Oren's generalization (arXiv:1404.0455), finite unions of intervals satisfy a rigid pairing/permutation condition on endpoint lengths. Digit-fractal sets almost certainly do not satisfy these arithmetically rigid conditions. This rules out exact coboundary as a proof strategy. The viable version is GPT 5A's o(1) refinement: target discrepancy -> 0 on the specific orbit segment of length L_m, which is weaker than the BRS condition and may still be achievable.

24. **Multi-lag Step B+ strengthens the isolation of orbit hits (GPT 5A Pro).** Since max_component(F_m) ~ 10^{-(m-1)} and ||k*theta|| >= 1/poly(m) for all 1 <= k <= L_m (by the three-distance theorem), no two orbit points in the transition zone can share a component of F_m, regardless of their lag separation. Every orbit hit is in a DISTINCT component. This means all pair correlations 1_{F_m}(x_i) * 1_{F_m}(x_j) factor through inter-component (long-range in alpha-space) correlations only. The resonant/bulk decomposition N_m = N_m^{res} + N_m^{bulk} is viable: bulk hits can be eliminated by discrepancy bounds, and only finitely many resonant templates remain to be killed.

25. **The "shortest path" to finiteness is the resonance template reduction + Baker (GPT 5A Pro).** Program: (1) Prove that the number of "danger cylinders" (F_m components that can capture orbit points) has uniformly bounded cardinality. Empirically supported: ~7 persistent orbit points at m=29. (2) Show that persistence of a template to depth m forces {n*theta} within distance ~10^{-m} of a boundary endpoint beta = log10(n_0) for some zeroless integer n_0. (3) If n_0 has bounded prime-factorization complexity (factors into {2,3,5,7}), express |n*theta - beta| as a linear form in logarithms of algebraic numbers and apply Baker/Matveev to get a lower bound contradicting the required proximity. The critical feasibility question is Step (3): whether persistent boundary points have bounded complexity. This program is the most concrete and feasible proof strategy identified in the entire consultation series. References: arXiv:1404.0455 (BRS theory), arXiv:math/0702853 (Tseng MSTP), Bugeaud irrationality measures.

26. **Baker cannot directly build the coboundary transfer function g_m; Ostrowski renormalization is the correct implementation (GPT 5A Pro, 2nd instance).** For discontinuous 1_{F_m}, the Fourier coefficients |f_hat(k)| ~ 1/k, and even with Baker giving |k*theta| >> k^{-A}, the result |g_hat(k)| ~ k^{A-1} is not summable. The Fourier series for g_m diverges. Baker's proper role is to control the near-resonant frequencies (tied to convergents q_j) where the transfer function blows up, not to build g_m globally. The correct implementation: Ostrowski renormalization of Birkhoff sums into convergent blocks, coarse-approximate F_m by f_{m,J} (first J digits, O(10^J) intervals), Denjoy-Koksma on each q_j-block, handle the m-J digit tail by survival rate (exponentially small). Baker controls bad blocks via effective irrationality. This is the most detailed implementation roadmap for Strategy C.

27. **The cluster forcing lemma provides the most direct bridge between Step B and Baker (GPT 5A Pro, 2nd instance).** If N_m >= r (r hits in the transition zone, all in distinct components by Step B+), then by pigeonhole on component positions, there exists h <= H(r) with |h*theta| <= delta_m, where delta_m is exponentially small in m. Baker/Matveev bounds then cap how often theta = log10(2) can be approximated this well, forcing r -> 0 for large m. This is complementary to the danger cylinder program (Conclusion 25): danger cylinders track persistence ACROSS m levels, while cluster forcing examines cluster structure AT fixed m. Both converge to the same Baker contradiction on |h*theta| <= delta_m. Additionally, Step B yields a dependency graph bound: F_m intersect (F_m - theta) involves cross-component overlap only, giving quasi-independence mu(F_m intersect (F_m - theta)) <= c * mu(F_m)^2, which initializes a sharp second-moment bound Var(N_m) <= E[N_m] + log|I_m| * E[N_m]. Two independent Pro instances arrive at the same endgame independently, confirming it as the natural "shortest path."

28. **Exact component geometry: uniform x-space width and the 9->0 disconnection principle (GPT 5B Pro).** In x = 10^alpha coordinates, all 9^{m-1} components of F_m have the same width: exactly 9 * 10^{-(m-1)} in x-space. The log transform alpha = log10(x) compresses these non-uniformly; the widest alpha-space component occurs at the all-1's prefix (smallest x), with exact maximum max_comp(F_m) = log10(1 + 81/(10^m - 1)) ~ (81/ln(10)) * 10^{-m}. The key structural fact: only the 9->0 digit transition creates a gap (disconnects F_m); transitions k->(k+1) for k in {1,...,8} are interior to the set because the boundary point has a nonzero last digit. This explains why there are 9^{m-1} components (one per allowed (m-1)-digit prefix) rather than 9^m. Persistence (alpha in F_m for many consecutive m) is equivalent to x = 10^alpha having a long initial block of digits avoiding 0, a restricted-digit Cantor set property with Hausdorff dimension log(9)/log(10), orthogonal to continued fractions.

29. **O(1) danger cylinders confirmed; persistence is a relay effect (Exp 30).** The number of distinct F_m components hit by orbit points in the transition zone is O(1), bounded by 9 across m=2..27. Every hit is in a distinct component (N_m = n_components for all m), confirming Step B+ empirically. No orbit index persists for more than 5 consecutive m-levels; the apparent persistence from Exp 29 (~7 persistent orbit points) is actually a relay effect across sequential index waves (indices 22-28 persist around m=8-12, indices 46-58 around m=18-24). N_27 = 0 (zero hits at the highest tested level). This supports the resonance template program (Conclusion 25) but complicates the Baker step: persistence cannot be attributed to individual orbit indices tracking a single boundary point across many m values.

30. **Boundary complexity blocks Strategy D (Exp 31).** Only 5 out of 94 boundary integers examined (5.3%) are {2,3,5,7}-smooth, all at m <= 3. For m >= 4, no boundary integer factors entirely into small primes. The maximum prime factor grows from 7 (m=2) to 65537 (m=10). Strategy D (applying Baker to boundary points beta = log10(n_0)) is therefore blocked: log10(n_0) cannot be expressed as a linear form in logs of small primes. Strategy E (cluster forcing) was proposed as an alternative but is also blocked (see Conclusions 34-35).

31. **Multi-lag Step B+ precisely characterized (Exp 34).** Step B+ (max_comp(F_m) < min_{k<=L_m} ||k*theta||) holds for all m >= 4 with exponentially decaying ratio ~0.34 * 10^{-(m-4)}. It FAILS at m=2 (ratio 2.68) and m=3 (ratio 3.31) because the widest F_2 component (width 0.2596) exceeds ||3*theta|| = 0.0969, and the widest F_3 component (width 0.0341) exceeds ||10*theta|| = 0.0103. These failures are harmless for the finiteness proof (which needs only sufficiently large m) and m=2,3 fall within the finite verification range. The minimum ||k*theta|| is ||10*theta|| = 0.0103 for all m >= 3 (since L_m < q_3 = 93 for m <= 27).

32. **Quasi-independence confirmed; second moment viable (Exp 32).** The correlation ratio mu(F_m cap (F_m - h*theta))/mu(F_m)^2 is bounded by 1.58 for lag h=1 and lies within [0.97, 1.04] for all lags h >= 3, across m=2..10 over the full orbit T_m. The lag-1 positive correlation (consecutive orbit points share digit structure) is real but bounded. Var(N_m)/E[N_m] ~ 1.26 at m=10 (bounded). This confirms the dependency graph bound from Conclusion 27 (mu(F_m cap (F_m - theta)) <= c * mu(F_m)^2 with c ~ 1.58) and validates both the second moment method and the dependency graph approach. The second moment doesn't directly give finiteness for specific theta, but combined with Borel-Cantelli it gives finiteness for a.e. theta.

33. **Ostrowski renormalization not asymptotically viable (Exp 33).** The J-digit coarse approximation of F_m by f_{m,J} produces an approximation error proportional to L * (rho_J - rho_m) = L * 0.9^J * (1 - 0.9^{m-J}), which is small only when J ~ m. But J ~ m makes the Denjoy-Koksma variation bound 9^J ~ 9^m, recovering the useless circle variation. The actual DK bounds are 10,000x too conservative compared to observed block discrepancies (DK gives ~162 while actual is ~0.01 at m=8). The CF of theta = [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, ...] gives convergent denominators q_0=1, q_1=3, q_2=10, q_3=93. The transition zone L_m < q_3 = 93 for all m <= 27, so Ostrowski decompositions use only q_0, q_1, q_2 blocks. The route (Conclusion 26) is formally correct but quantitatively useless.

34. **CORRECTED: Cluster forcing pigeonhole step is INCORRECT (Exp 35, corrected analysis).** The minimum pairwise gap delta_m between hit positions concentrates at O(1) constants ||q_j*theta|| (0.0969 for q_1=3, 0.0103 for q_2=10), NOT at rho_m ~ 0.9^m. The original claim that "pigeonhole on component measure forces ||h*theta|| <= rho_m" was wrong: having N_m points in a set of measure rho_m does NOT force any pair within distance rho_m, because the 9^{m-1} components of F_m are scattered across [0,1) and hits can land in components far apart. Strategy E is blocked.

35. **Strategy E pigeonhole gap: all rescue attempts fail (post-Exp 35 analysis).** Three alternative formulations were tested: (a) Baker on boundary positions of F_m requires the boundary integers to be {2,3,5,7}-smooth, but 95% are non-smooth (Exp 31); (b) Baker on theta directly gives orbit well-spacing (||h*theta|| >= c/h^A), but this only controls orbit spacing, not orbit position relative to F_m. A well-spaced orbit trivially fits in the complement of F_m (which has measure 1 - rho_m -> 1); (c) effective equidistribution of {frac(n*log10(2))} with error much smaller than 0.9^m is an open problem in analytic number theory (the best known discrepancy bound O(log L / L) is far too weak). The true remaining gap is certifying theta = log10(2) is "generic" for the shrinking target problem with F_m. Two viable paths remain: Strategy C' (o(1) coboundary via low-frequency Fourier mass bound) and Strategy F (second moment for a.e. theta, needing Diophantine specialization to theta = log10(2)).
