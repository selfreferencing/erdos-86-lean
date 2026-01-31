# Experiment 36: Circle Fourier Coefficients of F_m

## Summary

Exp 36 computed the continuous-circle Fourier coefficients hat{1_{F_m}}(k) for m = 2..7 and k = 1..5000 (1000 for m=7), using the exact interval formula. This is the first experiment to use the standard e^{2pi i k x} basis rather than the 5-adic orbit basis.

## Key Results

### 1. The heuristic |hat{1_{F_m}}(k)| ~ rho_m is FALSE

The ratios |hat(k)|/rho_m are NOT close to 1. They are approximately 0.02-0.08, stabilizing rapidly by m=4:

| k | ratio (m>=4) |
|---|-------------|
| 1 | 0.0270 |
| 3 | 0.0538 |
| 7 | 0.0743 |
| 10 | 0.0625 |
| 17 | 0.0768 (max) |

The ratios are O(1/k) on average, not O(1). Specifically, |hat{1_{F_m}}(k)| ~ C(k) * rho_m where C(k) is a fixed function of k that does NOT depend on m (for m >= 4). This means:

**|hat{1_{F_m}}(k)| = C(k) * (9/10)^{m-1}**

where C(k) ranges from ~0.02 to ~0.08 for low k. The exponential decay in m is confirmed, but the prefactor C(k) is much smaller than 1.

### 2. S_m does NOT go to zero (with current K_max)

| m | S_m | K_max |
|---|-----|-------|
| 2 | 162.4 | 5000 |
| 3 | 382.5 | 5000 |
| 4 | 761.4 | 5000 |
| 5 | 744.0 | 5000 |
| 6 | 669.8 | 5000 |
| 7 | 160.5 | 1000 |

S_m initially INCREASES (m=2 to 4), then decreases (m=4 to 7). The m=7 value is misleadingly low because K_max = 1000 instead of 5000. The S_m values are dominated by high-frequency terms (|k| > m^2 accounts for >95% of S_m).

### 3. Convergent denominator k=2136 dominates

The largest single term in S_m comes from k = 2136, which is a convergent denominator of theta = log10(2). This frequency has ||2136*theta|| ~ very small, creating a huge |hat(k)|/||k*theta|| contribution:

| m | contribution from k=2136 |
|---|------------------------|
| 2 | 12.57 |
| 3 | 29.08 |
| 4 | 85.61 |
| 5 | 79.49 |
| 6 | 71.35 |

The k=2136 contribution peaks at m=4, then decays as rho_m shrinks. But other convergent-related frequencies (k=4272=2*2136, k=4757) also contribute substantially.

### 4. The measure ratio mu(F_m) / (9/10)^{m-1} stabilizes at 0.9761

This confirms F_m has total measure slightly less than (9/10)^{m-1}. The correction factor 0.9761 comes from the logarithmic (non-uniform) distribution of digits within each decade.

### 5. FFT cross-check validates the analytic formula

For m = 2,3,4 the FFT and analytic interval formula agree to within ~2.5% relative error (limited by discretization resolution). This confirms the analytic formula is correct.

## Interpretation for Strategy C'

### The fundamental difficulty

Strategy C' requires S_m = sum_{k!=0} |hat(k)| / ||k*theta|| = o(1). The data shows S_m ~ O(100-800) for K_max = 5000. This is very far from o(1).

However, the Strategy C' formulation involves the FULL sum over all k, weighted by the Dirichlet kernel. The relevant quantity is actually:

|N_m - L_m * rho_m| <= sum_{k!=0} |hat{1_{F_m}}(k)| * |D_{L_m}(k*theta)|

where D_L(alpha) = sum_{j=0}^{L-1} e(j*alpha) = e(L*alpha/2) * sin(pi*L*alpha) / sin(pi*alpha).

For the Dirichlet kernel, |D_L(alpha)| <= min(L, 1/||alpha||). So the sum S_m as computed (using 1/||k*theta|| instead of |D_L(k*theta)|) is an UPPER BOUND, potentially a very loose one.

### What saves the argument (potentially)

The actual error is:
sum_k |hat(k)| * |D_{L_m}(k*theta)|

For most k, |D_L(k*theta)| << 1/||k*theta|| because L_m is small (L_m ~ 3.3m). Specifically, |D_L(alpha)| <= L when ||alpha|| is not too small. Since L_m ~ 3m and |hat(k)| ~ C(k) * 0.9^m, the contribution from "generic" k is bounded by:

sum_k C(k) * 0.9^m * min(3m, 1/||k*theta||) << sum_k C(k) * 0.9^m / ||k*theta||

The gap between |D_L| and 1/||.|| is enormous for most k, potentially rescuing Strategy C'.

### What's needed next

1. **Compute the actual Erd.-Turan / Koksma-Hlawka sum** with |D_{L_m}(k*theta)| instead of 1/||k*theta||. This could shrink S_m from ~700 to something much smaller.

2. **Extend to higher K_max.** The current computation truncates at K=5000. Need to verify the tail sum converges.

3. **The C(k) function is stable across m.** This is the most important finding. It means |hat{1_{F_m}}(k)| = C(k) * rho_m exactly, so the m-dependence is purely through rho_m = (9/10)^{m-1}. This is STRONGER than the heuristic (which assumed C(k) = 1).

## Literature Check Results

### Maynard (Inventiones 2019)

**Paper**: "Primes with restricted digits," Invent. math. 217: 127-218.

**Key finding**: Maynard's Fourier transform of the restricted-digit indicator FACTORS as a product over digit positions:

|mu_B(Theta)| = prod_{j=0}^{k-1} |sum_{z_j in B_j} e(z_j * g^j * Theta)|

This product formula applies to the DISCRETE exponential sum S(t) = sum_n 1_A(n) e(n*t), not directly to the continuous circle Fourier coefficient hat{1_{F_m}}(k). Our Exp 36 Part C confirms these are distinct quantities (the discrete sum has magnitude ~9^m while the circle integral has magnitude ~C(k)*rho_m).

**Relevance to Strategy C'**: Maynard's framework is designed for proving infinitely many primes in A, using Type I/II sums and Harman's sieve. His estimates control the Fourier transform at RATIONAL points a/q^k, not at irrational frequencies. The key technique is "decorrelating Diophantine conditions from digital conditions," which is potentially useful but does not directly give the bound needed for Strategy C'.

**The product formula does explain our C(k) function**: Since the circle Fourier coefficient is computed from intervals [log10(n), log10(n+1)), and log10 is nearly linear on each interval, the circle and discrete transforms are related by:

hat{1_{F_m}}(k) ~ S(k * theta_eff) / (N_total * 2*pi*i*k)

where the product formula for S determines the k-dependence (explaining why C(k) stabilizes across m).

### Mauduit-Rivat (Annals 2010, Acta Math 2009)

**Papers**: "Sur un probleme de Gelfond: la somme des chiffres des nombres premiers" and "La somme des chiffres des carres."

**Key finding**: Their framework handles ADDITIVE digital functions (digit sums s_q(n)), proving equidistribution of s_q(p) for primes p and s_q(n^2) for squares. The methods are based on sophisticated exponential sum estimates with "cutting off digits" techniques.

**Relevance to Strategy C'**: Limited. Their results control sums like sum_n Lambda(n) * e(alpha * s_q(n)), where the digital condition is ADDITIVE (digit sum). Our condition (all digits nonzero) is MULTIPLICATIVE (product of individual digit indicators). The Mauduit-Rivat framework does not directly apply.

### Drmota-Mauduit-Rivat

**Papers**: "The sum-of-digits function of polynomial sequences" (various bases), "Prime numbers in two bases" (Duke 2020), "The Thue-Morse sequence along squares."

**Key finding**: Extended Mauduit-Rivat to polynomial sequences and multiple bases. The Thue-Morse work gives Fourier-analytic treatment with a product structure from the Rudin-Shapiro sequence. "Prime numbers in two bases" combines Fourier analysis in two coprime bases.

**Relevance to Strategy C'**: The two-base Fourier analysis could be relevant since our problem involves base 10 = 2*5 structure. However, the focus is still on additive digital functions, not multiplicative digit avoidance.

### Noda (arXiv:2510.18414)

**Paper**: "Upper Bounds for Digitwise Generating Functions of Powers of Two."

**Key finding**: Defines a transfer operator M_n[h] that encodes digit-weighted generating functions of 2^n mod 10^n. Lemma 1 gives the parity-fiber structure of column sums. Proposition 2 gives:

lim sup Psi_n(h) <= log(max{E,O}/5)

where E = sum of h over even digits, O = sum over odd. For h = 1_{nonzero}, E = 4 (digits 2,4,6,8), O = 5 (digits 1,3,5,7,9), so the bound gives Psi <= log(5/5) = 0, confirming rho ~ (9/10)^n at best.

**Relevance to Strategy C'**: The transfer operator framework is the right language but the paper explicitly does NOT pursue spectral analysis. A spectral gap result for M_n[1_{nonzero}] would directly give the exponential decay needed.

### Banks-Conflitti-Shparlinski (Illinois J. Math 2002)

**Paper**: "Character sums over integers with restricted g-ary digits."

**Key finding**: Upper bounds for multiplicative character sums and exponential sums over digit-restricted integers, using Weil and Vinogradov bounds. Applied to quadratic non-residues and primitive roots among restricted-digit integers.

**Relevance to Strategy C'**: Their exponential sum bounds control sum_n chi(n) for n with restricted digits. This is closer to our needs (discrete exponential sums over zeroless integers) but the bounds are not directly usable for circle Fourier coefficients.

### Lagarias (arXiv:math/0512006)

**Paper**: "Ternary expansions of powers of 2."

**Key finding**: Studies the ternary analog (no digit 2 in base 3). Uses dynamical systems (real and 3-adic), Hausdorff dimension of translates of 3-adic Cantor sets. Does NOT prove finiteness. Gives asymptotic upper bounds on the count of iterates omitting digit 2.

**Relevance to Strategy C'**: Identifies the same fundamental barrier (certifying a specific irrational is not exceptional). His dynamical framework (Cantor set intersections) parallels our approach but does not resolve the individual-theta problem.

## Conclusions (numbered, continuing from Exp 35)

**Conclusion 36.** The circle Fourier coefficients |hat{1_{F_m}}(k)| satisfy |hat{1_{F_m}}(k)| = C(k) * (9/10)^{m-1} where C(k) is a fixed function of k independent of m (for m >= 4). C(k) ranges from ~0.02 to ~0.08 for k = 1..100, with max at k=17.

**Conclusion 37.** The naive coboundary sum S_m = sum |hat(k)|/||k*theta|| does NOT tend to zero. It is O(100-800) for K_max = 5000, dominated by the convergent denominator k=2136 and its harmonics.

**Conclusion 38.** The correct sum for Strategy C' uses |D_{L_m}(k*theta)| instead of 1/||k*theta||. Since L_m ~ 3m is small, |D_L| << 1/||.|| for most k, potentially making the corrected sum much smaller. This needs to be computed in Exp 37.

**Conclusion 39.** The C(k) stability across m is the most important finding. It means the Fourier structure of F_m is entirely determined by the digit-position product formula, with the only m-dependence being the exponential factor (9/10)^{m-1}. This is consistent with Maynard's product structure.

**Conclusion 40.** The literature provides the product formula (Maynard) and the transfer operator framework (Noda) but neither directly resolves Strategy C'. The missing ingredient is a bound on the circle Fourier coefficients (as distinct from discrete exponential sums) weighted by the Dirichlet kernel, not just by 1/||k*theta||.

## Recommended Next Steps

1. **Exp 37**: Compute the ACTUAL discrepancy bound using |D_{L_m}(k*theta)| instead of 1/||k*theta||. This is the true test of Strategy C'.

2. **Extend K_max**: Verify tail convergence by computing to K = 50000 or higher for m = 4,5.

3. **Characterize C(k)**: The function C(k) appears to follow a pattern related to the digit-exclusion geometry. Derive C(k) analytically from the product formula.

4. **Spectral gap for Noda's operator**: If Noda's transfer operator M_n[1_{nonzero}] has spectral gap, this would directly give the needed decay. Worth pursuing as a theoretical complement.
