# C-Series Prompts: Information Theory and Density Zero

## Context for all prompts

These prompts build on 34 prior AI responses (16 metaprompt, 10 A-series on equidistribution, 8 B-series on transfer matrices) and 10 computational experiments. The C-series feeds NEW experimental findings back for theoretical analysis.

**Problem**: 2^86 is the last power of 2 with no digit 0 in base 10 (the "86 Conjecture"). We seek proof mechanisms.

**Prior results (established in A/B series)**:
- The orbit of 2^n mod 10^k has period T_k = 4*5^{k-1}
- Transfer matrix for m-fold constraint (x, 2x, ..., 2^{m-1}x all zeroless mod 10^k): state space is carry vector (c_1,...,c_{m-1}) in {0,1}^{m-1}, dimension 2^{m-1}
- For m=2: M = [[4,4],[4,5]], rho ~ 8.531
- For m=3: M = [[2,2,1,1],[2,2,2,3],[2,2,2,2],[2,2,2,3]], rho ~ 8.035
- Pair extinction is provably false (lifting lemma: >= 4 lifts per level)
- The A-series identified three impossibilities: target can't be compressed, orbit can't be averaged, dynamics can't be mixed

**New experimental data (from Experiments 9 and 10)** is included in each prompt below.

---

## Prompt C1: The Information Constant and Asymptotic Behavior of beta(m)

We study the m-fold zeroless constraint: x, 2x, 4x, ..., 2^{m-1}x all have nonzero digits mod 10^k. The transfer matrix M_m has dimension 2^{m-1} x 2^{m-1}, with state space = carry vectors in {0,1}^{m-1}. We define:

- rho(m) = spectral radius of M_m
- beta(m) = rho(m) / 2 (the orbit branching factor, verified empirically)

We computed M_m and rho(m) for m = 1 through 18. Here is the complete data:

| m | dim | rho(m) | beta(m) | beta(m) - 4 |
|---|-----|--------|---------|-------------|
| 1 | 1 | 9.00000000 | 4.50000000 | +0.50000000 |
| 2 | 2 | 8.53112887 | 4.26556444 | +0.26556444 |
| 3 | 4 | 8.03537824 | 4.01768912 | +0.01768912 |
| 4 | 8 | 7.50527616 | 3.75263808 | -0.24736192 |
| 5 | 16 | 7.02036781 | 3.51018391 | -0.48981609 |
| 6 | 32 | 6.63180024 | 3.31590012 | -0.68409988 |
| 7 | 64 | 6.27616597 | 3.13808298 | -0.86191702 |
| 8 | 128 | 5.91173712 | 2.95586856 | -1.04413144 |
| 9 | 256 | 5.59399057 | 2.79699528 | -1.20300472 |
| 10 | 512 | 5.26771462 | 2.63385731 | -1.36614269 |
| 11 | 1024 | 4.97814311 | 2.48907156 | -1.51092844 |
| 12 | 2048 | 4.70220636 | 2.35110318 | -1.64889682 |
| 13 | 4096 | 4.46197812 | 2.23098906 | -1.76901094 |
| 14 | 8192 | 4.22915813 | 2.11457906 | -1.88542094 |
| 15 | 16384 | 4.01591532 | 2.00795766 | -1.99204234 |
| 16 | 32768 | 3.80122776 | 1.90061388 | -2.09938612 |
| 17 | 65536 | 3.60044482 | 1.80022241 | -2.19977759 |
| 18 | 131072 | 3.41292876 | 1.70646438 | -2.29353562 |

The information per additional constraint is remarkably stable:

| transition | delta(ln beta) | nats | bits |
|------------|---------------|------|------|
| m=1->2 | 0.0535 | 0.054 | 0.077 |
| m=2->3 | 0.0599 | 0.060 | 0.086 |
| m=3->4 | 0.0682 | 0.068 | 0.098 |
| m=4->5 | 0.0668 | 0.067 | 0.096 |
| m=5->6 | 0.0569 | 0.057 | 0.082 |
| m=6->7 | 0.0551 | 0.055 | 0.080 |
| m=7->8 | 0.0598 | 0.060 | 0.086 |
| m=8->9 | 0.0552 | 0.055 | 0.080 |
| m=9->10 | 0.0601 | 0.060 | 0.087 |
| m=10->11 | 0.0565 | 0.057 | 0.082 |
| m=11->12 | 0.0570 | 0.057 | 0.082 |
| m=12->13 | 0.0524 | 0.052 | 0.076 |
| m=13->14 | 0.0536 | 0.054 | 0.077 |
| m=14->15 | 0.0517 | 0.052 | 0.075 |
| m=15->16 | 0.0549 | 0.055 | 0.079 |
| m=16->17 | 0.0543 | 0.054 | 0.078 |
| m=17->18 | 0.0535 | 0.054 | 0.077 |

Mean from m=5 onward: 0.0550 nats (0.0793 bits) per constraint.

Characteristic polynomials (nonzero parts only):

- m=1: [1, -9]
- m=2: [1, -9, 4]
- m=3: [1, -9, 8, -2]
- m=4: [1, -9, 12, -6, 1]
- m=5: [1, -9, 16, -16, 9, -2]
- m=6: [1, -9, 19, -24, 15, -5, 1, -1]
- m=7: [1, -9, 22, -34, 22, -9, -18, 24, -28, 17, -10, 1, 1]
- m=8: [1, -9, 24, -38, 25, -2, -28, 13, 25, -71, 91, -74, 43, -22, 6, -1, -1]

Note: the trace is always 9 (coefficient of lambda^{d-1} is always -9). The number of nonzero eigenvalues grows much slower than 2^{m-1}.

Additional data: beta(m) compared with the independence prediction beta_indep(m) = 5*(9/10)^m:

| m | beta(m) | beta_indep(m) | ratio |
|---|---------|---------------|-------|
| 1 | 4.500 | 4.500 | 1.000 |
| 2 | 4.266 | 4.050 | 1.053 |
| 3 | 4.018 | 3.645 | 1.102 |
| 5 | 3.510 | 2.953 | 1.189 |
| 8 | 2.956 | 2.151 | 1.374 |
| 10 | 2.634 | 1.744 | 1.510 |
| 15 | 2.008 | 1.034 | 1.941 |
| 18 | 1.706 | 0.756 | 2.257 |

The ratio beta(m)/beta_indep(m) grows with m, indicating strengthening positive correlation.

**Questions:**

1. The information constant ~0.055 nats per doubling constraint is stable from m=5 to m=18. Can you derive this from the entropy rate of the carry Markov chain? Specifically: the carry chain has state space {0,1} and transition probabilities depending on the digit distribution. What is the conditional entropy H(c_{i+1} | c_i) and how does it relate to the 0.055-nat constant?

2. Does beta(m) -> 0 as m -> infinity, or does it converge to a positive limit? The exponential fit beta ~ 4.71 * exp(-0.057m) gives beta(27) ~ 1.0 and beta -> 0. But could there be a floor? The growing ratio beta/beta_indep suggests the positive correlation might eventually stabilize beta above some threshold.

3. The characteristic polynomials have a growing number of zero eigenvalues. What determines the "effective rank" (number of nonzero eigenvalues)? Is there a closed-form for the dimension of the active subspace as a function of m?

4. The second-largest eigenvalue magnitude is approximately 2.1 for m >= 14. This appears to be converging. What is the subdominant eigenvalue, and does it determine the asymptotic information rate?

5. If beta(m) -> 0, the m-fold survivor tree eventually dies out for large m. What is the mathematical meaning of this? In particular: if beta(m_0) < 1 for some m_0, does this prove that for sufficiently large k, there are no m_0 consecutive zeroless orbit elements at level k? What implications does this have for the 86 Conjecture?

---

## Prompt C2: Perfect Digit Uniformity Among Orbit Survivors

We discovered a striking uniformity phenomenon in the orbit of 2^n mod 10^k.

**Setup**: At each level k, the orbit {2^n mod 10^k : n = 0, 1, ..., T_k - 1} visits T_k = 4*5^{k-1} distinct residues. Among these, the "survivors at level k" are those whose last k digits are all nonzero (no digit 0 among the trailing k digits).

**Observation**: Among the survivors at level m-1, the digit at position m is distributed exactly uniformly across {0, 1, 2, ..., 9}. Here is the data:

| m | survivors at m-1 | digit 0 count | digit 0 fraction | chi-squared |
|---|-----------------|---------------|-----------------|-------------|
| 2 | 20 | 4 | 0.200000 | 3.00 |
| 3 | 88 | 9 | 0.102273 | 0.18 |
| 4 | 403 | 41 | 0.101737 | 0.10 |
| 5 | 1818 | 181 | 0.099560 | 0.01 |
| 6 | 8189 | 819 | 0.100012 | 0.00 |
| 7 | 36854 | 3685 | 0.099989 | 0.00 |
| 8 | 165849 | 16582 | 0.099983 | 0.00 |
| 9 | 746339 | 74639 | 0.100007 | 0.00 |
| 10 | 3358504 | 335852 | 0.100000 | 0.00 |
| 11 | 15113264 | 1511320 | 0.100000 | 0.00 |
| 12 | 68009724 | 6800982 | 0.100000 | 0.00 |

The chi-squared statistic (9 degrees of freedom, significance threshold 16.92 at 5%) is essentially zero for m >= 5. The distribution is not just approximately uniform; it appears to be EXACTLY uniform for m >= 5.

At level m=2, the digit 0 fraction is 0.20 (double the expected 0.10), but this is a finite-size effect with only 20 survivors.

**Additional context**: The orbit of 2^n mod 10^k lies in the coset C_k = {x : 2^k | x, gcd(x, 5) = 1}. The CRT map r(u) = 2^k * (2^{-k} mod 5^k) * u mod 10^k converts 5-adic units u to elements of this coset. The digit constraint "digit m is nonzero" is an additive condition in base 10, while the orbit is a multiplicative object (cyclic group under multiplication by 2).

**Related finding**: The conditional survival rate S_m = P(digit m nonzero | digits 1..m-1 all nonzero) along the actual trajectory of 2^n (not just the orbit mod 10^k) is:

Mean S_m = 0.903 (for m = 2..30), with fluctuations of +-0.008 around this mean.

This is slightly above 0.9, and the 0.003 excess is consistent with the orbit having ~11% more zeroless residues than random (since 0.9 * 1.003^{many levels} builds up to the 11% enrichment).

**Questions:**

1. Can the exact uniformity for m >= 5 be proved? The orbit mod 10^m is a cyclic group of order T_m = 4*5^{m-1}, acting by multiplication by 2. The survivors at level m-1 form a subset S_{m-1} of this group. The claim is: for each digit value d in {0,...,9}, exactly |S_{m-1}|/10 elements of S_{m-1} have digit d at position m. What group-theoretic or number-theoretic property of the orbit would guarantee this?

2. The uniformity breaks down at m=2 (digit 0 fraction is 0.20 instead of 0.10). What causes this? Is it purely a small-sample effect, or is there a structural reason related to the short orbit period at level 2 (T_2 = 20)?

3. If the exact uniformity IS provable, it immediately gives S_m = 0.9 for the conditional survival rate on the orbit. Combined with the convergent heuristic sum, this would prove density zero for zeroless powers. How far does this take us? Specifically: does S_m = 0.9 at every level, combined with S_1 = 1, give a proof that #{n <= N : 2^n is zeroless} = O(1)?

4. The digit uniformity among orbit survivors is much stronger than generic equidistribution of the orbit. The orbit itself is NOT equidistributed in [0, 10^k) (it lives in a thin coset of density ~2^{-k}). But among the survivors, the next digit is perfectly uniform. Is this a consequence of the Chinese Remainder Theorem structure? The digit at position m depends on x mod 10^m but the survival condition at level m-1 depends on x mod 10^{m-1}. The "fiber" over each residue mod 10^{m-1} has exactly 10 elements mod 10^m, and the claim is that the orbit visits all 10 fibers equally. When does a cyclic group action on Z/10^m Z have this fiber-equidistribution property?

5. The autocorrelation of the zeroless indicator I_k(n) shows a periodic spike at lag 20. This connects to the dominant Fourier character at j = 5^{k-2} of order 20 (identified in A-series prompt A3). Does the digit uniformity phenomenon coexist with this lag-20 correlation? How do the two interact?

---

## Prompt C3: Closing the Density-Zero Argument

We have assembled a complete quantitative picture of the zeroless-powers problem from 10 computational experiments and 34 AI analyses. The density-zero argument appears to be "morally complete" but lacks one rigorous bridge. This prompt asks: what exactly is the missing lemma, and can it be proved?

**The argument structure:**

Step 1. For 2^n to be fully zeroless, ALL k(n) = floor(n*log10(2)) + 1 digits must be nonzero.

Step 2. Decompose this into conditional survival: P(2^n zeroless) = product_{m=1}^{k(n)} S_m(n), where S_m(n) = P(digit m of 2^n is nonzero | digits 1..m-1 are all nonzero).

Step 3. S_1 = 1 always (the ones digit of 2^n is always 2, 4, 6, or 8).

Step 4. For m >= 2, S_m ~ 0.9 empirically (measured on n = 1..50000, levels m = 2..30). The deviation from 0.9 is at most 0.008.

Step 5. The heuristic sum Z_heur = sum_{n=1}^{infinity} (0.9)^{k(n)-1} converges, because k(n) ~ 0.301*n gives a geometric series with ratio 0.9^{0.301} ~ 0.969. The sum is approximately 31.

Step 6. The actual count Z(50000) = 35. No zeroless power after n = 86 in 50000 checked. Z(N)/N -> 0.

**The empirical evidence for S_m = 0.9:**

From the orbit mod 10^k (Part D of Experiment 9), among survivors at level m-1, digit m is distributed exactly uniformly across {0,...,9} for m >= 5. This gives S_m = 9/10 = 0.9 exactly.

From the actual trajectory of 2^n (Part B of Experiment 9):

| level m | n checked | survived | S_m |
|---------|-----------|----------|-----|
| 2 | 49997 | 44999 | 0.900034 |
| 3 | 44996 | 40499 | 0.900058 |
| 4 | 40496 | 36399 | 0.898830 |
| 5 | 36398 | 32759 | 0.900022 |
| 10 | 21471 | 19302 | 0.898980 |
| 15 | 12652 | 11456 | 0.905469 |
| 20 | 7533 | 6794 | 0.901898 |
| 25 | 4425 | 4009 | 0.905989 |
| 30 | 2587 | 2323 | 0.897951 |

**What the transfer matrix gives (but is too weak):**

The single-doubling transfer matrix M = [[4,4],[4,5]] with rho ~ 8.531 gives a rigorous bound: the fraction of k-digit zeroless numbers x such that 2x is also k-digit-zeroless is at most (rho/9)^k ~ (0.948)^k. This bounds the PAIR survival, not the single conditional survival.

For single digits: among all 9^k zeroless k-digit strings, the fraction with 2x also zeroless is (rho/9)^k. But we want S_m for the specific orbit, not for random strings.

**The gap:**

The argument needs: for all m >= 2, S_m <= C for some constant C < 1, uniformly along the orbit.

We OBSERVE S_m ~ 0.9 with tiny fluctuations. But proving S_m < 1 - epsilon along the orbit requires showing the orbit doesn't systematically avoid zeros at level m. This is a weaker statement than full equidistribution (we don't need uniform distribution of all digits, just that digit 0 has positive frequency). But it's still about the specific orbit, not generic behavior.

**Additional data that might help:**

The beta(m) sequence from Experiment 10 shows that the m-fold constraint has spectral radius rho(m) and orbit branching factor beta(m) = rho(m)/2:

| m | rho(m) | beta(m) |
|---|--------|---------|
| 1 | 9.000 | 4.500 |
| 2 | 8.531 | 4.266 |
| 3 | 8.035 | 4.018 |
| 4 | 7.505 | 3.753 |
| 5 | 7.020 | 3.510 |
| 10 | 5.268 | 2.634 |
| 15 | 4.016 | 2.008 |
| 18 | 3.413 | 1.706 |

The enrichment constant: the orbit has ~11% more zeroless residues than the random prediction (0.9^k). This ratio is constant in k, determined by the Perron-Frobenius eigenvector.

**Questions:**

1. What is the precise lemma needed to close the density-zero argument? State it as a mathematical claim about the orbit {2^n mod 10^k} and the set of zeroless residues.

2. Is the digit-uniformity observation (Part D) provable, and if so, does it suffice? The claim "digit m is uniform among orbit survivors at level m-1" is equivalent to "each fiber of the projection 10^m -> 10^{m-1} contains exactly 1/10 of the orbit's survivors." What tools from algebraic number theory or additive combinatorics could establish this?

3. The transfer matrix bound S_m <= 0.948 is for arbitrary strings. Can it be sharpened ON THE ORBIT? The orbit has additional structure: it's a cyclic group, its elements are divisible by 2^k, and it has the exact uniformity property. Do any of these constrain S_m to be closer to 0.9?

4. Consider a weaker target: instead of S_m = 0.9, prove S_m <= 0.99 (or even S_m <= 1 - epsilon for any epsilon > 0). Is this easier? What would it take?

5. Three 2025 papers are directly relevant:
   - Dumitru (arXiv:2503.23177): metric finiteness for "all digits even" in powers of 2
   - Noda (arXiv:2510.18414): transfer-operator for digit-weighted functions of 2^n
   - Lagarias (math/0512006): ternary digits of 2^n

   Given our experimental data, which of these approaches is closest to proving density zero for zeroless powers? What would need to be added or modified?

6. Is there a way to use the beta(m) sequence directly? If beta(m_0) < 1 for some m_0, it proves that m_0-fold zeroless windows eventually die out on the orbit. Combined with the positive autocorrelation (zeroless powers cluster), could this constrain the total count?
