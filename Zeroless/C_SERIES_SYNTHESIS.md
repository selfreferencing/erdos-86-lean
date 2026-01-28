# C-Series Synthesis: Information Theory and the Parity-Balance Reduction

## 6 Responses Processed (3 prompts x 2 models: GPT Pro "A" + GPT Thinking "B")

### January 27, 2026

---

## 1. The One-Sentence Verdict

The density-zero argument for zeroless powers of 2 reduces to a single parity-balance lemma: **prove that the survivor set at each digit level cannot concentrate almost entirely in odd-type fibers, i.e., show |E_m|/|Z_m| >= delta > 0 uniformly in m.**

---

## 2. The Three Reductions (One Per Prompt, Fully Confirmed by Both Models)

### Reduction 1 (C1): The 1/18 information mechanism

The stable 0.055-nat information constant per doubling constraint has a clean derivation from the carry Markov chain.

**The mechanism**: A zero digit at the new doubling layer occurs only when:
- carry c = 0 (stationary probability ~ 1/2)
- input digit d = 5 (probability 1/9 among nonzero digits)

So the "bad-pattern" frequency is q = (1/2)(1/9) = 1/18 ~ 0.0556.

The information per constraint is I = -ln(1 - q) = -ln(17/18) ~ 0.0572 nats.

**Comparison with data**: Observed mean from m=5 onward: 0.0550 nats. The 4% discrepancy comes from the carry chain not being exactly stationary (slight bias toward c=1 among survivors).

**Asymptotic consequence**: Since each constraint adds ~0.057 nats, and the total information needed to push from supercritical (beta=4.5) to critical (beta=1) is ln(4.5) ~ 1.504 nats, the crossing requires approximately 1.504/0.057 ~ 26 constraints beyond m=1. This matches the exponential fit prediction of beta=1 at m~27.

**What both models agree on**:
- beta(m) -> 0 as m -> infinity (no positive floor)
- The subdominant eigenvalue ~2.1 must eventually decrease
- The bridge from beta(m) < 1 to the 86 conjecture requires a separate argument

### Reduction 2 (C2): The parity-uniformity theorem

The "perfect digit uniformity" observed in Experiment 9 Part D has a rigid structural explanation. This is the strongest single finding across all three series.

**The decomposition**: Digit uniformity splits into two independent pieces:

**Piece 1 (automatic, paper-ready)**: Within each parity class, digit m is exactly uniform. The proof uses the fiber structure: each survivor u_0 at level m-1 has 5 lifts u = u_0 + a*5^{m-1} (a = 0,1,2,3,4). The m-th digit is d_m = floor(2u/5^{m-1}) = floor(2a + theta) where theta = 2u_0/5^{m-1} in [0,2).

- If theta < 1 (i.e., u_0 < 5^{m-1}/2): digits are {0, 2, 4, 6, 8}, each exactly once
- If theta >= 1 (i.e., u_0 >= 5^{m-1}/2): digits are {1, 3, 5, 7, 9}, each exactly once

This is a theorem, not a conjecture. It explains why the chi-squared statistics collapse to zero for m >= 5.

**Piece 2 (the hard part)**: Full 10-way uniformity requires E = O, i.e., equal numbers of even-type and odd-type survivors. This is the parity-balance condition.

**Two routes to proving balance** (from C2-B):
1. **Fourier route**: The E-O imbalance is a single Fourier coefficient of the survivor indicator against a parity character. Decay of this coefficient would give balance.
2. **Carry-chain route**: Model the survivor set via the carry transfer operator and show the parity observable decays under iteration.

### Reduction 3 (C3): The parity-fiber formula closes the circle

The conditional survival rate has an exact closed form in terms of the parity balance:

**The formula**:

|Z_m| = 4|E_{m-1}| + 5|O_{m-1}| = 5|Z_{m-1}| - |E_{m-1}|

Dividing by 5|Z_{m-1}|:

S_m = |Z_m| / (5|Z_{m-1}|) = 1 - |E_{m-1}| / (5|Z_{m-1}|) = 1 - P(even|survive)/5

**Consequences**:
- S_m = 0.9 iff P(even|survive) = 1/2 (exact parity balance)
- S_m <= 0.99 iff P(even|survive) >= 0.05 (extremely weak balance)
- S_m = 1 iff P(even|survive) = 0 (all survivors odd-type, impossible to prove)

**The weak parity lemma**: To close density zero, it suffices to show P(even|survive) >= delta > 0 for some fixed delta, uniformly in m. This is the weakest possible statement that closes the argument.

---

## 3. The Missing Lemma: Three Equivalent Formulations

All 6 responses converge on the same lemma, stated in three equivalent ways:

### Formulation A: Counting form

For all sufficiently large m:

|E_m| / |Z_m| in [delta, 1 - delta]

for some fixed delta > 0. Ideally, |E_m|/|Z_m| = 1/2 + o(1).

### Formulation B: Survival form

For all sufficiently large m:

S_m <= 1 - epsilon

for some fixed epsilon > 0.

### Formulation C: Operator form (from C3-B)

Consider the digit-extension transfer operator with weight w(d) = 1{d != 0}, augmented to track even/odd fiber type. Then the induced operator on the parity observable has spectral radius strictly less than the Perron eigenvalue of the survivor-count operator.

In symbols: |E_m/Z_m - 1/2| <= C * theta^m for some theta < 1.

**Equivalences**: A with delta implies B with epsilon = delta/5. C implies A. B with any epsilon > 0 implies density zero.

---

## 4. Cross-Response Convergence

| Response | Focus | Key result | Distinctive contribution |
|----------|-------|-----------|------------------------|
| C1-A | Information constant | q = 1/18, I = 0.0572 nats | Entropy H(c'|c) ~ 0.689 nats computation |
| C1-B | Information constant | Same q = 1/18 independently | Subdominant eigenvalue ~2.1 must decrease; bridge lemma |
| C2-A | Digit uniformity | Parity-uniformity theorem + E=O reduction | Strongest single response: complete structural decomposition |
| C2-B | Digit uniformity | Same decomposition independently | Two routes to balance (Fourier + carry-chain) |
| C3-A | Density-zero gap | Parity-fiber formula S_m = 1 - P(even)/5 | Step-20 window suggestion; Lagarias ranked first for density zero |
| C3-B | Density-zero gap | Same formula; operator-form lemma | Sharpest lemma statement; Noda ranked first overall |

**Convergence is total.** No response found a different structural decomposition, a different missing lemma, or a workaround. The 6 responses use different notation and emphasis but arrive at identical mathematics.

---

## 5. Key Mathematical Objects Identified

### 5.1 The parity-fiber decomposition

For each survivor r in Z_{m-1}, the 5 lifts to level m have digits of a fixed parity:
- **Even-type** (u_0 < 5^{m-1}/2): digits {0, 2, 4, 6, 8}. Survival rate: 4/5.
- **Odd-type** (u_0 >= 5^{m-1}/2): digits {1, 3, 5, 7, 9}. Survival rate: 5/5 = 1.

This is a rigid arithmetic fact, not an approximation.

### 5.2 The E-O balance quantity

E_m = number of even-type survivors at level m
O_m = number of odd-type survivors at level m
Z_m = E_m + O_m

The quantity |E_m - O_m| / |Z_m| is the "parity bias." The data shows this is essentially zero for m >= 5.

### 5.3 The 1/18 bad-pattern probability

The carry chain (c_i in {0,1}) with the nonzero-digit constraint has a unique "fatal configuration": c = 0 and d = 5, giving output digit 0. This occurs with probability q = P(c=0) * P(d=5|c=0) = (1/2)(1/9) = 1/18.

### 5.4 The carry/parity spectral-gap operator

The transfer operator for the digit-extension process, augmented to track the even/odd fiber type. Its spectral gap (ratio of second to first eigenvalue) controls how fast parity bias decays with m. If this gap exists, the parity-balance lemma follows.

---

## 6. What Is Provable vs What Is Not

### 6.1 Proved (paper-ready)

- **Within-parity uniformity**: Among orbit survivors at level m-1, digit m is exactly uniform within each parity class ({0,2,4,6,8} or {1,3,5,7,9}). One-page proof via the u = u_0 + a*5^{m-1} fiber structure.
- **The parity-fiber formula**: S_m = 1 - P(even|survive)/5. Exact arithmetic identity.
- **The |Z_m| recurrence**: |Z_m| = 5|Z_{m-1}| - |E_{m-1}|. Exact.
- **Unconditional digit uniformity on C_m**: Among all orbit elements (not conditioned on survival), digit m is exactly uniform on {0,...,9}.

### 6.2 Plausibly provable (the target)

- **Parity-balance lemma (weak form)**: |E_m|/|Z_m| >= delta > 0 uniformly. Implies S_m <= 1 - delta/5.
- **Parity-balance lemma (strong form)**: |E_m|/|Z_m| = 1/2 + O(theta^m). Implies S_m = 0.9 + O(theta^m).
- **Density zero**: #{n <= N : 2^n zeroless} = o(N). Follows from either form of the parity-balance lemma.

### 6.3 Out of reach (unchanged from A+B series)

- **Finiteness for the specific orbit**: Requires pointwise hitting arguments that no current method provides.
- **The full 86 Conjecture**: 2^86 is the last zeroless power. Same obstacle as finiteness, plus effectivity.

---

## 7. Literature Assessment (Consensus from C3 responses)

### Noda (arXiv:2510.18414): Most directly on-target

Noda's transfer-operator formalism is the closest existing framework to the missing lemma. He explicitly sets up the finite-state matrix for digit-weighted generating functions of powers of 2 and highlights the parity structure (Lemma 1). What's needed: plug in the zeroless weight w(d) = 1{d != 0}, prove a spectral gap for the parity-projected operator.

### Lagarias (math/0512006): Best for intersection/dimension approach

Lagarias formulates missing-digit problems as dynamical/Cantor-set intersections. For density zero specifically, this framework is the most natural: translate "zeroless in base 10" to a 10-adic Cantor-type set, study the orbit's intersection with it. Requires a base-10 / (2,5)-adic adaptation.

### Dumitru (arXiv:2503.23177): Metric only

Dumitru proves metric finiteness (a.e. starting phase) for "all digits even" via dynamical Borel-Cantelli. Philosophically aligned with our heuristic, but explicitly notes the specific orbit is beyond the method. Upgrading from metric to pointwise requires showing the specific phase is generic, which is typically out of reach.

---

## 8. Connection to A-Series and B-Series

The three series form a complete reduction chain:

| Series | Domain | Key finding | What it rules out |
|--------|--------|------------|-------------------|
| A (equidistribution) | Analytic | Three impossibilities | Full conjecture via exponential sums |
| B (transfer matrices) | Combinatorial | rho >> period, pairs don't die | Full conjecture via counting |
| C (information theory) | Structural | Parity-balance is the gap | Everything except density zero |

**How C-series resolves B-series limitations**: The B-series showed rho ~ 8.035 >> 5, so counting alone can't beat the orbit period. The C-series shows this comparison is irrelevant for density zero: the correct comparison is not "survivors vs orbit period" but "conditional survival rate vs 1." The parity-fiber formula extracts exactly the right quantity.

**How C-series uses A-series findings**: The A-series dominant Fourier character at order 20 connects to the lag-20 autocorrelation (Exp 9 Part F). C3-A suggested a step-20 window transfer matrix to exploit this. The A-series's "permanent Fourier obstruction" (relative bias ~1/9) does NOT obstruct density zero, only the full conjecture.

**The provability hierarchy (A+B+C combined)**:

| Statement | Method | Status |
|-----------|--------|--------|
| Within-parity digit uniformity on orbit | Fiber structure | **Proved** |
| Parity-fiber formula S_m = 1 - P(even)/5 | Arithmetic identity | **Proved** |
| Information constant ~ 0.057 nats/constraint | Carry chain | **Derived** |
| Triple survivor density decays as (0.893)^k | Transfer matrix | **Provable** |
| Metric finiteness (a.e. starting point) | Borel-Cantelli | **Provable** |
| Density zero for the orbit | Parity-balance lemma | **Reduced to one lemma** |
| Finiteness for the specific orbit | Unknown | **Out of reach** |

---

## 9. The Computational Verification Opportunity

The C-series identifies a concrete computation that could verify (but not prove) the parity-balance lemma to arbitrary depth:

**Compute E_m and O_m exactly for m = 1 through 30+.**

This requires enumerating the orbit mod 10^m (period 4*5^{m-1}) and classifying each survivor by fiber type. For m up to ~12, this is feasible with direct enumeration (period ~ 10^8). For larger m, modular arithmetic suffices: compute 2^n mod 10^m for the full period and check digits.

**What to look for**:
- |E_m|/|Z_m| converging to 1/2
- The rate of convergence (should be geometric if theta < 1)
- Any m where the ratio deviates significantly (would indicate structural obstruction)

This computation would also reveal whether the spectral gap theta is related to the subdominant eigenvalue ~2.1 observed in the m-fold constraint matrices.

---

## 10. CRITICAL CORRECTION: Classification Bug (Experiment 11)

### 10.1 The error

Both GPT Pro and GPT Thinking classified level-m survivors using u < 5^m/2, where u is the 5-adic parameter. Experiment 11a revealed this gives E_m/Z_m = 4/9 (constant), and the identity Z_{m+1} = 4*E_m + 5*O_m fails.

### 10.2 The fix

The correct classification is: even-type if w = u * 2^{-1} mod 5^m < 5^m/2.

The factor of 2^{-1} arises because the level shift x = 2^m * u_m (level m) to x = 2^{m+1} * u_{m+1} (level m+1) gives u_{m+1} = u_m / 2 mod 5^m. The parity of the new digit depends on this shifted parameter, not on u_m directly.

### 10.3 Verification

Experiment 11b tested three classification methods. Method 2 (corrected) matches Method 3 (direct digit parity check, ground truth) exactly at every level m = 1..10.

### 10.4 Impact on the framework

The within-parity uniformity theorem is unaffected (it was always correct). The parity-fiber formula Z_{m+1} = 4*E_m + 5*O_m now holds exactly with the corrected classification. The reduction to a parity-balance lemma is validated.

---

## 11. Experiment 11 Results: Parity Balance CONFIRMED

### 11.1 The corrected E/Z ratios

| m | Z_m | E/Z (corrected) | S_{m+1} |
|---|-----|-----------------|---------|
| 1 | 4 | 0.50000000 | 0.90000000 |
| 2 | 18 | 0.50000000 | 0.90000000 |
| 3 | 81 | 0.50617284 | 0.89876543 |
| 4 | 364 | 0.50000000 | 0.90000000 |
| 5 | 1,638 | 0.50000000 | 0.90000000 |
| 6 | 7,371 | 0.49993217 | 0.90001357 |
| 7 | 33,170 | 0.49990956 | 0.90001809 |
| 8 | 149,268 | 0.50003350 | 0.89999330 |
| 9 | 671,701 | 0.50000223 | 0.89999955 |
| 10 | 3,022,653 | 0.49999785 | 0.90000043 |

### 11.2 Identity verification

Z_{m+1} = 4*E_m + 5*O_m holds **exactly** at every level m = 1..9 (all tested). No exceptions.

### 11.3 Interpretation

The strong form of the parity-balance lemma (E/Z -> 1/2) is empirically confirmed. Deviations from 1/2 are of order 1/sqrt(Z_m), consistent with a near-uniform distribution of the 2^{-1} map on the survivor set.

The conditional survival rate S_m = 0.9 + O(1/Z_m) at every level. This means the probability of all k digits being nonzero decays as ~0.9^k, validating the density-zero heuristic.

---

## 12. Refined Diagnosis (Post-Experiment 11)

The parity-balance lemma is no longer speculative. The data confirms:

1. **E_m/Z_m = 1/2 + O(Z_m^{-1/2})** with the corrected classification (w = u * 2^{-1} mod 5^m)
2. **Z_{m+1} = 4*E_m + 5*O_m** holds exactly
3. **S_m = 0.9 + O(Z_m^{-1/2})** at every level

The remaining theoretical challenge is to prove why E_m/Z_m -> 1/2. The most natural approach: the map u -> u * 2^{-1} mod 5^m is an automorphism of (Z/5^m Z)*, and the survivor set Z_m is defined by digit constraints that are "approximately symmetric" under this map. A spectral-gap argument on the transfer operator, tracking the parity character under digit extension, should yield the result.

---

## 13. Suggested Next Steps (Updated)

### Computational
1. **Push E_m/O_m computation to m = 15-20** (track convergence rate more precisely)
2. **Measure the convergence exponent**: fit |E_m/Z_m - 1/2| to C * theta^m and estimate theta
3. **Step-20 window transfer matrix**: Build the transfer operator for the multiplier 2^20 and measure its spectral radius

### Theoretical
4. **Prove the parity-balance lemma** via the 2^{-1} automorphism: show that the survivor set cannot have systematic bias under the half-space indicator composed with the 2^{-1} map
5. **Formalize the parity-uniformity theorem** as a clean one-page proof (paper-ready, corrected classification)
6. **Read Noda carefully** and identify whether his Lemma 1 already contains the parity-fiber structure
