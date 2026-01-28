# A-Series Synthesis: Equidistribution and Exponential Sums

## 10 Responses Processed (5 prompts x 2 models: GPT Pro "A" + GPT Thinking "B")

### January 27, 2026

---

## 1. The One-Sentence Verdict

Every approach to proving the 86 Conjecture via equidistribution, exponential sums, discrepancy, or p-adic dynamics reduces to the same obstacle: **controlling a length-3 sum in a period-5^k cyclic group where the system has no mixing, the target set has non-decaying relative Fourier bias, and N ~ log(q) is astronomically below every known cancellation threshold.**

---

## 2. The Five Walls (One Per Prompt, Fully Confirmed by Both Models)

### Wall 1 (A1): The k^{1/3} vs k exponent gap
- **Known**: Korobov gives cancellation ~exp(-c * k^{1/3}) for sums Sum e(2^n / 5^k)
- **Needed**: exp(-0.105 * k) = (9/10)^k
- **Why it's structural**: The gap comes from N ~ log(q), not from a fixable constant. Korobov differencing uses the 5-adic valuation v_5(2^h - 1) ~ log_5(h), limiting it to k^{1/3}. Even with sum-product improvements (Bourgain-Chang), you need |H| >= q^delta, but N ~ log(q) << q^delta for any delta > 0.
- **Complete sums are trivial**: The Ramanujan sum c_{5^k}(1) = 0 for k >= 2. Perfect cancellation over full periods, but this doesn't bootstrap to incomplete sums.
- **Gauss sum completion fails**: Introduces factor 5^{k/2}, meaningful only when N ~ 5^{k/2}. Our N ~ k is exponentially below this.
- **Sieve approach re-encounters the same barrier**: Encoding digits as congruence exclusions still requires bounding exponential sums at the same frequencies.
- **References**: Korobov, Vandehey (arXiv:1606.07911), Bourgain-Chang composite modulus extensions

### Wall 2 (A2): The 1/k information-theoretic floor
- **With N ~ k sample points, discrepancy is at best ~ 1/k (polynomial)**
- **Needed: ~ e^{-0.105k} (exponential)**
- **This is not a Korobov limitation; it's a counting limitation.** Even perfect exponential sum bounds can't bridge polynomial to exponential through discrepancy with O(k) points.
- **Multidimensional discrepancy on the tower (5, 5^2, ..., 5^k) collapses to the top modulus**: the compatible projections don't create extra cancellation.
- **Metric lacunary results (Philipp LIL)**: D_N ~ sqrt(log log N / N) for a.e. alpha. Excellent, but metric: doesn't reach log_10(2) specifically.
- **Digit-block results (Fuchs)**: Control only O(log N) trailing digits; author explicitly states "a totally new method is needed" for more.
- **Martingale approach**: Filtration F_k = "info mod 5^k" gives a natural structure, but requires proving the orbit's conditional lift distribution is Haar-uniform. That's the full problem restated.
- **References**: Philipp (LIL for lacunary), Fuchs (digit blocks of exponential sequences), Kurzweil (shrinking targets)

### Wall 3 (A3): The permanent Fourier obstruction
- **Max |hat{1_Z}(j)| / hat{1_Z}(0) ~ 1/9, NOT DECAYING with k**
- **Actually GROWING**: 0.110 (k=2), 0.121 (k=3), 0.123 (k=4)
- **The maximizer is j = 5^{k-2}**, corresponding to the character e(-n/20) of order 20
- **This is a fixed low-conductor character** living on the quotient G_k -> G_2. The bias is already fully visible at level k=2 and persists upward.
- **Digit constraints are independent additively (product over digit positions) but NOT multiplicatively**: the "shadow" on low-level quotients produces non-decaying relative Fourier coefficients.
- **The lifting/induction structure**: Low-level characters see the weighted child-count c_k(u). Since c_k(u) is not constant (it's 4 or 5), low-level correlations persist. High-conductor characters get extra cancellation from the size-5 fiber sum, but the dominant spectrum IS low-conductor.
- **Computed data**: Full Fourier coefficients for k=1..4 saved to data/fourier_Zk_k1_4.csv
- **References**: Ramanujan sums (Wikipedia), Gauss sum theory (Bristol lecture notes)

### Wall 4 (A4): Ultra-short phase-specific hitting
- **The problem is NOT equidistribution. It's pointwise hitting in a non-mixing system.**
- **At length L=3, the trivial bound |S| <= 3 is already best-possible.** No cancellation method can improve on it. Character sum methods are conceptually mismatched.
- **The Fourier expansion of the 3-term window** shows you need either tiny coefficients across all dangerous j (contradicted by Wall 3) or systematic cancellation in the geometric factor (1 + e(j/T_k) + e(2j/T_k)) for the same j that carry mass (no mechanism for this).
- **Positive correlation is unbounded**: The pair-correlation transfer matrix M = [[4,4],[4,5]] has spectral radius (9+sqrt(65))/2 ~ 8.53. This IS the conditioned spectral radius from Exp 1. The correlation ratio grows exponentially in k.
- **Three recent references directly on our doorstep**:
  - Lagarias: ternary digits of 2^n, dynamical framework, exceptional sets are small, specific orbit still open
  - Dumitru (2025): metric finiteness for "all digits even" via dynamical Borel-Cantelli, explicitly notes specific orbit beyond method
  - Noda (2025): transfer-operator for digit-weighted generating functions of powers of 2
- **Density zero is a realistic intermediate target**: Show #{n <= N : 2^n zeroless} = o(N). Suffices to control "last m digits zeroless" with m = c*log(N) growing slowly. Transfer-matrix methods are applicable here.
- **References**: Lagarias (math/0512006), Dumitru (arXiv:2503.23177), Noda (arXiv:2510.18414)

### Wall 5 (A5): Isometric dynamics has no decorrelation
- **The system is a translation T(x) = 2x on Z_5*, which is uniquely ergodic, equicontinuous, purely discrete spectrum, no mixing.**
- **Dense orbit + measure zero does NOT force eventual exit.** This is a shrinking target problem, not a Birkhoff ergodic theorem application.
- **Mean return time to Z_k is (10/9)^{k-1}** by Kac's lemma. Exponentially long on average, but "on average" doesn't control the specific 3-term window.
- **Metric Borel-Cantelli works**: sum of mu(Z_k(n)) converges, so for a.e. starting point only finitely many hits. But this doesn't reach the specific orbit starting at 1.
- **5-adic logarithm linearizes the orbit but not the target**: Z_k in log-coordinates is a complicated union of congruence classes with no p-adic ball structure. The CRT lift (5-adic to 10-adic) destroys geometric simplicity.
- **For p-adic Diophantine approximation to help, you'd need a compressed description of Z_k** avoiding the "exponentially many cylinders" bookkeeping. No such compression exists (this IS the "no compression" axis of the unified obstruction).
- **Three equivalent sufficient conditions**: (A) quasi-independence for Z_k ∩ 2^{-m}Z_k, (B) effective equidistribution with error o(1) for k ~ 0.3N, (C) Fourier decay of 1_{Z_k} on relevant characters. All three are the same obstacle restated.
- **References**: Haydn-Nicol-Persson-Vaienti (mixing => Borel-Cantelli), Kurzweil (shrinking targets on rotations)

---

## 3. Cross-Response Convergence

All 10 responses independently arrive at the same wall from different mathematical directions:

| Response | Approach | Names the wall as | Distinctive contribution |
|----------|----------|-------------------|------------------------|
| A1-B | Exponential sums | 5-adic valuation bottleneck | v_5(2^h-1) ~ log_5(h) limits differencing to k^{1/3} |
| A1-A | Exponential sums | N ~ log q vs q^delta | Gauss sum completion analysis, sieve dead-end |
| A2-B | Discrepancy | Set complexity formally vacuous | Discrepancy tools produce nothing in this regime |
| A2-A | Discrepancy | 1/k vs e^{-ck} information floor | Digit-block literature (Fuchs), martingale connection |
| A3-B | Character sums | Fourier obstruction at 1/9 | Max at j=5^{k-2}, order-20 characters |
| A3-A | Character sums | Relative bias GROWS with k | Computed coefficients k=1..4, CRT map explicit |
| A4-B | Short sums | Length-3 sums trivially bounded | Three weaker provable results identified |
| A4-A | Short sums | Ultra-short phase-specific hitting | Transfer matrix unifies Exp 1+3, three 2025 refs |
| A5-B | p-adic dynamics | Isometric, no spectral gap | Shrinking target reformulation |
| A5-A | p-adic dynamics | Rotation has no decorrelation | Mean return time, intersection = correlation |

**The convergence is total.** Not a single response found a gap, a workaround, or an unconsidered tool. Every mathematical framework examined either (a) explicitly fails in the ultra-short regime, or (b) reduces to the same exponential sum barrier.

---

## 4. Key Mathematical Objects Identified

### 4.1 The Ramanujan sum c_{5^k}(j)
- Complete period sum Sum_{n=0}^{T_k-1} e(j * 2^n / 5^k) = c_{5^k}(j)
- For v_5(j) <= k-2: c_{5^k}(j) = 0 (perfect cancellation)
- For v_5(j) = k-1: c_{5^k}(j) = -5^{k-1}
- For v_5(j) >= k: c_{5^k}(j) = 4 * 5^{k-1} = phi(5^k)
- Implication: The Fourier counting formula collapses from 10^k terms to only 5 * 2^k terms (those j divisible by 5^{k-1})

### 4.2 The pair-correlation transfer matrix
- M = [[4,4],[4,5]], spectral radius (9+sqrt(65))/2 ~ 8.531
- This is BOTH the conditioned spectral radius from Exp 1 AND the pair-correlation growth rate from Exp 3
- The growing correlation ratio ~ (8.531/8.1)^k ~ 1.053^k explains the observed 1.00, 1.05, ..., 1.43 progression

### 4.3 The dominant Fourier character
- Maximizer at j = 5^{k-2}, corresponding to e(-n/20), a character of order 20
- Lives on the quotient G_k -> G_2 (conductor 25)
- Relative magnitude: ~1/9, growing slightly with k (0.110, 0.121, 0.123)
- This is the "permanent obstruction": a fixed low-level bias that doesn't wash out

### 4.4 The CRT bridge map
- r(u) = 2^k * (2^{-k} mod 5^k) * u mod 10^k
- Converts 5-adic unit u to the 10-adic residue with all digits visible
- The "additive-multiplicative misalignment": digit constraints are additive (base 10), the group is multiplicative (mod 5^k), and this map is the non-trivial bridge

---

## 5. What Is Provable vs What Is Not

### 5.1 Currently provable (or nearly so)
- Complete period sums: exact evaluation via Ramanujan sums
- Transfer matrix eigenstructure: finite computation, fully explicit
- Fourier coefficients of Z_k: computable for any k (product formula over digits)
- Metric finiteness: for a.e. starting point, only finitely many zeroless (follows from convergent Borel-Cantelli)
- Correlation structure: pair/triple correlations governed by finite transfer matrix

### 5.2 Plausibly provable with current tools
- **Density zero**: #{n <= N : 2^n zeroless} = o(N), via logarithmic digit-depth control
- **Quantitative upper bounds**: #{n <= N : zeroless} << N^{1-delta} for some delta > 0
- **Metric finiteness with quantitative bounds**: for a.e. phase, at most f(epsilon) exceptions

### 5.3 Out of reach with known tools
- **Finiteness for the specific orbit**: requires N ~ log(q) cancellation, which no method provides
- **Exponential sum bound exp(-ck)**: the k^{1/3} barrier is structural, not a constant-factor miss
- **Pointwise shrinking target for this rotation**: requires decorrelation that equicontinuous systems don't have

---

## 6. The Most Important References (From A-Series)

### Directly on our problem's doorstep
1. **Lagarias** (math/0512006): Ternary digits of 2^n. Dynamical framework, exceptional sets small, specific orbit open.
2. **Dumitru (2025)** (arXiv:2503.23177): Metric finiteness for "all digits even" constraint. Closest published result to what we want. Explicitly notes specific orbit beyond method.
3. **Noda (2025)** (arXiv:2510.18414): Transfer-operator for digit-weighted functions of powers of 2.

### For the exponential sum barrier
4. **Vandehey** (arXiv:1606.07911): Modern Korobov bounds, explicit discussion of when nontriviality starts.
5. **Bourgain-Chang**: Sum-product extensions to composite moduli. Need |H| >= q^delta.
6. **Fuchs** (web.math.nccu.edu.tw): Digit blocks of exponential sequences, O(log N) digits, "totally new method needed."

### For the dynamical framework
7. **Haydn-Nicol-Persson-Vaienti** (USC): Mixing => Borel-Cantelli paradigm (which our system lacks).
8. **Kurzweil / Kim (arXiv:2307.10122)**: Shrinking targets for rotations.
9. **Philipp / Aistleitner-Fukuyama**: Lacunary discrepancy LIL (metric, not effective for specific alpha).

---

## 7. Refined Diagnosis: Where the Breakthrough Must Come

The A-series confirms and sharpens the synthesis's diagnosis. The problem sits at the intersection of three impossibilities:

1. **The target set Z_k cannot be compressed** (exponentially many cylinders, non-decaying Fourier bias on low-conductor characters)
2. **The orbit cannot be averaged** (only ~3 samples per digit count, N ~ log q << q^delta)
3. **The dynamics cannot be mixed** (equicontinuous rotation, purely discrete spectrum, no spectral gap)

Any proof must violate at least one of these apparent impossibilities. The A-series responses collectively suggest:

- **Most realistic near-term target**: Density zero, via transfer-matrix methods applied to logarithmic digit depth
- **Most likely breakthrough mechanism**: A "compressed description" of Z_k that doesn't require exponentially many terms (something exploiting the product structure of the digit constraint that the current Fourier analysis misses)
- **Crisp slogan (from A4-A)**: "The bottleneck is not equidistribution; it's ultra-short, phase-specific hitting in a non-mixing system."

---

## 8. Implications for Option E (Direct Exponential Sum Computation)

The A-series tells us exactly what to compute:

1. **The collapsed counting formula**: Only 5 * 2^k Fourier terms contribute (those with 5^{k-1} | j), thanks to the Ramanujan sum structure. Compute these explicitly.
2. **The dominant character contribution**: Isolate the j = 5^{k-2} term and compute its contribution to the zeroless count vs the actual count. How much of the "error" is carried by this single character?
3. **The 3-term window Fourier decomposition**: For specific n near 86-87, decompose which Fourier terms are responsible for the transition from zeroless to non-zeroless.
4. **Recursive structure**: How do Fourier quantities at level k relate to level k-1? Is there a clean transfer relation?
5. **The density-zero test**: Can we verify computationally that the logarithmic digit-depth approach gives a bound?
