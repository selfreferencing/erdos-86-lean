# B-Series Synthesis: Triple Constraint and Transfer Matrices

## 8 Responses Processed (4 prompts x 2 models: GPT Pro "A" + GPT Thinking "B")

### January 27, 2026

---

## 1. The One-Sentence Verdict

The carry-based transfer matrix gives a clean, rigorous density-decay theorem for triple survivors, but the spectral radius (8.035 >> 5) is far too large to beat the orbit period by counting alone, and the pair-extinction stepping stone is provably false.

---

## 2. The Core Object: 4x4 Triple-Constraint Transfer Matrix

### 2.1 Setup

Track two carries at each digit position when computing x -> 2x -> 4x:
- c1: carry into current digit for x -> 2x
- c2: carry into current digit for 2x -> 4x

State space: (c1, c2) in {0,1}^2, ordered as (0,0), (0,1), (1,0), (1,1).

Given state (c1, c2) and input digit d in {1,...,9}:
1. First doubling: t1 = 2d + c1, y = t1 mod 10, c1' = floor(t1/10). Require y != 0.
2. Second doubling: t2 = 2y + c2, z = t2 mod 10, c2' = floor(t2/10). Require z != 0.

### 2.2 Forbidden digits

- c1 = 0: must avoid d = 5 (gives y = 0)
- c1 = 1, c2 = 0: must avoid d in {2, 7} (gives y = 5, then z = 0)
- c1 = 0, c2 = 0: only d = 5 forbidden (y is even when c1 = 0, so y != 5 automatically)
- c1 = 1, c2 = 1: no forbidden digits

### 2.3 The matrix (confirmed 6 times independently)

```
M = [[2, 2, 1, 1],
     [2, 2, 2, 3],
     [2, 2, 2, 2],
     [2, 2, 2, 3]]
```

Columns = source state, rows = destination state.

### 2.4 Spectral analysis

Characteristic polynomial: lambda(lambda^3 - 9*lambda^2 + 8*lambda - 2)

Eigenvalues:
- lambda_0 = 0
- lambda_1 = rho ~ 8.03538 (Perron-Frobenius eigenvalue)
- lambda_2, lambda_3: roots of remaining quadratic, |lambda| ~ 0.498

Spectral radius: rho ~ 8.03537823968, the largest real root of lambda^3 - 9*lambda^2 + 8*lambda - 2 = 0.

Verification: f(8) = 512 - 576 + 64 - 2 = -2 < 0, f(9) = 729 - 729 + 72 - 2 = 70 > 0.

### 2.5 Exact counts and recurrence

The number of k-digit zeroless x with both 2x and 4x zeroless mod 10^k:

| k | N_k | N_k / 9^k |
|---|-----|-----------|
| 1 | 8 | 0.8889 |
| 2 | 64 | 0.7901 |
| 3 | 514 | 0.7050 |
| 4 | 4130 | 0.6279 |
| 5 | 33186 | 0.5600 |
| 7 | 2,142,730 | 0.4480 |

Exact recurrence: N_{k+3} = 9*N_{k+2} - 8*N_{k+1} + 2*N_k, with N_1 = 8, N_2 = 64, N_3 = 514.

Asymptotic: N_k ~ C * rho^k with C ~ 0.9907.

### 2.6 The unconstrained baseline

Without zero-avoidance constraints, the transfer matrix has all column sums = 9, giving rho_full = 9. The constraint drops rho from 9 to 8.035, a per-digit survival ratio of rho/9 ~ 0.8928.

---

## 3. Comparison: Single vs Double Doubling

| Constraint | Matrix size | Spectral radius | Per-digit ratio | Char. polynomial |
|-----------|------------|----------------|----------------|-----------------|
| x, 2x zeroless | 2x2 | (9+sqrt(65))/2 ~ 8.531 | 0.9479 | lambda^2 - 9*lambda + 4 |
| x, 2x, 4x zeroless | 4x4 | ~8.035 | 0.8928 | lambda^3 - 9*lambda^2 + 8*lambda - 2 |

Each additional doubling constraint costs ~0.5 in spectral radius, or ~5.5 percentage points per digit.

The 2x2 matrix:
```
M_single = [[4, 4],
            [4, 5]]
```

Recurrence: a_{k+2} = 9*a_{k+1} - 4*a_k.

---

## 4. The Critical Correction: Pair Extinction Is False

### 4.1 The lifting lemma

Every pair-survivor at level k has at least 4 valid lifts to level k+1.

Proof: The orbit has period T_{k+1} = 5*T_k, giving exactly 5 lifts per residue. These 5 lifts correspond to digits d of a single parity class:
- Even parity: d in {0, 2, 4, 6, 8}. Lose at most d = 0 (zero digit). At least 4 survive.
- Odd parity: d in {1, 3, 5, 7, 9}. Lose at most d = 5 (if carry c = 0). At least 4 survive.

Since k=1 has pair-survivors (e.g., x = 2, 2x = 4), induction gives pair-survivors for all k.

### 4.2 Concrete examples

- k = 20: n = 610,351,888,025 gives a pair-survivor (both 2^n and 2^{n+1} have 20 nonzero trailing digits)
- Triple survivors exist along the orbit at k = 10 (n = 849,227) and k = 11 (n = 38,811,471)

### 4.3 Implications

- The pair branching factor (~4.27 observed, >= 4 proved) is too close to 5 for extinction
- Pairs are "too weak" as a stepping stone
- Triple branching is the first level where subcritical behavior *might* emerge
- But rho ~ 8.035 >> 5, so even triples can't win by counting alone

---

## 5. Why the Transfer Matrix Cannot Reach the Orbit

### 5.1 The counting gap

The transfer matrix proves: among all 9^k zeroless k-digit strings, triple survivors number ~8.035^k.

To beat the orbit by counting, we'd need 8.035^k < 4 * 5^{k-1} (the orbit period), i.e., rho < 5.

Since 8.035 >> 5, the survivor set is exponentially larger than the orbit, so a cardinality argument cannot force empty intersection.

### 5.2 The orbit is structured, not random

For n >= k, the residue 2^n mod 10^k lives in the coset {x : 2^k | x, 5 does not divide x}, which has size 4 * 5^{k-1}. This is a tiny, structured subset of all residues mod 10^k.

The bridge from "rare among digit strings" to "absent from the orbit" requires:
- Equidistribution of the orbit relative to digit-defined sets, OR
- A structural argument encoding the 2^k-divisibility constraint in base-10 digits (non-local, requires much larger state space)

### 5.3 The orbit-restricted automaton (open direction)

B3-B suggested: redo the automaton count restricted to the orbit's coset. If the effective spectral radius on that slice drops below 5, you'd have a counting argument. This is the natural next computation, but encoding "divisible by 2^k" in base-10 digits is non-local.

---

## 6. Rigorous Bounds (Theorem-Ready)

### 6.1 Single doubling

For x uniform in Z_k = {k-digit strings with all digits in {1,...,9}}:

Pr(2x zeroless) = (1^T * M_single^k * e_0) / 9^k <= (lambda_+/9)^k ~ (0.9479)^k

where lambda_+ = (9 + sqrt(65))/2 ~ 8.531.

### 6.2 Double doubling

Pr(2x and 4x zeroless) = (1^T * M^k * e_{00}) / 9^k <= (rho/9)^k ~ (0.8928)^k

The bound with C = 1 (i.e., N_k <= rho^k) is provable by induction from the recurrence.

A slightly looser all-k bound via Perron-Frobenius left eigenvector: N_k <= 1.14214 * rho^k.

---

## 7. Cross-Response Convergence

| Response | Focus | Key result | Agrees with all others? |
|----------|-------|-----------|------------------------|
| B1-B | Carry automaton | M, rho ~ 8.035, density decay | Yes |
| B2-A | Transfer matrix | M, rho, recurrence, M_full baseline | Yes |
| B2-B | Transfer matrix | M, rho, exact counts | Yes |
| B3-A | Probability bounds | Rigorous C*alpha^k, PF left eigenvector | Yes |
| B3-B | Probability bounds | C=1 inductive bound, orbit-restricted suggestion | Yes |
| B1-A | Carry rigidity | M, rho, k=10 and k=11 triple examples | Yes |
| B4-B | Pair stepping-stone | Lifting lemma: pairs never die | Yes |
| B4-A | Pair stepping-stone | k=20 example, pairs too weak | Yes |

**Convergence is total.** All 8 responses agree on the matrix, the spectral radius, and the limitation. Both B4 responses independently prove the same lifting lemma and correct the same false hypothesis.

---

## 8. Connection to A-Series

The A-series (equidistribution/exponential sums) and B-series (combinatorial/transfer matrices) hit the same wall from opposite sides:

| Direction | What works | Where it stops |
|-----------|-----------|---------------|
| A-series (analytic) | Complete period sums, Ramanujan structure | N ~ log(q) is too short for cancellation |
| B-series (combinatorial) | Transfer matrix, exact spectral radii | rho ~ 8.035 >> 5, counting can't beat period |

Both say: **density decay is provable, orbit-specific finiteness is not.**

The three impossibilities (from A-series) map directly onto B-series findings:
1. "Target can't be compressed" -> Transfer matrix has rho >> 5 (too many survivors)
2. "Orbit can't be averaged" -> Only ~3 samples per modulus (too few points)
3. "Dynamics can't be mixed" -> Equicontinuous rotation, no spectral gap

---

## 9. The Provability Hierarchy (A + B Combined)

| Statement | Method | Status |
|-----------|--------|--------|
| Triple survivor density decays as (0.893)^k | Transfer matrix | **Provable** |
| Pair survivor density decays as (0.948)^k | Transfer matrix | **Provable** |
| Metric finiteness (a.e. starting point) | Borel-Cantelli | **Provable** |
| Pair survivors exist at every k | Lifting lemma | **Proved (false extinction)** |
| Density zero for the orbit | Transfer matrix + log-depth | **Plausibly provable** |
| Finiteness for the specific orbit | Equidistribution in ultra-short regime | **Out of reach** |

---

## 10. Implications for Option E (Exponential Sum Computation)

The B-series tells us what to compute next:

1. **Orbit-restricted transfer matrix**: Build the automaton on the coset {x : 2^k | x, gcd(x,5) = 1} and measure the effective spectral radius. Does restriction to the orbit's slice change rho significantly?

2. **Triple lifting analysis**: Does the lifting lemma for triples give fewer than 5 lifts? If the triple branching factor drops below 5 at some level, that's a structural obstruction.

3. **Verify the large-k examples**: Confirm B1-A's triple survivors at k=10 (n=849,227) and k=11 (n=38,811,471), and B4-A's pair survivor at k=20 (n=610,351,888,025).

4. **The collapsed Fourier formula from A-series**: Compute the ~5*2^k contributing terms (those with 5^{k-1} | j) and see how the transfer matrix eigenstructure appears in the Fourier domain.

5. **Density-zero test**: Can the transfer matrix approach, combined with logarithmic digit-depth, yield #{n <= N : 2^n zeroless} = o(N)?
