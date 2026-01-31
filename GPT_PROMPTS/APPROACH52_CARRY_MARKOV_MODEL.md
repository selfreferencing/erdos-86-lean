# APPROACH 52: Carry Markov Model — From Experiments to Proof

## Context

You offered to translate our Exp 62-71 killing pair / protection data into an explicit 2-state carry Markov model (digit × carry) to estimate effective zero rate p₀ and correlation length. This is the bridge from computational experiments to proof strategy.

We're proving the Erdős 86 Conjecture: **2^86 is the last power of 2 with no zero digit.**

---

## Experimental Data (Exp 62-71)

### The Doubling Transducer

Reading digits LSB-first, the doubling map is:
- State = carry c ∈ {0, 1}
- Input digit a ∈ {0, ..., 9}
- Output: b = (2a + c) mod 10
- Next carry: c' = ⌊(2a + c)/10⌋

**Zero is produced when**: (a, c) ∈ {(5, 0), (0, 0)} → output 0

For zeroless inputs (a ∈ {1,...,9}): zero occurs only when **(a, c) = (5, 0)**.

### Killing Pairs (Exp 62, 66, 70)

A "killing pair" (d, 5) with d ∈ {1,2,3,4} at positions (i-1, i) means:
- Digit 5 at position i with carry-in 0
- This creates a zero on the next doubling

**Measured frequencies** (ratio vs uniform 1/81):

| Pair | Observed Ratio | Interpretation |
|------|----------------|----------------|
| (1, 5) | 0.82 | 18% suppressed |
| (2, 5) | 0.85 | 15% suppressed |
| (3, 5) | 0.80 | 20% suppressed |
| (4, 5) | **0.64** | 36% suppressed |
| All killing | 0.78 | 22% overall suppression |

### Protection Pairs (Exp 70)

A "protecting pair" (d, 5) with d ∈ {5,6,7,8,9} means:
- Digit 5 at position i with carry-in 1 (from d ≥ 5 at position i-1)
- This produces output 1, not 0

**Measured frequencies**:

| Pair | Observed Ratio |
|------|----------------|
| (5, 5) | 0.87 |
| (6, 5) | 0.92 |
| (7, 5) | 0.75 |
| (8, 5) | 0.91 |
| (9, 5) | 0.75 |

**Protection advantage**: 1.078× (protecting/killing ratio is 8% above random expectation of 5/4)

### Carry Cascade Effect (Exp 68-69)

The carry propagates correlations:
- Low digits (1-4) have carry-out 0
- High digits (5-9) have carry-out 1
- This biases adjacent digit pairs

**Key finding**: P(high digit follows low digit) ≈ 0.54 (vs theoretical 0.44 under independence)

The correlation structure is **short-range** but measurable.

### The (7, high) Suppression (Exp 67-69)

- (7, 7) pairs are only **27% of random** (ratio 0.71)
- (7, high) pairs generally 60-75% of expected
- Mechanism: 7 comes from d=3 (52.7%, carry-out 0) or d=8 (47.3%, carry-out 1)
- With carry-out 0, only 4/9 source digits produce high output

### Full Pair Matrix (Exp 70)

**ALL digit pairs are suppressed** compared to uniform (ratios 0.6-0.96).
The most suppressed:
- (9, 9): 60% of random
- (4, 5): 64% of random
- (7, 7): 71% of random

---

## What We Need

### Q1: The 2-State Markov Model

Please construct the explicit Markov chain on state space (digit, carry) = {1,...,9} × {0,1} (18 states for zeroless).

For each state (a, c), define:
- Transition probabilities to next states (a', c')
- Which transitions produce a zero output
- The stationary distribution (if it exists)

### Q2: Effective Zero Rate p₀

From the Markov model, compute:
- The stationary probability of being in a "zero-producing" configuration
- This gives the **effective zero rate p₀** per digit
- Compare to naive 1/10 = 0.1

### Q3: Correlation Length

The carry creates short-range dependence. Estimate:
- The mixing time / correlation decay rate
- How many positions until digits are "effectively independent"
- This determines when product approximations become valid

### Q4: Survival Probability

Using the Markov model, compute:
- P(k consecutive zeroless doublings) as function of k
- Compare to the transfer matrix spectral radius ρ ≈ 8.531 from APPROACH 50
- Identify the decay rate

### Q5: Bridge to Proof

How can this Markov model be used in the proof skeleton:
1. **Bulk zero forcing**: Can we prove zeros must appear in any long enough run?
2. **Borel-Cantelli**: Does the model give the quasi-independence needed?
3. **Sparse mesh**: Which positions should the mesh sample to maximize Baker's leverage?

---

## Additional Context

### The Transfer Matrix (from APPROACH 50)

The 2×2 transfer matrix for "protection counting":
```
A = [[4, 4],
     [4, 5]]
```
- Spectral radius ρ ≈ 8.531
- Per-digit survival factor ρ/9 ≈ 0.9479
- This gives P(m-digit run survives) ≈ 0.9479^m

### The Survival Statistics (Exp 71)

- P(survive step n | prev zeroless) ≈ 0.611 overall
- Random model: P(survive to 86) ≈ 6.85 × 10^{-28}
- Actual: survived → luck factor ≈ 1.46 × 10^{27}

The structural biases are real but insufficient alone to explain survival to n=86.

---

## Summary

We have rich experimental data on digit-pair frequencies, carry correlations, and killing/protecting pair suppression. Please formalize this as an 18-state Markov chain and extract:

1. Effective zero rate p₀
2. Correlation length
3. Survival decay rate
4. Implications for the proof strategy

This bridges Exp 62-71 to the bulk zero forcing argument in the proof skeleton.
