# APPROACH 52C: Exact 9×9 Pair Matrix from Exp 82

## Context

Following APPROACH 52A and 52B, you offered to build the literal 18×18 transition matrix P if given the actual 9×9 pair counts from the experiments. Here is that data, computed from powers 2^50 through 2^499.

We're proving the Erdős 86 Conjecture: **2^86 is the last power of 2 with no zero digit.**

---

## The Data (Exp 82)

### Raw Counts (30,065 zeroless pairs from n = 50 to 499)

```
          1      2      3      4      5      6      7      8      9
  1 |   383    367    364    368    372    369    372    333    387
  2 |   417    379    385    366    393    356    369    394    370
  3 |   389    371    377    372    367    342    360    358    348
  4 |   378    397    364    392    325    388    360    372    372
  5 |   369    376    357    354    372    387    351    362    384
  6 |   388    364    355    355    412    382    400    376    367
  7 |   371    363    373    373    369    350    337    342    384
  8 |   343    401    354    378    362    388    383    384    378
  9 |   392    363    381    377    367    345    369    374    377
```

### 9×9 Transition Matrix Q[a][b] = P(next digit = b | current digit = a)

```python
Q = {
    1: [0.11554, 0.11071, 0.10980, 0.11101, 0.11222, 0.11131, 0.11222, 0.10045, 0.11674],
    2: [0.12161, 0.11053, 0.11228, 0.10674, 0.11461, 0.10382, 0.10761, 0.11490, 0.10790],
    3: [0.11845, 0.11297, 0.11480, 0.11328, 0.11175, 0.10414, 0.10962, 0.10901, 0.10597],
    4: [0.11290, 0.11858, 0.10872, 0.11708, 0.09707, 0.11589, 0.10753, 0.11111, 0.11111],
    5: [0.11141, 0.11353, 0.10779, 0.10688, 0.11232, 0.11685, 0.10598, 0.10930, 0.11594],
    6: [0.11415, 0.10709, 0.10444, 0.10444, 0.12121, 0.11239, 0.11768, 0.11062, 0.10797],
    7: [0.11373, 0.11128, 0.11435, 0.11435, 0.11312, 0.10730, 0.10331, 0.10484, 0.11772],
    8: [0.10175, 0.11896, 0.10501, 0.11213, 0.10739, 0.11510, 0.11362, 0.11391, 0.11213],
    9: [0.11719, 0.10852, 0.11390, 0.11271, 0.10972, 0.10314, 0.11031, 0.11181, 0.11271],
}
```

### Marginal Distribution π[d]

```python
pi = {
    1: 0.11026,
    2: 0.11405,
    3: 0.10923,
    4: 0.11136,
    5: 0.11016,
    6: 0.11306,
    7: 0.10850,
    8: 0.11212,
    9: 0.11126,
}
```

### High/Low Aggregated 2×2 Matrix

Aggregating low digits (1-4) and high digits (5-9):

```
P(L→L) = 0.4537    P(L→H) = 0.5463
P(H→L) = 0.4426    P(H→H) = 0.5574
```

This gives second eigenvalue λ₂ = P(L→L) + P(H→H) - 1 = 0.0111, indicating near-independence.

### Killing and Protecting Masses

**Killing pairs** (a, 5) with a ∈ {1,2,3,4}:
- Total killing mass: 0.0485
- Baseline (4/81): 0.0494
- Ratio: **0.981** (2% suppression)

**Protecting pairs** (a, 5) with a ∈ {5,6,7,8,9}:
- Total protecting mass: 0.0626
- Baseline (5/81): 0.0617
- Ratio: **1.014** (1.4% enhancement)

---

## Discrepancy to Investigate

APPROACH 52A estimated |λ₂| ≈ 0.227 based on carry-out fractions H₀ ≈ 0.46 and H₁ ≈ 0.313. But the empirical 2×2 aggregation gives |λ₂| = 0.0111, which is 20× smaller.

This suggests either:
1. The digit transitions in 2^n are much closer to uniform than the carry model predicts
2. The 2×2 aggregation loses information that exists in the full 9×9 structure
3. The carry model from 52A was miscalibrated

---

## What We Need

### Q1: Build the Full 18×18 Transition Matrix

Using the 9×9 matrix Q[a][b] above, construct the full 18-state Markov chain on (digit, carry) space.

The carry-out from digit a is deterministic: τ(a) = 0 if a ∈ {1,2,3,4}, τ(a) = 1 if a ∈ {5,6,7,8,9}.

So the transition from (a, c) to (a', c') should have:
- c' = τ(a) (deterministic)
- The probability comes from the empirical Q[a][a']

But wait: Q[a][b] gives the next digit given current digit, not accounting for carry state. To build the 18-state model, we need to decompose by carry. Can you do this from the 9×9 data alone, or do we need conditional counts Q[a][b | c]?

### Q2: Compute the True |λ₂|

From the full 18×18 matrix (or the 9×9 if that's sufficient), compute the second eigenvalue. Resolve the discrepancy between the predicted 0.227 and empirical 0.0111.

### Q3: Stationary Distribution π̃(d, c)

Compute the stationary distribution over the 18 states. This gives the effective zero rate:
- p₀ = π̃(5, 0)

### Q4: Spectral Radius for Survival

The "zeroless survival" transfer matrix is the 18×18 matrix with state (5, 0) removed (or its row/column zeroed). What is the spectral radius ρ of this survival matrix? The per-digit survival factor is ρ.

### Q5: Reconcile with 52A/B

The 52A/B responses estimated:
- p₀^eff ≈ 0.0385
- |λ₂| ≈ 0.227
- ρ ≈ 0.9602

Does the data-driven 18×18 model confirm or revise these estimates?

### Q6: What Missing Data Would Help?

If you need the conditional transition matrices Q[a][b | c=0] and Q[a][b | c=1] separately (instead of the marginal Q[a][b]), I can compute those. Let me know.

---

## Additional Context

### The Doubling Transducer (Recap)

Reading digits LSB-first, doubling works as:
- State = carry c ∈ {0, 1}
- Input digit a ∈ {1, ..., 9} (for zeroless)
- Output: b = (2a + c) mod 10
- Next carry: c' = ⌊(2a + c)/10⌋

Zero is produced only when (a, c) = (5, 0) gives output 0.

### What We Already Know

From Exp 62-71:
- Killing pairs (d, 5) with d ∈ {1,2,3,4} are suppressed ~22% vs uniform
- Protecting pairs (d, 5) with d ∈ {5,6,7,8,9} are enhanced ~8%
- The (4, 5) pair is most suppressed at 64% of expected
- All digit pairs are somewhat suppressed (0.6-0.96 of uniform)

The Exp 82 marginal data shows smaller effects because it averages over all positions, while the Exp 70 conditional data (specifically for killing/protecting contexts) shows larger effects.

---

## Summary

Please use the empirical 9×9 transition matrix to:
1. Build the explicit 18×18 (digit, carry) Markov chain
2. Compute exact stationary distribution and effective zero rate
3. Find the true |λ₂| and correlation length
4. Compute spectral radius for survival analysis
5. Reconcile with APPROACH 52A/B estimates
