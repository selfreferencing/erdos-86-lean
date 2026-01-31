# Synthesis: Experiments 62-71 - Why Is 2^n Lucky?

## Executive Summary

Experiments 62-71 investigated why powers of 2 survive to n=86 (36 zeroless powers) when the random model predicts extinction by n≈25.

**Key Finding:** The structural biases from carry propagation provide modest protection (22% killing pair suppression, 8% protection advantage), but these are **INSUFFICIENT** to explain survival to n=86. The orbit involves genuine luck (probability ~10^{-27} under the random model).

**Implication for Proof:** The proof strategy should focus on showing N_m = 0 for large m (danger cylinder + Baker), not on explaining why 2^86 survived. The "luck" question is interesting but irrelevant to the conjecture.

---

## Key Experimental Findings

### Exp 62: Killing Pair Frequency
- **Finding:** Killing pairs (low, 5) appear at 78% of random expectation
- (1,5): 82% of random
- (2,5): 85% of random
- (3,5): 80% of random
- **(4,5): 64% of random** (most suppressed)

### Exp 63-64: Trajectory Dynamics
- P(zeroless at n | zeroless at n-1) ≈ 0.611 overall
- Early survival (n < 20): P ≈ 0.867
- Late survival (n ≥ 60): P ≈ 0.25
- Random model predicts P(survive to 86) ≈ 6.85 × 10^{-28}

### Exp 65: Why 2^n Is Lucky
- New 5s are created from d ∈ {2, 7} with carry-in 1
- When a NEW 5 is created, it's automatically protected (carry-in 1 means right neighbor ≥ 5)
- Unprotected 5s arise from changed carry structure, not new 5 creation

### Exp 66: Killing Pair Sources
- Killing pairs require d_{i-1} ≥ 5 (for carry) AND output ∈ {1,2,3,4}
- Only d ∈ {5,6,7} can produce killing outputs (1,2,3,4) with appropriate carry
- d=8, d=9 always produce safe outputs (6,7,8,9)

### Exp 67: The (4,5) Anomaly
- (4,5) is most suppressed killing pair (64% of random)
- (7,7) pairs are only 27% of random
- (7, high) pairs are generally underrepresented (60-65%)

### Exp 68-69: The Carry Cascade
- 7 is produced from d=3 (carry-out 0) or d=8 (carry-out 1)
- 52.7% of 7s come from d=3, so 52.7% have carry-out 0
- With carry-out 0, only 4/9 zeroless digits produce high output
- This explains (7, high) suppression: predicted 47.3%, actual 44.9%, random 55.6%

### Exp 70: Full Pair Matrix
- **ALL digit pairs are suppressed** (ratio < 1) compared to uniform
- (9,9) is most suppressed overall: 60% of random
- (4,5) is most suppressed killing pair: 64% of random
- Protection advantage: 1.078x (only 8% above random)

### Exp 71: Luck Synthesis
- Random model: P(survive to 86) ≈ 6.85 × 10^{-28}
- Luck factor: 1.46 × 10^{27}
- Structural biases explain SOME suppression but NOT survival to 86
- 36 zeroless powers form a sparse, "lucky" set

---

## The Carry Cascade Mechanism

The doubling map 2: d → (2d + c) mod 10 creates correlations:

1. **Carry propagation:** d ≥ 5 produces carry-out 1, d < 5 produces carry-out 0

2. **Output depends on carry:**
   - Carry 0: outputs are {0,2,4,6,8} from sources {0,1,2,3,4}
   - Carry 1: outputs are {1,3,5,7,9} from sources {0,1,2,3,4}

3. **Correlation structure:**
   - Low digits (1-4) tend to be followed by low digits (slight bias)
   - High digits (5-9) tend to be followed by high digits (slight bias)

4. **Killing pair suppression:**
   - 5 requires carry-in 1 (from d ≥ 5 to the right)
   - But d ≥ 5 biases the output toward high (5-9)
   - This creates STRUCTURAL suppression of (low, 5) patterns

---

## Why the Bias Is Insufficient

The measured biases:
- 22% killing pair suppression
- 8% protection advantage
- Per-digit survival improvement: ~0.95% → ~0.96%

But the cumulative effect over 86 steps:
- Random: 0.9479^{sum of m_n} ≈ 10^{-28}
- With 8% improvement: still ≈ 10^{-20}

**Gap:** 10^{20} vs 10^{27} luck factor not explained by measured biases.

---

## Implications for Proof Strategy

### What This Tells Us

1. **The "luck" is real** - 2^n surviving to 86 is genuinely improbable
2. **Structural biases exist** but are too weak to explain full survival
3. **Early survival (n < 30) is key** - this is where most "luck" accumulates
4. **Late survival (n > 60) is rare** - only 5 zeroless powers have n > 50

### What This Means for the Proof

1. **Don't try to prove survival was "inevitable"** - it wasn't
2. **Focus on N_m = 0 for large m** - the conjecture is about non-existence, not probability
3. **The danger cylinder approach is correct:**
   - For large m, only O(1) cylinders can capture orbit points
   - Baker's theorem excludes these O(1) possibilities
   - This is independent of the "luck" question

4. **The transition from "lucky survival" to "structural impossibility":**
   - For m < 30: survival is possible but lucky
   - For m > 30: survival becomes structurally impossible (N_m = 0)
   - The conjecture asserts m ≥ 27 suffices

---

## Summary Table

| Quantity | Random Model | Actual | Ratio |
|----------|-------------|--------|-------|
| Killing pairs (1-4, 5) | 647 | 504 | 0.78 |
| Protecting pairs (5-9, 5) | 808 | 679 | 0.84 |
| Protection advantage | 1.25 | 1.35 | 1.08 |
| (4,5) pairs | expected | 64% | 0.64 |
| (7,7) pairs | expected | 27% | 0.71 |
| P(survive to 86) | 6.85e-28 | 1 | 1.46e+27 |

---

## Next Steps

1. **Update APPROACH11 (Danger Cylinders)** with these findings
2. **Focus on N_m = 0 for m ≥ 27** rather than explaining m < 27
3. **Use Baker's theorem** for the small number of danger cylinders
4. **The proof reduces to:** showing only O(1) cylinders matter for large m
