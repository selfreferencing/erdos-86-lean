# GPT Prompt: Experimental Refutation of 22A/22B Mechanisms (APPROACH 24)

## Summary

We tested both mechanisms you proposed in 22A and 22B. **Neither explains the gap.**

The gap is explained by **arithmetic unreachability**, not probabilistic branch weighting.

## What You Proposed

### 22A: Shift/Normalization Branch (~30%)
- The "shift branch" (mantissa × 5) occurs with probability log₁₀(2) ≈ 0.301
- The "witness branch" (where predecessor has zero) is tied to the shift branch
- This should give π_E^orbit ≈ 0.30-0.33

### 22B: Boundary Parity (~33%)
- The boundary carry c_top = d_{m+1} mod 2
- Conditioning on zeroless prefixes should bias this parity ~2:1
- The minority parity (~33%) should correlate with zero-predecessor

## What We Found

### Exp 54: Boundary Parity is NOT Skewed

We tested 22B's specific claim across 300 powers of 2:

| m | Even d_{m+1} | Odd d_{m+1} | Ratio | Minority |
|---|--------------|-------------|-------|----------|
| 3 | 108 | 120 | 1.11:1 | 47.4% |
| 4 | 99 | 112 | 1.13:1 | 46.9% |
| 5 | 96 | 98 | 1.02:1 | 49.5% |
| 6 | 83 | 83 | **1.00:1** | **50.0%** |
| 7 | 74 | 77 | 1.04:1 | 49.0% |

**The parity distribution is ~50/50, not ~67/33.**

22B's mechanism requires a ~2:1 skew. We see essentially uniform parity.

### Additional Findings from Exp 54

- **Parity vs predecessor-zero**: No correlation. P(pred zero | even) ≈ P(pred zero | odd) ≈ 17-22%
- **Entry witness vs parity**: No consistent correlation across depths

## The Actual Explanation: Arithmetic Unreachability

### Exp 52: E∩X Cylinders Have Zero Predecessors

The only E∩X 3-digit cylinders are 521 and 541. **Both have zero predecessors in the doubling graph.**

| Cylinder | Required Predecessor | Problem |
|----------|---------------------|---------|
| 521 | ~260.5 × 10^k | 260, 2605, 2606, ... all contain 0 |
| 541 | ~270.5 × 10^k | 270, 2705, 2706, ... all contain 0 |

**No zeroless number, when doubled, produces a number starting with 521 or 541.**

### Exp 53: This Extends to Depths 4 and 5

| Depth | E∩X Cylinders | Reachable | Blocked |
|-------|---------------|-----------|---------|
| 3 | 2 | 0 | 100% |
| 4 | 68 | 0 | 100% |
| 5 | 1,318 | 0 | 100% |

**ALL E∩X cylinders at depths 3-5 are arithmetically unreachable.**

Every single one requires a predecessor containing zero.

## Why This Changes the Picture

### Your Mechanism (Probabilistic)
- Branch weighting gives π_E ≈ 0.33
- The orbit "selects" certain branches
- A ~3× probabilistic correction

### Our Finding (Arithmetic)
- E∩X at short depths is **impossible**, not improbable
- The model counts states that are **structurally unreachable**
- There's no "probability 1/3" - it's probability **zero** at short depths

### The Two Regimes

**Short depths (m ≤ 5):**
- E and X witnesses must overlap spatially
- Overlapping patterns force prefixes like 521, 541
- These require predecessors with zeros
- **|E∩X|_actual = 0** (arithmetic block)

**Longer depths (m ≥ 12):**
- E and X witnesses CAN be separated by 4+ positions
- Separated patterns don't force zero-containing predecessors
- |E∩X|_actual > 0, but only for separated configurations
- Position separation gives ~1.6× correction (Exp 50)

## The Refined Question

Given that the gap is arithmetic, not probabilistic:

### Q1: Can we prove E∩X unreachability generalizes?

At depths 3-5, 100% of E∩X cylinders are blocked. Does this extend to all depths where witnesses overlap?

### Q2: What characterizes the transition depth?

E∩X first appears in actual hits at m ≥ 12. What allows E∩X to become arithmetically possible?

### Q3: Can this lead to a proof?

If we can prove:
1. Short-range E∩X (overlapping witnesses) is always arithmetically blocked
2. Long-range E∩X (separated witnesses) has density << independence prediction
3. Combined: |E∩X|_actual << |E∩X|_naive by factor ~3×

Then we've explained the gap rigorously.

### Q4: What's the correct transfer matrix?

The naive transfer matrix assumes all 9^m prefixes are equally accessible. A corrected matrix would:
- Restrict to arithmetically reachable cylinders (O(1) per depth)
- Enforce witness separation constraints
- Use transition probabilities from the doubling graph

## Data Summary

| Finding | Value | Exp |
|---------|-------|-----|
| Boundary parity skew | **1:1** (not 2:1) | 54 |
| E∩X at depth 3 | 0/2 reachable | 52 |
| E∩X at depth 4 | 0/68 reachable | 53 |
| E∩X at depth 5 | 0/1318 reachable | 53 |
| Hit cylinders at depth 3 | 29/729 = 4% | 47 |
| Reachable cylinders | 406/729 = 56% | 52 |
| Position separation factor | ~1.6× at m=7 | 50 |

## Conclusion

The ~3× gap is not from probabilistic branch weighting. It's from **arithmetic constraint**:

1. The model counts E∩X states that are structurally unreachable
2. At short depths, E∩X requires prefixes whose predecessors contain zeros
3. The zeroless orbit cannot reach these prefixes
4. At longer depths, E∩X requires spatial separation of witnesses

The question is no longer "why is π_E ≈ 1/3?" but "can we rigorously prove the arithmetic unreachability of short-range E∩X patterns?"
