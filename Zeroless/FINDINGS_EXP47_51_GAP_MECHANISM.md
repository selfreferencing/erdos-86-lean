# Findings: The 19-Digit Gap Mechanism (Exp 47-52)

## Executive Summary

The k=1 transfer matrix model predicts the last zeroless power of 2 occurs at m ≈ 46 digits. The empirical threshold is m = 27 (2^86). This 19-digit gap corresponds to a ~3× overcounting in the model.

Experiments 47-52 identified the gap's source: **arithmetic constraint, not probabilistic correction**.

**The key discovery (Exp 52):** E∩X cylinders (521, 541) have **zero predecessors** in the doubling graph. To reach 521, the predecessor must start with ~260, which contains a zero. The orbit's avoidance of E∩X is forced by arithmetic, not probability.

## The Model's Assumption vs Reality

### What the Model Assumes

The transfer matrix computes |E ∩ X| at depth m, where:
- E = entry set (prefixes with pattern "even digit followed by 1")
- X = exit set (prefixes with pattern "5 followed by 1,2,3,4")

The model treats E and X as **independent** over the space of all 9^m zeroless prefixes.

### What Actually Happens

1. **E and X are structurally incompatible at short range** (Exp 48)
2. **The orbit uses only O(1) cylinders per depth** (Exp 47, 51)
3. **Hit cylinders perfectly exclude E ∩ X** (Exp 51)
4. **When E ∩ X does occur (m > 10), witnesses are separated** (Exp 49, 50)

---

## Key Findings by Experiment

### Exp 47: Cylinder Deep Dive

**Finding: O(1) cylinders are hit at each depth**

| Depth | Total Zeroless | Hit | Fraction |
|-------|---------------|-----|----------|
| 2 | 81 | 27 | 33% |
| 3 | 729 | 29 | 4.0% |
| 4 | 6,561 | 26 | 0.4% |
| 5 | 59,049 | 25 | 0.04% |

The hit count is roughly constant (~25-29) while the total grows as 9^depth.

**Finding: Zero hit cylinders are in E ∩ X**

Of the 29 hit 3-digit cylinders, exactly 0 are in E ∩ X.

---

### Exp 48: E ∩ X Avoidance Analysis

**Finding: Only 2 three-digit cylinders can be in E ∩ X**

Structural analysis shows E ∩ X at depth 3 requires:
- Entry at position 1: B is even, C = 1
- Exit at position 0: A = 5, B ≤ 4

Combined: A = 5, B ∈ {2, 4}, C = 1

Only **521** and **541** satisfy both constraints.

**Finding: No power of 2 starts with 521 or 541**

Checked through n = 200. These cylinders are never visited by the orbit.

---

### Exp 49: Witness Position Analysis

**Finding: E ∩ X only appears in hits with m ≥ 12**

For smaller m, entry and exit witnesses cannot both fit without overlapping.

**Finding: When E ∩ X occurs, witnesses are separated**

| Metric | Value |
|--------|-------|
| Average gap (E to X position) | 4.43 |
| Hits with gap ≥ 2 | 86% |
| Hits with gap ≥ 3 | 57% |

**Finding: Entry clusters late, exit clusters early**

- Entry witnesses: average relative position 0.62 (toward end)
- Exit witnesses: average relative position 0.38 (toward start)

---

### Exp 50: Position-Aware Model

**Finding: Position separation gives ~1.6× correction**

| m | Naive E ∩ X | Gap ≥ 2 | Ratio |
|---|-------------|---------|-------|
| 4 | 68 | 32 | 2.12× |
| 5 | 1,318 | 832 | 1.58× |
| 6 | 20,140 | 14,312 | 1.41× |
| 7 | 270,006 | 204,504 | 1.32× |

The ratio decreases with m, suggesting asymptotic factor < 2×.

**Finding: This alone doesn't explain the ~3× gap**

Position separation contributes but isn't sufficient.

---

### Exp 51: Combined Gap Decomposition

**Finding: Perfect E ∩ X exclusion in hit cylinders**

| Depth | Hit Cylinders | In E ∩ X | Exclusion |
|-------|---------------|----------|-----------|
| 3 | 29 | 0 | 100% |
| 4 | 26 | 0 | 100% |

**Finding: Non-hit cylinders have HIGHER E ∩ X rate**

At depth 3:
- Hit cylinders: 0/29 = 0% in E ∩ X
- Non-hit cylinders: 2/700 = 0.29% in E ∩ X

The orbit selects exactly the cylinders that avoid E ∩ X.

**Finding: Cylinder reachability shrinks exponentially**

The O(1) constraint becomes tighter at larger depths:
- Depth 3: 25× reduction
- Depth 4: 250× reduction
- Depth 5: 2,360× reduction

---

## The Gap Mechanism

### What the Model Counts

```
|E ∩ X|_naive = P(E) × P(X) × 9^m

At m = 27: |E ∩ X|_naive ≈ 3.26 × 10^26
```

### What the Model Should Count

The model should only count E ∩ X prefixes that are **orbit-reachable**. These are:

1. In a cylinder that the doubling dynamics can reach
2. Have E and X witnesses that are sufficiently separated

### The Structural Constraint

The orbit's cylinder-selection mechanism **forces** avoidance of short-range E ∩ X:

- At depth ≤ 3: Hit cylinders are exactly those with E ∩ X = ∅
- At depth > 10: E ∩ X can occur, but only with separated witnesses

This isn't a probabilistic "1/3" factor. It's a **structural zero** at short depths that transitions to a separation constraint at longer depths.

---

## Quantitative Correction

### Decomposition Attempt

| Factor | Contribution | Source |
|--------|--------------|--------|
| Position separation | ~1.6× | Exp 50 |
| Cylinder reachability | 25× (at m=3) | Exp 51 |

But these aren't independent. The cylinder constraint **implies** E ∩ X exclusion.

### Better Interpretation

The correct interpretation is:

1. The orbit uses O(1) cylinders per depth
2. These cylinders are characterized by **avoiding E ∩ X at short range**
3. The ~3× gap is the ratio of:
   - Naive E ∩ X count (assuming all 9^m prefixes equally likely)
   - Orbit-constrained E ∩ X count (only reachable cylinders)

---

## Implications for the Transfer Matrix

### Current Model

The transfer matrix tracks states based on:
- Last few digits (for E and X pattern detection)
- Has E witness appeared?
- Has X witness appeared?

This assumes all zeroless prefixes are equally accessible.

### Needed Modification

A correct model would:

1. **Restrict to orbit-reachable cylinders**: Only O(1) per depth
2. **Track witness positions**: Require separation constraint
3. **Use constrained transition probabilities**: Not uniform over 9 digits

### Practical Challenge

The orbit-reachable cylinders aren't known analytically. They're determined by the full doubling dynamics, which couples all digit positions.

---

## Connection to Earlier Findings

### Exp 44: E = E' Perfect Match

The orbit perfectly matches existential entry (pattern-based) with deterministic entry (predecessor had zero). This suggested the orbit avoids states where the two conditions differ.

### Exp 45: π_E ≈ 0.5

The local inverse-branching analysis gave π_E ≈ 0.5, not 1/3. This is consistent with the new understanding: the ~3× gap isn't from local branching but from **global cylinder constraints**.

### Exp 46: 4% Cylinder Usage

First observation that only 4% of 3-digit cylinders are hit. Now explained as structural E ∩ X avoidance.

---

### Exp 52: Transition Graph Analysis

**Finding: E∩X cylinders have ZERO predecessors**

| Cylinder | Predecessors | Required N | Problem |
|----------|--------------|------------|---------|
| 521 | 0 | ~260.5 | 260 contains zero |
| 541 | 0 | ~270.5 | 270 contains zero |

To reach 521 by doubling, need N where 2N starts with 521. This requires N ≈ 260.5 × 10^k. But 260, 2605, 2606, ... all contain zeros.

**Finding: Transition graph structure**

- 729 zeroless 3-digit cylinders
- 929 transitions (average out-degree 1.27)
- 406 cylinders are reachable from the actual orbit
- All 29 hit cylinders are in the reachable set

**Finding: The arithmetic constraint**

The orbit's E∩X avoidance is **forced by arithmetic**:
- E∩X at depth 3 requires prefix 521 or 541
- These require predecessors containing 0
- Zeroless orbit cannot reach them

This transforms the explanation from "probabilistic ~1/3 factor" to "hard arithmetic constraint."

---

### Exp 53: Deep E∩X Reachability

**Finding: Arithmetic constraint extends to depths 4 and 5**

| Depth | E∩X Cylinders | Reachable | Blocked |
|-------|---------------|-----------|---------|
| 3 | 2 | 0 | 100% |
| 4 | 68 | 0 | 100% |
| 5 | 1,318 | 0 | 100% |

ALL E∩X cylinders at depths 3-5 require predecessors containing zero.

---

### Exp 54: GPT 22B Boundary Parity Test (REFUTED)

GPT 22B proposed: The boundary carry c_top = d_{m+1} mod 2 should be ~2:1 skewed on zeroless prefixes, giving the ~1/3 factor.

**Finding: Parity is ~50/50, not ~67/33**

| m | Even | Odd | Ratio | Minority |
|---|------|-----|-------|----------|
| 3 | 108 | 120 | 1.11:1 | 47.4% |
| 4 | 99 | 112 | 1.13:1 | 46.9% |
| 5 | 96 | 98 | 1.02:1 | 49.5% |
| 6 | 83 | 83 | 1.00:1 | 50.0% |

**Conclusion:** GPT 22B's parity mechanism does not explain the gap. The arithmetic constraint (Exp 52-53) remains the primary explanation.

---

### Exp 55-56: The Universal Forced-Zero Lemma

**Finding: 100% of E∩X cylinders have floor(w/2) containing 0**

| Depth | E∩X Count | floor(w/2) has 0 | Blocked |
|-------|-----------|------------------|---------|
| 3 | 2 | 2 | 100% |
| 4 | 68 | 68 | 100% |
| 5 | 1,318 | 1,318 | 100% |
| 6 | 20,140 | 20,140 | 100% |
| 7 | 270,006 | 270,006 | 100% |
| 8 | 3,332,804 | 3,332,804 | 100% |
| 9 | 38,867,038 | 38,867,038 | 100% |

This is a **universal pattern**: every E∩X cylinder at depths 3-9 is blocked.

**THE FORCED-ZERO LEMMA:**

> For any E∩X cylinder w (with overlapping entry and exit witnesses), floor(w/2) contains the digit 0.

**Corollary:** All E∩X cylinders are arithmetically unreachable from the zeroless subshift.

**Proof:**
1. To reach w by doubling, need N such that 2N starts with w
2. N must be in the interval [w/2, (w+1)/2)
3. All such N have leading digits matching floor(w/2)
4. Since floor(w/2) contains 0, N is not zeroless
5. Hence w has no zeroless predecessor

**Implication:** The transition depth (where E∩X hits first appear at m ≥ 12) occurs because:
- At m ≥ 12, E and X witnesses can be **separated** by 4+ positions
- Separated patterns don't force floor(w/2) to contain 0
- Only then does E∩X become arithmetically possible

---

## Open Questions

1. **What characterizes orbit-reachable cylinders?**
   - They avoid E ∩ X at short range
   - They follow Benford-like leading digit distribution
   - But what's the full characterization?

2. **How does this scale to m = 27?**
   - At m = 27, we can't enumerate all cylinders
   - Does the O(1) constraint persist?
   - What's the effective |E ∩ X| in reachable cylinders?

3. **Can we compute the constrained transfer matrix?**
   - Would need to track cylinder reachability
   - This couples all digit positions non-locally

4. **Why does the orbit avoid E ∩ X cylinders?**
   - Is there a carry-chain explanation?
   - Does doubling dynamics force certain digit correlations?

---

## Summary

The 19-digit gap comes from **structural exclusion**, not probabilistic correction:

- The orbit uses O(1) cylinders per depth
- These cylinders perfectly avoid E ∩ X patterns
- The naive model counts E ∩ X states that are structurally unreachable
- The ~3× overcounting is the ratio of naive to constrained counts

This shifts the question from "why is π_E ≈ 1/3?" to "why does the orbit select cylinders that avoid E ∩ X?"
