# APPROACH 25: The Forced-Zero Mechanism

## Context

We are investigating the Erdős 86 Conjecture: the last zeroless power of 2 is 2^86.

A key discovery has emerged from computational experiments. Define:
- **Entry witness**: Pattern "even digit followed by 1" (e.g., 21, 41, 61, 81)
- **Exit witness**: Pattern "5 followed by 1,2,3,4" (e.g., 51, 52, 53, 54)
- **E∩X cylinder**: A prefix containing both an entry and exit witness

The transfer matrix model for zeroless powers overcounts by ~3× because it treats E∩X states as reachable when they are not.

## The Universal Pattern

We computed floor(w/2) for every E∩X cylinder w at depths 3-9:

| Depth | E∩X Count | floor(w/2) has 0 | Blocked |
|-------|-----------|------------------|---------|
| 3 | 2 | 2 | 100% |
| 4 | 68 | 68 | 100% |
| 5 | 1,318 | 1,318 | 100% |
| 6 | 20,140 | 20,140 | 100% |
| 7 | 270,006 | 270,006 | 100% |
| 8 | 3,332,804 | 3,332,804 | 100% |
| 9 | 38,867,038 | 38,867,038 | 100% |

**100% of E∩X cylinders at depths 3-9 have floor(w/2) containing the digit 0.**

This is not sampling error. Every single one of the 42+ million E∩X cylinders checked follows the pattern.

## Why This Matters

If w is a cylinder and floor(w/2) contains 0, then w has no zeroless predecessor:
- To reach w by doubling, need N such that 2N starts with w
- N must be in [w/2, (w+1)/2)
- All such N have leading digits matching floor(w/2)
- If floor(w/2) contains 0, every predecessor contains 0
- Hence w is unreachable from the zeroless subshift

## The Core Question

**WHY does floor(w/2) always contain 0 when w is an E∩X cylinder with overlapping witnesses?**

The pattern must arise from the arithmetic interaction between:
1. Exit constraint: w starts with 5 followed by a small digit (1-4)
2. Entry constraint: somewhere in w, an even digit is followed by 1
3. Division by 2: how these constraints propagate through halving

## Specific Examples

**Depth 3:**
- w = 521: floor(521/2) = 260 (contains 0)
- w = 541: floor(541/2) = 270 (contains 0)

**Depth 4:**
- w = 5121: floor(5121/2) = 2560 (contains 0)
- w = 5141: floor(5141/2) = 2570 (contains 0)
- w = 5211: floor(5211/2) = 2605 (contains 0)
- w = 5212: floor(5212/2) = 2606 (contains 0)
- w = 5214: floor(5214/2) = 2607 (contains 0)
- w = 5218: floor(5218/2) = 2609 (contains 0)

The pattern: 52X/2 = 26Y and 54X/2 = 27Y, and these always produce a 0.

## Questions

**Q1: What is the algebraic mechanism?**

When w = 5d₁d₂...dₘ with d₁ ∈ {1,2,3,4} (exit witness at position 0), what forces floor(w/2) to contain 0?

Specifically:
- 52.../2 = 26... and the third digit computation?
- 54.../2 = 27... and the third digit computation?

**Q2: How does the entry witness interact?**

The entry witness (even followed by 1) must appear somewhere in w. How does this constraint combine with the exit constraint to force a 0 in floor(w/2)?

**Q3: Can you prove the lemma for small cases?**

Prove: For all 3-digit E∩X cylinders, floor(w/2) contains 0.

There are exactly 2 such cylinders: 521 and 541. But prove it from the constraints, not by enumeration.

**Q4: Can you prove the general case?**

Prove: For any E∩X cylinder w where the entry and exit witnesses overlap (gap < 4 positions), floor(w/2) contains the digit 0.

**Q5: What is the transition depth?**

At what depth can E∩X witnesses be separated enough that floor(w/2) need not contain 0? Our data suggests m ≥ 12. Can you derive this threshold?

## Hints

1. The exit witness forces w to start with 5X where X ∈ {1,2,3,4}.
2. Dividing 5X... by 2 gives 2Y... where Y depends on X and the carry.
3. The entry witness forces some position to have an even digit followed by 1.
4. When witnesses overlap, the constraints combine to force specific digit sequences.
5. The 0 appears because certain digit combinations under halving produce 0s.

## Desired Output

A rigorous proof explaining WHY the Forced-Zero Lemma holds, not just verifying that it does. The proof should:
1. Identify the exact algebraic mechanism
2. Show which digit positions are forced to be 0
3. Determine the minimum witness separation needed to avoid the forced 0
