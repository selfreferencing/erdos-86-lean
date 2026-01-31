# APPROACH 26: Formalizing the Forced-Zero Lemma

## Context

We are proving the Erdős 86 Conjecture. A key lemma has emerged from computation that needs rigorous formalization.

## Definitions

Let w = d₁d₂...dₘ be an m-digit string with dᵢ ∈ {1,2,...,9} (zeroless).

**Definition (Entry Witness):** Position i is an entry witness if dᵢ ∈ {2,4,6,8} and dᵢ₊₁ = 1.

**Definition (Exit Witness):** Position i is an exit witness if dᵢ = 5 and dᵢ₊₁ ∈ {1,2,3,4}.

**Definition (E∩X Cylinder):** w is an E∩X cylinder if it contains both an entry witness and an exit witness.

**Definition (Witness Gap):** For an E∩X cylinder with entry witness at position i and exit witness at position j, the witness gap is |i - j|.

**Definition (Overlapping Witnesses):** Witnesses overlap if gap ≤ 3.

## The Conjecture to Prove

**Forced-Zero Lemma:** Let w be an E∩X cylinder with overlapping witnesses (gap ≤ 3). Then floor(w/2) contains the digit 0.

**Corollary (Arithmetic Unreachability):** Every E∩X cylinder with overlapping witnesses has no zeroless predecessor under doubling.

## Computational Evidence

| Depth | E∩X with gap ≤ 3 | floor(w/2) has 0 | Percentage |
|-------|------------------|------------------|------------|
| 3 | 2 | 2 | 100% |
| 4 | 68 | 68 | 100% |
| 5 | 1,318 | 1,318 | 100% |
| 6 | 20,140 | 20,140 | 100% |
| 7 | 270,006 | 270,006 | 100% |
| 8 | 3,332,804 | 3,332,804 | 100% |
| 9 | 38,867,038 | 38,867,038 | 100% |

Total: 42,491,376 cylinders checked, 100% satisfy the lemma.

## Structural Observations

**Observation 1:** At depth 3, the only E∩X cylinders are 521 and 541.
- 521: entry at position 1 (2→1), exit at position 0 (5→2). Gap = 1.
- 541: entry at position 1 (4→1), exit at position 0 (5→4). Gap = 1.

**Observation 2:** At depth 4, all 68 E∩X cylinders have gap ≤ 2.

**Observation 3:** Exit witness at position 0 forces w to start with 5X where X ∈ {1,2,3,4}.

**Observation 4:** When w starts with 52, floor(w/2) starts with 26. When w starts with 54, floor(w/2) starts with 27.

**Observation 5:** The entry witness (even followed by 1) creates constraints that, combined with the exit constraint, force specific digit patterns.

## Key Cases to Analyze

**Case A: Exit at position 0, Entry at position 1**
- w = 5, d₁, 1, d₃, ...
- Exit requires d₁ ∈ {1,2,3,4}
- Entry requires d₁ ∈ {2,4,6,8} and d₂ = 1
- Combined: d₁ ∈ {2,4}, d₂ = 1
- So w starts with 521 or 541
- floor(521/2) = 260, floor(541/2) = 270 (both contain 0)

**Case B: Exit at position 0, Entry at position 2**
- w = 5, d₁, d₂, 1, ...
- Exit requires d₁ ∈ {1,2,3,4}
- Entry requires d₂ ∈ {2,4,6,8} and d₃ = 1
- Multiple subcases depending on d₁, d₂

**Case C: Entry at position 0, Exit at position 1**
- w = d₀, 1, 5, d₃, ...
- Entry requires d₀ ∈ {2,4,6,8}
- Exit requires d₂ = 5 and d₃ ∈ {1,2,3,4}
- But wait: d₁ must be 1, so d₁ ≠ 5, so exit cannot be at position 1
- This case is impossible!

## Questions

**Q1: Complete Case Analysis**

Enumerate all possible configurations of overlapping entry and exit witnesses (gap ≤ 3) and prove floor(w/2) contains 0 in each case.

**Q2: Arithmetic of Halving**

For each case, trace through the digit-by-digit computation of w/2, identifying exactly which digit becomes 0.

**Q3: The Carry Propagation**

Division by 2 involves carries between digit positions. How do the entry/exit constraints interact with carry propagation to force a 0?

**Q4: Minimal Separation Theorem**

Prove: If the witness gap is ≥ k (for some threshold k), then floor(w/2) need not contain 0. Determine k.

**Q5: Paper-Ready Statement**

Write the lemma and its proof in a form suitable for a mathematics paper, with:
- Precise definitions
- Complete case analysis
- Clear logical structure
- No gaps in reasoning

## Proof Sketch to Develop

1. **Exit at position 0 forces w = 5Xabc... where X ∈ {1,2,3,4}**
   - floor(5Xabc.../2) = 2Y... where Y depends on X
   - 51.../2 = 25..., 52.../2 = 26..., 53.../2 = 26..., 54.../2 = 27...

2. **Entry witness nearby forces specific digit**
   - If entry at position 1: X ∈ {2,4} and next digit is 1
   - If entry at position 2: constraints on position 2

3. **Combined constraints force 0 in halved prefix**
   - Trace through arithmetic
   - Identify forced 0

4. **Generalize to gap ≤ 3**

## Desired Output

A complete, rigorous proof of the Forced-Zero Lemma suitable for inclusion in a mathematical paper, with all cases analyzed and no logical gaps.
