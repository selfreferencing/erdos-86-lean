# APPROACH 50: The Protected 5 Mechanism and Carry Cascade Failure

## Context

We are seeking an **analytic proof** of the Erdős 86 Conjecture: 2^86 is the last power of 2 with no zero digit.

**Critical discovery from computational experiments (Exp 57-59):**

ALL run terminations in the sequence of zeroless powers are caused by a SINGLE mechanism: the "unprotected 5."

---

## The Unprotected 5 Mechanism

### Definition

When doubling a number digit-by-digit (with carry propagation from right to left):

- **Output digit** = (2 × input_digit + carry_in) mod 10
- **Carry out** = ⌊(2 × input_digit + carry_in) / 10⌋

A **zero is created** when output = 0, which happens iff:
```
2 × d + c = 10
```

The only solution with d ∈ {1,...,9} and c ∈ {0,1} is: **(d, c) = (5, 0)**.

### Terminology

- **Unprotected 5:** A digit 5 with incoming carry = 0
- **Protected 5:** A digit 5 with incoming carry = 1 (produces 2×5+1 = 11, digit 1)

### Experimental Finding

**Every single run termination** in the 36 zeroless powers is caused by an unprotected 5:

| Run Terminator | 2^n value | Unprotected 5 positions |
|----------------|-----------|-------------------------|
| n = 9 | 512 | [2] |
| n = 16 | 65536 | [2] |
| n = 19 | 524288 | [5] |
| n = 25 | 33554432 | [4] |
| n = 28 | 268435456 | [3] |
| n = 37 | 137438953472 | [4] |
| n = 39 | 549755813888 | [11] |
| n = 49 | 562949953421312 | [7] |
| n = 51 | 2251799813685248 | [3, 13] |
| n = 67 | 147573952589676412928 | [13] |
| n = 72 | 4722366482869645213696 | [6] |
| n = 77 | 151115727451828646838272 | [13, 22] |
| n = 81 | 2417851639229258349412352 | [1, 19] |
| n = 86 | 77371252455336267181195264 | [3, 15, 19] |

**Trend:** Later terminators have more unprotected 5s (1 → 2 → 3).

---

## The n = 76 Anomaly

### Discovery

n = 76 is **unique** among late zeroless powers: it has **NO unprotected 5**.

```
2^76 = 75557863725914323419136
```

All digit-5s receive carry-in = 1:
- Position 12: 2×5 + 1 = 11 → digit 1, carry 1
- Position 19: 2×5 + 1 = 11 → digit 1, carry 1
- Position 20: 2×5 + 1 = 11 → digit 1, carry 1
- Position 21: 2×5 + 1 = 11 → digit 1, carry 1

### Why Does This Happen?

The 5s at positions 19, 20, 21 form a **consecutive block "555"**. Starting from position 18:
- The digit at position 18 creates carry-out = 1
- This carry protects the 5 at position 19: 2×5+1 = 11, carry-out = 1
- This protects position 20: 2×5+1 = 11, carry-out = 1
- This protects position 21: 2×5+1 = 11, carry-out = 1

**A carry cascade propagates through the consecutive 5s.**

### What Happens Next?

2^77 = 151115727451828646838272 is also zeroless, but NOW has unprotected 5s at positions 13 and 22.

The doubling operation:
1. Shifted all digits
2. Created new 5s at different positions
3. Broke the carry cascade alignment

2^78 = 302231454903657293676544 contains zeros.

---

## Questions

### Q1: Characterize "protected configurations"

A **protected configuration** is a digit pattern where every 5 receives carry-in = 1.

**Question:** What structural conditions on the digits guarantee protection?

Sufficient conditions for digit 5 at position i to be protected:
- The digit at position i-1 is ≥ 5, OR
- There's a carry cascade from position < i-1

**Formalize:** Given digits d_0, d_1, ..., d_{m-1} (LSB first), define:
```
c_0 = 0  (initial carry)
c_{i+1} = ⌊(2·d_i + c_i) / 10⌋
```

The configuration is protected iff: for all i with d_i = 5, we have c_i = 1.

### Q2: Probability of complete protection

For a "random" m-digit zeroless number:

**Question:** What is the probability that ALL 5s are protected?

Heuristic:
- Each 5 has probability ~1/2 of being protected (carry = 1 vs 0)
- Expected number of 5s: m/9
- Naive probability of complete protection: (1/2)^{m/9} = 2^{-m/9}

But carries are NOT independent. A carry cascade can protect multiple consecutive 5s.

**Question:** What's the true probability, accounting for carry correlations?

### Q3: The carry automaton perspective

Model the carry propagation as a **finite automaton** with states {0, 1} (carry value).

**Transition probabilities** (assuming uniform digits 1-9):
- From carry 0: P(next carry = 0) = 4/9 (digits 1,2,3,4), P(next carry = 1) = 5/9 (digits 5,6,7,8,9)
- From carry 1: P(next carry = 0) = 4/9 (digits 1,2,3,4), P(next carry = 1) = 5/9 (digits 5,6,7,8,9)

Wait, this is the same! The transition matrix is:
```
T = [4/9, 4/9]
    [5/9, 5/9]
```

This is rank 1. The stationary distribution is (4/9, 5/9).

**Implication:** In steady state, P(carry = 1) = 5/9 ≈ 0.556.

So each 5 has probability 5/9 of being protected.

**Question:** If there are k independent 5s, P(all protected) = (5/9)^k ≈ 0.556^k.

For 2^86 with 26 digits, expected 5s ≈ 26/9 ≈ 2.9. Actual: 3 unprotected 5s.

### Q4: Why isn't P(all protected) = (5/9)^{#5s} sufficient?

The problem: This gives P > 0 for any finite number of 5s.

But we need to explain why the sequence TERMINATES at n = 86.

**Key insight:** The digits of 2^n are NOT random. They are determined by the doubling dynamics.

**Question:** What constraints do the doubling dynamics impose beyond random?

### Q5: The orbit constraint

Let D_n = (d_0^{(n)}, d_1^{(n)}, ..., d_{m_n-1}^{(n)}) be the digits of 2^n.

The constraint is:
```
D_{n+1} = Doubling(D_n)
```

where Doubling is the digit-by-digit operation with carries.

**Question:** Does this constraint make protection LESS likely than the random model suggests?

Specifically: If 2^n is zeroless, what's P(2^{n+1} is zeroless | 2^n is zeroless)?

From our data, this probability is:
- High for small n (consecutive runs of length 10, 7, 4, ...)
- Low for large n (mostly isolated survivors)

### Q6: The "5-cascade stability" phenomenon

In 2^76, we have a block "555" at positions 19-20-21.

**Question:** How stable are such 5-cascades under doubling?

When we double:
- "555" with initial carry 1 becomes: 111 with all carries 1
- The NEW positions of 5s depend on the ENTIRE digit pattern

**Conjecture:** 5-cascades are UNSTABLE. A block of k consecutive 5s:
1. Becomes k consecutive 1s (if initially protected)
2. Creates new 5s at DIFFERENT positions
3. These new 5s may not be protected

**Question:** Can this instability be quantified? Does it explain why long protection eventually fails?

### Q7: Position-aware analysis

The position of a 5 within 2^n matters.

**Question:** Are 5s in certain positions more likely to be unprotected?

From Exp 59 data on unprotected 5 positions (as fraction of digit length):
- n=39: [0.92] (near LSB)
- n=49: [0.47] (middle)
- n=51: [0.19, 0.81] (both ends)
- n=67: [0.62] (middle)
- n=72: [0.27] (near MSB region)
- n=76: [] (none - anomaly)
- n=77: [0.54, 0.92] (middle + LSB)
- n=81: [0.04, 0.76] (MSB + middle)
- n=86: [0.12, 0.58, 0.73] (distributed)

**Observation:** Unprotected 5s appear throughout the digit range, not concentrated in any region.

### Q8: The MSB region

**Question:** Is the MSB (most significant bit) region special?

The leading digits of 2^n are determined by {n·θ} where θ = log₁₀(2).

For the leading few digits, the carry structure is DETERMINISTIC given the fractional part.

**Question:** Can Baker-type bounds on {n·θ} constrain the leading digit patterns and force unprotected 5s?

### Q9: A sufficient condition for termination

**Proposed Theorem:** There exists N₀ such that for all n ≥ N₀, 2^n contains an unprotected 5.

**Proof strategy:**
1. Show that the probability of complete protection decays as 2^{-cn} for some c > 0
2. Show that the orbit {2^n} cannot consistently beat these odds
3. Use the specific arithmetic of θ = log₁₀(2) to get the finite threshold

**Question:** Can this be made rigorous?

### Q10: The k-step connection

From APPROACH 49, the k-step transfer operator T_k has spectral radius ρ(T_k) that decays with k.

**Connection:** T_k counts digit patterns where k consecutive doublings produce no zeros.

**Question:** Does ρ(T_k) → 0 as k → ∞ correspond to "protection eventually fails"?

If ρ(T_k)^{1/k} → λ < 1, then:
- The number of n for which 2^n, 2^{n+1}, ..., 2^{n+k} are ALL zeroless decays as λ^n
- For large enough k, this forces the sequence to terminate

---

## Desired Output

1. Rigorous characterization of "protected configurations" for the doubling operation
2. Probability analysis of complete protection, accounting for carry correlations
3. Explanation of why the n = 76 carry cascade occurs and why it's unstable
4. Connection between protection probability decay and the k-step spectral radius
5. Assessment of whether this mechanism can yield a proof of finite termination
6. If possible, a prediction of the threshold N₀ from the analysis

---

## Computational Data Reference

**The 36 zeroless powers:**
n ∈ {0,1,2,3,4,5,6,7,8,9,13,14,15,16,18,19,24,25,27,28,31,32,33,34,35,36,37,39,49,51,67,72,76,77,81,86}

**14 consecutive runs with lengths:** [10, 4, 2, 2, 2, 7, 1, 1, 1, 1, 1, 2, 1, 1]

**The unique length-2 late run:** {76, 77}

**Key carry transition matrix:**
```
From carry c, digit d ∈ {1,...,9}:
- c' = 1 iff 2d + c ≥ 10
- c' = 1 iff d ≥ 5 - c/2
- For c=0: c'=1 when d ∈ {5,6,7,8,9} (5 of 9)
- For c=1: c'=1 when d ∈ {5,6,7,8,9} (5 of 9)
```

**Stationary carry distribution:** P(carry = 1) = 5/9 ≈ 0.556
