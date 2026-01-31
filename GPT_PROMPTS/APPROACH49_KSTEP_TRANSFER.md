# APPROACH 49: k-Step Transfer Operator Analysis

## Context

We are seeking an **analytic proof** of the Erdős 86 Conjecture: 2^86 is the last power of 2 with no zero digit.

**Key insight from APPROACH 44B:** The k-step transfer operator T_k, encoding the constraint "(N, 2N, 4N, ..., 2^k N) are all zeroless," is the correct object for explaining why the sequence dies at n = 86.

**This prompt:** Develop the k-step transfer operator framework rigorously.

---

## The Single-Step Transfer Matrix (Review)

From APPROACH 44, the single-step transfer matrix T encodes: "given a zeroless number N, when is 2N also zeroless?"

The carry automaton has 2 states (carry ∈ {0, 1}) and transitions based on input digit d ∈ {1,...,9}:

```
Output digit = (2d + carry_in) mod 10
Carry_out = ⌊(2d + carry_in) / 10⌋
```

**Zero-creating event:** Output = 0, which happens iff 2d + carry_in = 10, i.e., (d, carry_in) = (5, 0).

**Transfer matrix T:** T[c', c] = # of digits d ∈ {1,...,9} such that:
- Output ≠ 0 (so not (d=5, c=0))
- Next carry = c'

From APPROACH 44A:
```
T = [4, 4]
    [4, 5]
```

Eigenvalues: (9 ± √65)/2 ≈ 8.531, 0.469
Spectral radius: ρ(T) ≈ 8.531

---

## The k-Step Transfer Operator

### Definition

For k ≥ 1, define T_k as the transfer operator for the constraint:
"N, 2N, 4N, ..., 2^k N are all zeroless"

The state space for T_k must track enough information to determine whether multiplying by 2 k times in succession produces any zeros.

### State Space for T_k

**Observation:** To determine if 2^j N has a zero (for j = 1, ..., k), we need to track:
1. The carry propagating through each multiplication
2. Whether any intermediate result had a zero

**Key insight:** The carry after multiplying by 2^j depends on the last j digits processed (because carries can propagate).

Actually, simpler: carries are binary, and each multiplication's carry depends only on the previous carry and the current digit.

**State for T_k:** A k-tuple (c_1, c_2, ..., c_k) ∈ {0, 1}^k, where c_j is the carry entering position i in the j-th multiplication.

Wait, this isn't quite right. Let me think more carefully.

### Simplified Model: Per-Digit Independence

For a single position (digit), the k-step evolution is:
- Start with digit d₀ and carry c₀
- After multiplication j: digit d_j = (2d_{j-1} + c_{j-1}) mod 10, carry c_j = ⌊(2d_{j-1} + c_{j-1})/10⌋

**But:** The carry c_j at position i depends on the digit at position i-1 after j-1 multiplications.

So the state at position i after k multiplications depends on a growing "cone" of initial digits.

### The Spacetime SFT Approach

Think of the doubling operation as a **cellular automaton** on digit sequences.

**State:** (digit, carry) pairs at each position
**Update:** Local rule based on (digit, carry_from_right)

The k-step operator asks: starting from a zeroless configuration, what configurations remain zeroless after k doublings?

This is a **subshift of finite type (SFT)** with forbidden patterns being those that produce a zero digit.

### Simplified Question

**Q:** What's the growth rate of m-digit zeroless numbers N such that 2N, 4N, ..., 2^k N are also zeroless?

Let S_k(m) = #{N ∈ [10^{m-1}, 10^m) : N, 2N, ..., 2^k N all zeroless}

Then S_k(m) ~ ρ(T_k)^m for some spectral radius ρ(T_k).

**Claim:** ρ(T_k) < ρ(T_1)^k for k ≥ 2, because the constraints interact.

---

## Questions

### Q1: Explicit computation of ρ(T_2)

For k = 2, compute the transfer matrix T_2 for "N, 2N, 4N all zeroless."

The state needs to track: after processing digits 1, ..., i of N, what is the carry state for multiplication by 2 AND multiplication by 4?

**State:** (c_1, c_2) ∈ {0, 1}² where:
- c_1 = carry entering position i+1 in the 2N computation
- c_2 = carry entering position i+1 in the 4N computation

**Transitions:** For input digit d ∈ {1,...,9} and state (c_1, c_2):
1. Compute d'_1 = (2d + c_1) mod 10, c'_1 = ⌊(2d + c_1)/10⌋
2. Compute d'_2 = (2d'_1 + c_2) mod 10, c'_2 = ⌊(2d'_1 + c_2)/10⌋
3. Accept iff d'_1 ≠ 0 AND d'_2 ≠ 0
4. New state: (c'_1, c'_2)

Build the 4×4 matrix T_2[(c'_1, c'_2), (c_1, c_2)] = # of valid digits d.

### Q2: Spectral radius of T_2

Compute the eigenvalues of T_2. Is ρ(T_2) < ρ(T_1)² = 8.531² ≈ 72.78?

If ρ(T_2) << ρ(T_1)², this shows the constraints compound non-trivially.

### Q3: Pattern for T_k

For general k:
- State space: {0, 1}^k (k-tuples of carries)
- Matrix size: 2^k × 2^k
- Entries: count of digits d ∈ {1,...,9} that produce valid (non-zero) outputs at all k levels

**Question:** Does ρ(T_k)^{1/k} decay as k increases?

### Q4: Limiting behavior

Define: λ_∞ = lim_{k→∞} ρ(T_k)^{1/k}

**Question:** Is λ_∞ < 9? If λ_∞ < 1, the language of "forever zeroless" strings is finite!

(But we know there are infinitely many n with 2^n zeroless, so λ_∞ ≥ 1 in some sense. The question is how to interpret this.)

### Q5: Connection to the orbit

The orbit {2^n} is a SPECIFIC sequence, not a random sample from the zeroless language.

**Key question:** How does the k-step spectral radius relate to the behavior of this specific orbit?

Possible connection: The orbit can stay zeroless only if it tracks the "k-step admissible" language. As k increases, this language shrinks, and tracking becomes harder.

### Q6: The "forbidden pattern" perspective

Instead of transfer matrices, think of forbidden patterns:
- 1-step forbidden: digit 5 at position with carry 0 (creates zero in 2N)
- 2-step forbidden: patterns that lead to the 1-step forbidden pattern after one doubling
- k-step forbidden: patterns that eventually lead to zeros within k doublings

**Question:** How does the set of k-step forbidden patterns grow with k?

### Q7: The "unprotected 5" chain

From APPROACH 46: The pattern "52, 53, 54, 51" (unprotected 5) creates a zero in the next doubling.

**2-step dangerous:** Patterns that create an unprotected 5 after one doubling.
**k-step dangerous:** Patterns that eventually create an unprotected 5.

**Question:** Can we characterize the k-step dangerous patterns inductively?

### Q8: Why does this explain 86?

If we can show:
1. The k-step admissible language shrinks exponentially with k
2. The orbit 2^n cannot stay in this shrinking language past some threshold

Then we have an "explanation" for why the sequence dies.

**Question:** Can this be made quantitative to predict/explain the threshold near n = 86?

### Q9: Numerical experiments

Compute:
1. ρ(T_1) ≈ 8.531 (known)
2. ρ(T_2) = ?
3. ρ(T_3) = ?
4. ρ(T_4) = ?
5. ρ(T_5) = ?

Plot ρ(T_k)^{1/k} vs k. Does it decay? To what limiting value?

### Q10: The "spacetime" SFT

Model the entire orbit as a 2D pattern:
- Horizontal axis: digit position (1, 2, 3, ...)
- Vertical axis: power of 2 (n = 0, 1, 2, ...)
- Entry at (i, n): the i-th digit of 2^n

This is a **spacetime** configuration. The doubling rule constrains adjacent rows.

**Question:** What's the entropy of this spacetime SFT? Does it relate to ρ(T_∞)?

---

## Desired Output

1. Explicit construction of T_2 (the 4×4 transfer matrix for 2-step zeroless)
2. Eigenvalues and spectral radius of T_2
3. If feasible, also T_3 and T_4
4. Analysis of whether ρ(T_k)^{1/k} decays as k → ∞
5. Assessment of whether the k-step framework can explain the n = 86 cutoff
6. Connection to the "unprotected 5" mechanism from APPROACH 46

---

## Computational Setup

```python
import numpy as np
from itertools import product

def build_T1():
    """Single-step transfer matrix."""
    T = np.zeros((2, 2))
    for c_in in [0, 1]:
        for d in range(1, 10):  # digits 1-9
            out = (2*d + c_in) % 10
            c_out = (2*d + c_in) // 10
            if out != 0:  # not zero-creating
                T[c_out, c_in] += 1
    return T

def build_T2():
    """Two-step transfer matrix."""
    # States: (c1, c2) where c1 = carry for ×2, c2 = carry for ×4
    T = np.zeros((4, 4))
    states = [(0,0), (0,1), (1,0), (1,1)]
    state_idx = {s: i for i, s in enumerate(states)}

    for (c1, c2) in states:
        for d in range(1, 10):
            # First doubling
            d1 = (2*d + c1) % 10
            c1_out = (2*d + c1) // 10
            if d1 == 0:
                continue  # zero created

            # Second doubling (of the first result)
            d2 = (2*d1 + c2) % 10
            c2_out = (2*d1 + c2) // 10
            if d2 == 0:
                continue  # zero created

            # Valid transition
            new_state = (c1_out, c2_out)
            T[state_idx[new_state], state_idx[(c1, c2)]] += 1

    return T
```
