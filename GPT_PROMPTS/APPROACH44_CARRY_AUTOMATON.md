# APPROACH 44: Carry Automaton Dynamics

## Context

We are seeking an **analytic proof** of the Erdős 86 Conjecture: 2^86 is the last power of 2 with no zero digit.

**Status:** A computational proof is complete. The question is "why is it true?"

**Key insight:** Multiplication by 2 in base 10 is realized by a finite-state automaton that processes digits and propagates carries. This automaton structure might explain why zeroless powers become impossible.

---

## The Carry Automaton

### Definition
When computing 2·N in base 10, we process digits right-to-left:
- Input: digit d_i of N, carry c_i ∈ {0, 1}
- Output: digit e_i = (2·d_i + c_i) mod 10
- Next carry: c_{i+1} = ⌊(2·d_i + c_i)/10⌋

The automaton has:
- **States:** {0, 1} (the carry values)
- **Input alphabet:** {0, 1, ..., 9} (digits)
- **Transition function:** δ(c, d) = (output_digit, next_carry)

### Transition Table
| c | d | 2d+c | output | next c |
|---|---|------|--------|--------|
| 0 | 0 | 0 | 0 | 0 |
| 0 | 1 | 2 | 2 | 0 |
| 0 | 2 | 4 | 4 | 0 |
| 0 | 3 | 6 | 6 | 0 |
| 0 | 4 | 8 | 8 | 0 |
| 0 | 5 | 10 | 0 | 1 |
| 0 | 6 | 12 | 2 | 1 |
| 0 | 7 | 14 | 4 | 1 |
| 0 | 8 | 16 | 6 | 1 |
| 0 | 9 | 18 | 8 | 1 |
| 1 | 0 | 1 | 1 | 0 |
| 1 | 1 | 3 | 3 | 0 |
| 1 | 2 | 5 | 5 | 0 |
| 1 | 3 | 7 | 7 | 0 |
| 1 | 4 | 9 | 9 | 0 |
| 1 | 5 | 11 | 1 | 1 |
| 1 | 6 | 13 | 3 | 1 |
| 1 | 7 | 15 | 5 | 1 |
| 1 | 8 | 17 | 7 | 1 |
| 1 | 9 | 19 | 9 | 1 |

### Key Observations
1. **Inputs 5-9 with c=0, or inputs 5-9 with c=1, produce a carry**
2. **Input 5 with c=0 produces output 0** (zero-creating)
3. **Input 0 with c=1 produces output 1** (zero-consuming)

---

## The Zeroless Constraint

### Zeroless Multiplication
If N is zeroless and 2N is also zeroless, then:
- Every digit of N must avoid producing a 0 in 2N
- The forbidden transitions are: (c=0, d=5) → output 0

So if N is zeroless and contains digit 5, then 2N has a zero (from that position, if c=0).

### The Transfer Matrix
Let Z_m = set of zeroless m-digit strings.
Define the transfer matrix T ∈ ℝ^{2×2} by:
```
T[c', c] = #{d ∈ {1,...,9} : δ(c, d) has output ≠ 0 and next carry = c'}
```

This counts zeroless-preserving transitions.

From the table:
- c=0 → c'=0: digits {1,2,3,4} → outputs {2,4,6,8} (4 choices)
- c=0 → c'=1: digits {6,7,8,9} → outputs {2,4,6,8} (4 choices) [Note: d=5 → output 0, excluded]
- c=1 → c'=0: digits {1,2,3,4} → outputs {3,5,7,9} (4 choices)
- c=1 → c'=1: digits {5,6,7,8,9} → outputs {1,3,5,7,9} (5 choices)

So the transfer matrix is:
```
T = | 4  4 |
    | 4  5 |
```

**Eigenvalues:** λ = (9 ± √17)/2 ≈ 7.56, 1.44

**Spectral radius:** ρ(T) = (9 + √17)/2 ≈ 7.56 < 9

---

## Questions

### Q1: What does ρ(T) < 9 mean?

The number of zeroless m-digit numbers is 9^m. The number of zeroless m-digit numbers N such that 2N is also zeroless grows like ρ(T)^m.

Since ρ(T) ≈ 7.56 < 9, the proportion of zeroless numbers that stay zeroless after doubling decays exponentially:
```
#{N zeroless m-digit : 2N zeroless} / 9^m ≈ (7.56/9)^m = 0.84^m → 0
```

**Does this explain why zeroless powers of 2 become rare?**

### Q2: Iteration of the automaton

For 2^n, we apply the doubling automaton n times starting from 1:
```
1 → 2 → 4 → 8 → 16 → 32 → 64 → 128 → ...
```

At each step, we need the result to be zeroless. The carry state after processing all digits is the "running state" that feeds into the next multiplication.

**Can you model the sequence of m-digit prefixes of {2^n} as a path in a directed graph?**

### Q3: The forbidden pattern

A zeroless number N with digit 5 (and carry 0 at that position) will produce a zero in 2N.

For 2^n to be zeroless, it must either:
- Contain no digit 5, OR
- Every digit 5 must have a carry coming into it

**Can you characterize which powers of 2 are zeroless in terms of this constraint?**

### Q4: Prefix evolution

The m-digit prefix of 2^{n+1} is determined by the m-digit prefix of 2^n plus the carry structure.

Define the prefix graph G_m:
- Vertices: m-digit prefixes that appear among {2^n}
- Edges: w → w' if ∃n with prefix_m(2^n) = w and prefix_m(2^{n+1}) = w'

**Properties:**
- From APPROACH 43, |V(G_m)| ≤ 5
- The graph has some cycle structure

**Can you characterize this graph? Does it explain why zeroless prefixes die out?**

### Q5: Why does zerolessness fail at m ≥ 36?

The spectral radius ρ(T) ≈ 7.56 implies zeroless-preserving chains become exponentially rare. But the actual failure happens at m = 36 for prefixes.

**Is there a connection between:**
- ρ(T) = (9 + √17)/2 ≈ 7.56
- The threshold m = 36
- The boundary n = 86?

### Q6: The role of leading digits

The automaton processes digits right-to-left, but prefixes are defined left-to-right. There's a mismatch.

For the m-digit prefix, what matters is:
1. The leading m digits of 2^n
2. The carry that propagates into position m+1 from position m+2, m+3, ...

**Can you model the leading-digit dynamics separately from the trailing-digit dynamics?**

### Q7: Spectral analysis of zeroless chains

Let A_m be the number of length-m paths in the automaton that:
- Start with carry 0 (no leading zeros)
- End with any carry
- Have all intermediate outputs in {1, ..., 9}

This counts m-digit zeroless numbers whose "image" under doubling has known prefix behavior.

**Theorem needed:** A_m / 9^m → 0 exponentially, with rate ρ(T)/9 ≈ 0.84.

Can you prove this and connect it to the Erdős conjecture?

### Q8: Why is ρ(T) = (9 + √17)/2?

The eigenvalues of T = [4,4; 4,5] are (9 ± √17)/2.

This specific value (9 + √17)/2 ≈ 7.56 determines the asymptotic density of doubly-zeroless numbers.

**Is there a combinatorial interpretation of this eigenvalue?** Why √17?

Note: 17 = 1 + 16 = 1 + 4^2, and det(T) = 20-16 = 4, tr(T) = 9.

### Q9: Complete proof via automaton?

Can the carry automaton approach yield a complete analytic proof?

**Desired theorem:** For all sufficiently large n, 2^n contains a zero digit.

**Proof approach:**
1. Model 2^n as the result of n applications of the doubling automaton to 1
2. Track the "zeroless feasibility" at each step using the transfer matrix
3. Show that zeroless feasibility decays exponentially with n

**What are the obstacles to this approach?**

---

## Desired Output

1. A rigorous formulation of the carry automaton model for powers of 2
2. Connection between the spectral radius ρ(T) ≈ 7.56 and the zeroless threshold
3. Either a proof (or proof sketch) that uses automaton dynamics, or a clear statement of what's missing
4. Explanation of why the specific structure of base-10 doubling leads to eventual zeros

---

## Additional Data

### Spectral Analysis
Transfer matrix T = [4,4; 4,5]
- Characteristic polynomial: λ² - 9λ + 4
- Eigenvalues: (9 ± √17)/2 = {7.561..., 1.438...}
- Spectral radius: 7.561...
- Ratio to 9: 0.8402...

### Powers of 2 Prefix Chains
```
2^0 = 1
2^1 = 2
2^2 = 4
2^3 = 8
2^4 = 16 (first appearance of 6)
2^5 = 32
2^6 = 64
2^7 = 128 (first 3-digit with all nonzero)
2^8 = 256 (first appearance of 5)
2^9 = 512
2^10 = 1024 (first zero!)
...
2^86 = 77371252455336267181195264 (last zeroless)
2^87 = 154742504910672534362390528 (contains 0)
```
