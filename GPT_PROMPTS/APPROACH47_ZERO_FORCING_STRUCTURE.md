# APPROACH 47: Zero-Forcing via Prefix Structure

## Context

We are seeking an **analytic proof** of the Erdős 86 Conjecture: 2^86 is the last power of 2 with no zero digit.

**What's PROVED:**
- |P_m| ≤ 4: At most 4 distinct m-digit prefixes appear among {2^n : n < L_m}
- The appearing prefixes come from n with ⌊n·θ⌋ = m-1, where θ = log₁₀(2)
- This means n ∈ [(m-1)/θ, m/θ), an interval of length 1/θ ≈ 3.32

**What's OPEN (the zero-forcing gap):**
For m ≥ 36, prove that the ≤4 appearing prefixes all contain the digit 0.

**Key observation:** The appearing prefixes are literally the first m digits of 2^n for n in a specific small range. For m = 36, we need n ∈ [116.2, 119.5], so n ∈ {117, 118, 119}.

---

## The Structural Question

The prefixes that appear for depth m are:
```
w_i(m) = ⌊2^{n_i} / 10^{n_i·θ - m + 1}⌋  for n_i ∈ [(m-1)/θ, m/θ) ∩ ℤ
```

Equivalently: w_i(m) = first m digits of 2^{n_i}.

**Question:** Why do the first m digits of 2^n contain a zero for all n ≥ 117 (approximately)?

---

## Data

For m = 36, the candidate n values are 117, 118, 119:
- 2^117 = 166153499473114484112975882535043072 (36 digits, contains 0)
- 2^118 = 332306998946228968225951765070086144 (36 digits, contains 0)
- 2^119 = 664613997892457936451903530140172288 (36 digits, contains 0)

For m = 37, the candidate n values are 120, 121, 122, 123:
- 2^120 = 1329227995784915872903807060280344576 (37 digits, contains 0)
- 2^121 = 2658455991569831745807614120560689152 (37 digits, contains 0)
- 2^122 = 5316911983139663491615228241121378304 (37 digits, contains 0)
- 2^123 = 10633823966279326983230456482242756608 (38 digits, N/A)

**Pattern:** Every 2^n for n ≥ 117 appears to contain a zero in its decimal expansion.

---

## Questions

### Q1: Is there a threshold N₀ such that 2^n contains a 0 for all n ≥ N₀?

The last zeroless power is 2^86. But is there a smaller threshold N₀ ≤ 86 such that all 2^n for n ≥ N₀ contain zeros?

Looking at the zeroless powers: n ∈ {1,2,...,9,13,14,15,16,18,19,24,25,27,28,31,...,39,49,51,67,72,76,77,81,86}

The gaps grow: after 86, there are no more zeroless powers (verified to n ~ 10^10).

### Q2: What's special about the digit structure of 2^n for large n?

For n ≥ 117, why must 2^n contain a 0? Possible explanations:

1. **Density argument:** With ~0.301n digits, probability of all nonzero is ~0.9^{0.301n} → 0
2. **Structural constraint:** The multiplication-by-2 dynamics force certain digit patterns
3. **Modular constraint:** 2^n mod 10^k must eventually hit residue classes with internal zeros

### Q3: Can we prove zero-forcing via the "unprotected 5" mechanism?

From APPROACH 46: A zero appears when we double a 5 with incoming carry 0.

**Claim:** For n ≥ N₀, 2^n contains either:
- A digit 0 directly, OR
- An "unprotected 5" (digit 5 followed by digit < 5)

If true, then 2^{n+1} contains a 0, giving an inductive argument.

**Question:** Can this be proved? What's the mechanism that forces unprotected 5s to appear?

### Q4: Characterize the "never contains 0 or unprotected 5" language

Define the "safe" language S = {strings over {1,...,9} with no 5 followed by {1,2,3,4}}.

**Key insight:** After digit 5, only {5,6,7,8,9} are allowed.

This is a **regular language** recognized by a finite automaton:
- State 0: Normal state
- State 1: Just saw a 5
- From State 0: digits 1-4,6-9 → State 0; digit 5 → State 1
- From State 1: digits 5-9 → State 0; digits 1-4 → REJECT

**Question:** What's the growth rate of |S ∩ {1,...,9}^m|? If it's < 9^m, the language is thin.

### Q5: Spectral analysis of the "safe" automaton

The transition matrix for the safe automaton (on alphabet {1,...,9}) is:
```
     State 0  State 1
From 0:  8       1      (digits 1-4,6-9 stay; digit 5 transitions)
From 1:  5       0      (digits 5-9 return; digits 1-4 reject)
```

Wait, this isn't quite right because we need to track acceptance, not just transitions.

**Refined model:** States are {0, 1} where 1 means "previous digit was 5".
- From state 0: emit d ∈ {1,...,9}, go to state (d=5 ? 1 : 0)
- From state 1: emit d ∈ {5,...,9} only (else reject), go to state (d=5 ? 1 : 0)

Transition counts:
- State 0 → State 0: 8 ways (digits 1-4, 6-9)
- State 0 → State 1: 1 way (digit 5)
- State 1 → State 0: 4 ways (digits 6-9)
- State 1 → State 1: 1 way (digit 5)

Transfer matrix T = [8, 1; 4, 1]

**Eigenvalues:** λ = (9 ± √17)/2 ≈ 7.56, 1.44

**Spectral radius:** ρ(T) ≈ 7.56

So |S_m| ~ 7.56^m, giving density 7.56^m / 9^m = 0.84^m → 0.

### Q6: Why doesn't this immediately prove zero-forcing?

The spectral analysis shows "safe" strings (no unprotected 5) are exponentially rare. But:

1. The first m digits of 2^n are NOT random strings
2. We need to show the SPECIFIC orbit {2^n} eventually leaves the safe language
3. Density → 0 doesn't mean the orbit can't track the shrinking set indefinitely

**The gap:** We need to connect the spectral bound to the specific dynamics of powers of 2.

### Q7: Modular approach to zero-forcing

The last k digits of 2^n are determined by 2^n mod 10^k.

**Key fact:** 2^n mod 5^k has period 4·5^{k-1} (since gcd(2, 5) = 1).

For k = 4: period = 4·125 = 500. So the last 4 digits of 2^n cycle with period 500.

**Question:** Among the 500 residue classes of 2^n mod 10^4, how many have:
- No zero in the last 4 digits, AND
- No "unprotected 5" pattern (52, 53, 54, 51) in the last 4 digits?

If this count is small enough, and combined with leading-digit constraints, we might force zeros.

### Q8: The 4-digit suffix census

Compute: For n = 0, 1, ..., 499, what fraction of 2^n mod 10000 are "safe" (zeroless and no unprotected 5)?

If this fraction is small, say < 10%, then combined with the ~0.9^m leading-digit constraint, we get very strong bounds.

---

## Desired Output

1. Analysis of the "safe" language and its spectral radius
2. Computation of the 4-digit suffix census (fraction of safe residues among 2^n mod 10^4)
3. Assessment of whether modular + spectral arguments can prove zero-forcing
4. If not, identification of what additional input is needed
5. Any insight into why the threshold appears to be around n ≈ 87 (last zeroless) rather than much larger

---

## Reference Data

The 36 zeroless powers of 2:
```
n ∈ {1,2,3,4,5,6,7,8,9,13,14,15,16,18,19,24,25,27,28,31,32,33,34,35,36,37,39,49,51,67,72,76,77,81,86}
```

Transfer matrix for "safe" strings: T = [8, 1; 4, 1], ρ(T) ≈ 7.56

Density decay: (7.56/9)^m ≈ 0.84^m
