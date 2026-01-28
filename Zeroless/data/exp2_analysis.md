# Experiment 2: Carry Correlation Decay -- Analysis

## Headline Result

**The carry chain is PERFECTLY MEMORYLESS (Dobrushin coefficient = 0).**

For zeroless digits {1,...,9}, P(carry_out = 1 | carry_in = c) = 5/9 regardless of c.
For actual 2^n digits (uniform on {0,...,9}), P(carry_out = 1 | carry_in = c) = 1/2 regardless of c.

The carry Markov chain mixes in ZERO steps. There is no correlation length to estimate because
there is no correlation to begin with.

## Detailed Findings

### Test 1: Carry Chain Theory
- Zeroless digits: P(c_out=1) = 5/9 independent of c_in
- Mechanism: exactly 5 of 9 digits {5,6,7,8,9} produce carry regardless of incoming carry
- Output digit distributions differ by carry_in: c_in=0 gives even digits, c_in=1 gives odd digits
- BUT the carry output is invariant. The carry chain has rank-1 transition matrix.

### Test 2-4: Digit Correlations in Powers of 2
- All correlations < 0.001 at all separations m = 1..50
- No directional difference (left-to-right vs right-to-left)
- Digits of 2^n are essentially i.i.d. uniform on {0,...,9}
- No exponential decay needed because correlations are already zero

### Test 3: Conditional Distributions
- P(d_{j+1} = a | d_j = b) = 0.100 +/- 0.001 for all a, b
- Maximum deviation from uniform: 0.0012
- The transition matrix is essentially doubly stochastic (identity/10)

### Test 5: Within Zeroless Suffix
- Correlations slightly larger (~0.01) but still negligible
- Sample sizes shrink at large separation (only ~14K pairs at m=19)
- No systematic pattern detected

### Test 6: Dobrushin Coefficient
- **Unconditioned carry chain: delta = 0** (perfect mixing)
- **Conditioned carry chain: delta = 0.056** (mixing time = 1 step)
- The conditioning (output must be nonzero) introduces a TINY perturbation

### Test 7: Actual Carry Statistics
- P(carry=0) = 0.5006, P(carry=1) = 0.4994 (expected: 1/2 for uniform digits)
- Transition matrix: all entries ~0.500 (perfectly memoryless)
- Carry runs: mean 2.0, max 23, geometric distribution

## Critical Interpretation

### What this means for the two-step template:

**Step 1 (correlation decay) is TRIVIALLY TRUE.** The carry chain has zero
correlation length. This is not just "short" -- it is literally zero. The carry
dynamics creates NO persistent correlations between digit positions.

**Step 2 (deterministic typicality) is the ENTIRE problem.** The digits of 2^n
LOOK random (all statistics match i.i.d. uniform within sampling error). But
"looking random" and "being provably random enough" are different things.

### The paradox of the 4.5^k barrier:
If carries are memoryless and digits are uncorrelated, why does the survivor
count grow as 4.5^k (supercritical) rather than matching the (9/10)^{k-1}
density (subcritical)?

Answer: The 4.5^k counts the number of RESIDUE CLASSES mod 10^k that are
zeroless-compatible. This is a combinatorial count, not a probability. The
relevant question is: among the T_k = 4*5^{k-1} orbit elements of 2^n mod 10^k,
how many are zeroless? The answer is ~(9/10)^{k-1} fraction, which is EXACTLY
the "random" prediction. The digits ARE random in this modular sense.

### Why the conjecture should be true but is hard to prove:
The equidistribution of 2^n mod 10^k (following from log_10(2) irrational)
means 2^n visits each residue class about equally often. Combined with (9/10)^{k-1}
density of zeroless residues, the expected number of zeroless 2^n at digit count k
is ~3.32 * (9/10)^{k-1}, which sums to a finite number. But turning this heuristic
into a proof requires effective equidistribution bounds that don't currently exist.

## Signal Strength: VERY STRONG
This experiment provides the clearest picture yet of the problem structure:
- Carries are memoryless (delta = 0)
- Digits of 2^n are empirically i.i.d. uniform
- The entire difficulty is in proving effective equidistribution of 2^n mod 10^k
- No "hidden correlations" exist to exploit -- the problem is purely about equidistribution
