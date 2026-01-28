# Experiment 1: Transfer Operator with Hole -- Analysis

## Key Findings

### Formulation A (Single-step doubling)
- T_full spectral radius: 10 (trivial: 10 digits)
- T_hole spectral radius: **9.0000** (exactly 9/10 ratio)
- This is the naive per-digit probability of being nonzero. No surprise.

### Formulation B (5-adic survivor counting)
- Growth factor per level: **exactly 4.5** (to 4 decimal places at every level)
- Density matches **(9/10)^{k-1}** precisely through k=8
- Confirms the known formula: survivor count = 4 * 4.5^{k-1}

### Formulation C (Conditioned transfer -- THE KEY RESULT)
- Spectral radius of conditioned matrix: **8.5311** (< 9)
- Ratio to unconditioned: **0.9479 < 1**
- Meaning: when you condition on already being zeroless, the carry dynamics make
  the next digit SLIGHTLY more likely to hit 0 than the naive 1/10 rate
- Mechanism: carry_in=0 with d_in=5 produces d_out=0. This is the only zeroless
  input that produces a zero output, but it matters.
- carry_in=0: 8/9 outputs are zeroless (d=5 maps to 0)
- carry_in=1: 9/9 outputs are zeroless (2d+1 is always odd, never 0)

### Formulation D (Multi-scale zeroless-to-zeroless)
- Fraction of zeroless residues whose double is also zeroless:
  - k=1: 0.889, k=2: 0.840, k=3: 0.796, k=4: 0.754, k=5: 0.715
- These are HIGHER than (9/10)^k, meaning doubling is LESS disruptive to
  zerolessness than random reshuffling would be
- The carry dynamics creates persistence: carry_in=1 guarantees zeroless output,
  and carry_in=1 occurs ~5/9 of the time from zeroless inputs

## Interpretation

### What this CONFIRMS
1. The 4.5^k barrier is confirmed at the operator level (Formulation B)
2. Per-digit escape rate is exactly 9/10 (Formulation A) -- trivially tight
3. The carry chain creates correlations that HELP zeroless survival (Formulation D)

### What's NEW
The conditioned transfer (Formulation C) reveals a **slight anti-persistence** at
the single-step level: spectral radius 8.5311/9 = 0.9479 < 1. This means the
carry dynamics, while helping in the multi-scale view, still can't fully compensate.

But this is a single-step analysis. The multi-scale analysis (Formulation D) shows
the OPPOSITE: the zl->zl transition fraction exceeds (9/10)^k, meaning multi-step
correlations help survival.

### The tension
- Single-step conditioned: decay factor 0.9479 (faster than naive 0.9)
- Multi-step: zl->zl fraction > (9/10)^k (slower decay than naive)
- This means: inter-digit correlations from carries HELP survival, more than
  compensating for the single-step anti-persistence

### For the proof strategy
The escape rate approach via simple transfer operator does NOT immediately give
subcriticality. The carry dynamics creates correlations that resist escape. Any
proof must either:
1. Show these correlations are insufficient at large enough scale, OR
2. Find a different mechanism that overwhelms the carry persistence

### Signal strength: MEDIUM
Confirms the synthesis predictions. The 0.9479 conditioned ratio is new data.
The persistence effect in Formulation D is the main takeaway: carries help survival.
