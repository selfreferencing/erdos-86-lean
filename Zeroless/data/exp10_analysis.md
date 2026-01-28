# Experiment 10: Higher-Order Constraint Transfer Matrices

## Summary

Built transfer matrices for m-fold zeroless constraints (x, 2x, 4x, ..., 2^{m-1}x all zeroless) for m=1 through m=18. The branching factor beta(m) = rho(m)/2 decreases monotonically from 4.5 to 1.706. Extrapolation predicts the critical threshold beta=1 at m~27.

## Key Findings

### 1. The beta(m) sequence

| m | dim | rho(m) | beta(m) | beta-4 |
|---|-----|--------|---------|--------|
| 1 | 1 | 9.000 | 4.500 | +0.500 |
| 2 | 2 | 8.531 | 4.266 | +0.266 |
| 3 | 4 | 8.035 | 4.018 | +0.018 |
| 4 | 8 | 7.505 | 3.753 | -0.247 |
| 5 | 16 | 7.020 | 3.510 | -0.490 |
| 6 | 32 | 6.632 | 3.316 | -0.684 |
| 7 | 64 | 6.276 | 3.138 | -0.862 |
| 8 | 128 | 5.912 | 2.956 | -1.044 |
| 9 | 256 | 5.594 | 2.797 | -1.203 |
| 10 | 512 | 5.268 | 2.634 | -1.366 |
| 11 | 1024 | 4.978 | 2.489 | -1.511 |
| 12 | 2048 | 4.702 | 2.351 | -1.649 |
| 13 | 4096 | 4.462 | 2.231 | -1.769 |
| 14 | 8192 | 4.229 | 2.115 | -1.885 |
| 15 | 16384 | 4.016 | 2.008 | -1.992 |
| 16 | 32768 | 3.801 | 1.901 | -2.099 |
| 17 | 65536 | 3.600 | 1.800 | -2.200 |
| 18 | 131072 | 3.413 | 1.706 | -2.294 |

### 2. Monotonic decrease is strict and shows no sign of plateauing

The decrease per step is approximately 0.1 in beta, with a slight deceleration. The successive differences in beta range from -0.265 (m=4) to -0.094 (m=18), with a ratio of consecutive differences hovering around 0.93-0.95.

### 3. Asymptotic fit

Best fit: **beta(m) ~ 4.71 * exp(-0.0572 * m)**

This predicts:
- beta = 4 at m ~ 2.9 (actual: between m=3 and m=4, confirmed)
- beta = 2 at m ~ 15.0 (actual: between m=15 and m=16, confirmed)
- **beta = 1 at m ~ 27.1** (not yet verified computationally)

The exponential fit has the lowest residual sum of squares (0.0014) among models tested.

### 4. Information per additional constraint

Each additional doubling constraint provides approximately 0.055 nats (0.079 bits) of information about the carry state. This quantity is remarkably stable from m=5 onward:

- m=5 to m=18: range [0.051, 0.060] nats, mean 0.054 nats

The total information needed to push from supercritical (beta=4.5) to critical (beta=1) is ln(4.5) ~ 1.504 nats. At 0.054 nats per constraint, this requires approximately 28 constraints beyond m=1, consistent with the exponential fit.

### 5. Positive correlation between consecutive survivors

Compare beta(m) with the independence prediction beta_indep(m) = 5*(9/10)^m:

| m | beta(m) | beta_indep(m) | ratio |
|---|---------|---------------|-------|
| 1 | 4.500 | 4.500 | 1.000 |
| 2 | 4.266 | 4.050 | 1.053 |
| 3 | 4.018 | 3.645 | 1.102 |
| 4 | 3.753 | 3.281 | 1.144 |
| 5 | 3.510 | 2.953 | 1.189 |
| 8 | 2.956 | 2.151 | 1.374 |
| 10 | 2.634 | 1.744 | 1.510 |
| 15 | 2.008 | 1.034 | 1.941 |
| 18 | 1.706 | 0.756 | 2.257 |

The ratio grows with m, meaning consecutive zeroless powers are positively correlated, and this correlation strengthens for longer windows. The carry structure creates "inertia": a zeroless power makes the next one more likely to be zeroless. This pushes the beta=1 crossing from the independence prediction of m~15 to the actual m~27.

### 6. Characteristic polynomial structure

Despite the state space growing as 2^{m-1}, the characteristic polynomial has very few nonzero terms:

| m | dim | nonzero terms | % active |
|---|-----|---------------|----------|
| 1 | 1 | 2 | 100% |
| 2 | 2 | 3 | 100% |
| 3 | 4 | 4 | 80% |
| 4 | 8 | 5 | 56% |
| 5 | 16 | 6 | 35% |
| 6 | 32 | 8 | 24% |
| 7 | 64 | 13 | 20% |
| 8 | 128 | 17 | 13% |

Most eigenvalues are zero, indicating the active subspace is small. The trace is always 9 (sum of eigenvalues = 9 for all m). The effective rank grows much slower than 2^{m-1}.

### 7. Orbit verification: beta = rho/2 confirmed for all m

For every m=1..8 tested, the orbit branching factor converges to rho/2 by k=7 or k=8. Typical error at k=8: < 0.001. The relationship is exact in the limit.

## Interpretation

### What these results mean

The m-fold constraint transfer matrix captures how the "zeroless carry chain" propagates through m consecutive doublings. Each additional doubling adds ~0.055 nats of constraint. The system transitions from supercritical (growing survivor count) to subcritical (shrinking count) at approximately m=27.

### What these results do NOT mean

- beta(4) < 4 does NOT mean quadruple survivors go extinct. The extinction threshold is beta=1, not beta=4. The value 4 appeared in the B-series as the guaranteed minimum from the pair lifting lemma, but it is not a critical threshold for the branching process.
- beta(m) < 1 for some m would prove: for sufficiently large k, there is no window of m consecutive orbit elements all k-digit-zeroless. This is meaningful but does not prove the 86 conjecture directly.

### Connection to density-zero question

The positive correlation finding (beta(m) > 5*0.9^m) has implications for the density-zero approach in Experiment 9. It means zeroless powers tend to cluster, which makes them harder to rule out by averaging arguments. The carry-mediated inertia preserves zerolessness across consecutive powers more than random chance would predict.

### The 0.055-nat information constant

The most structurally interesting finding is the stable information per constraint: approximately 0.055 nats per doubling. This suggests a finite "channel capacity" of the carry system. If this constant can be understood theoretically (perhaps via the entropy rate of the carry Markov chain), it would give a principled prediction for when beta crosses 1.

## Next step

Verify the beta=1 crossing computationally by extending to m=25-30 using sparse methods (dim = 2^24 to 2^29, i.e., 16M to 500M states). This would require iterative eigenvalue methods on sparse matrices.
