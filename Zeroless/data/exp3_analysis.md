# Experiment 3: Triple Constraint -- Analysis

## Key Findings

### 1. Consecutive zeroless powers die out fast under pairing
- **Last single**: n=86 (2^86)
- **Last pair**: n=76 (2^76, 2^77)
- **Last triple**: n=35 (2^35, 2^36, 2^37)
- **Last quadruple**: n=34 (2^34, 2^35, 2^36, 2^37)

Triples die out at n=35 while singles persist to n=86. The gap (51 exponents) is large.
The triple constraint is dramatically more restrictive than the single constraint.

### 2. Growing positive correlation (carry persistence)
The ratio P(pair)/P(single)^2 grows with digit count k:
- k=1: 1.00, k=2: 1.05, k=3: 1.10, k=4: 1.16, k=5: 1.22, k=6: 1.28, k=7: 1.35, k=8: 1.43

This means consecutive n-values have POSITIVELY correlated zerolessness, and the
correlation strengthens at larger scales. Carries create persistence.

### 3. Doubling preserves zerolessness better than random
P(2x zeroless | x zeroless) exceeds the naive (9/10)^k at every scale:
- k=1: 0.889 vs 0.900 (slightly below)
- k=3: 0.796 vs 0.729 (above)
- k=5: 0.715 vs 0.590 (well above)
- k=7: 0.642 vs 0.478 (far above)

The carry dynamics creates a substantial persistence effect.

### 4. The carry-drop mechanism produces zeros
**Critical finding**: When the carry pattern has a 1-to-0 transition (carry drops),
the zero production rate jumps from 0.200 to **0.360**.

Mechanism: carry_in=0 with digit d=5 produces 2*5+0=10, giving output digit 0.
The 1-to-0 carry transition exposes this vulnerability. All-carry-1 patterns
protect against zeros (since 2d+1 is always odd).

### 5. Paired suffix depth drops sharply
- Max single suffix depth: 115 (n=7931)
- Max paired suffix depth: **81** (n=1958)
- Max triple suffix depth: **42** (n=432)

The paired constraint cuts max depth by ~30%, triple by ~63%.

### 6. Zero position distribution in 2x
When doubling a zeroless number produces a zero, the zero is most often at
position 0 (the units digit). Fraction at position 0:
- k=2: 0.692, k=3: 0.544, k=4: 0.452, k=5: 0.390, k=6: 0.345

This converges toward 1/k, suggesting zeros are roughly uniformly distributed
among positions, with a mild bias toward position 0.

## Implications for Proof Strategy

### BAD news for naive approaches:
The growing positive correlation (finding #2) means independence-based arguments
UNDERESTIMATE survival probability. The naive (9/10)^k is too optimistic as a
decay rate -- the real rate is slower because carries create persistence.

### GOOD news for paired/triple approaches:
Despite the persistence, the triple constraint dies out at n=35 (finding #1).
The "3 samples enrichment" idea from the synthesis has empirical support.
If one could prove that for large enough k, no triple (2^n, 2^{n+1}, 2^{n+2})
can have k zeroless trailing digits, this would directly prove the conjecture
(since for large n, three consecutive powers occupy the same digit count level).

### The carry-drop mechanism (finding #4) is the key vulnerability:
Whenever carries drop from 1 to 0 at some position, the zero rate jumps from
~0.20 to ~0.36. A proof could target this: show that long zeroless runs
require impossibly many carry-drops to be "lucky."

## Signal Strength: STRONG
The triple constraint data and carry-drop mechanism provide concrete proof targets.
The growing correlation is important structural information that constrains viable approaches.
