# Experiment 6: First-Zero Position -- Analysis

## Key Findings

### 1. j=1 is IMPOSSIBLE
The last digit of 2^n cycles through {2,4,8,6}, never 0. So j >= 2 always.
This alone accounts for the shift from expected mean 10 to observed mean 11.

### 2. NOT geometric(0.1)
Chi-squared = 5591 with 48 df (terrible fit). The distribution is approximately
geometric for j >= 2, but with significant deviations:
- j=2 is overrepresented (0.100 vs geometric 0.090)
- All values j=2..30 have ratio obs/geo(0.1) ~ 1.10-1.12
- Systematic upward shift because j=1 mass redistributes

### 3. Strong modular structure
eta^2 (fraction of variance explained by residue class) grows with k:
- k=1 (period 4): 1.2%
- k=2 (period 20): **11.0%**
- k=3 (period 100): **20.1%**
- k=4 (period 500): **28.4%**
- k=5 (period 2500): **37.6%**

Some residue classes force j=2 exactly (e.g., residue 83 mod 100 always gives j=2).
This means the 5-adic orbit structure strongly constrains the first-zero position.

### 4. Significant autocorrelation with periodic structure
- lag 1: **0.328** (strong)
- lag 2: 0.090, lag 3: 0.030, lag 4: 0.009 (fast decay)
- But periodic oscillation at period ~20: lag 20: 0.091, lag 40: 0.084, lag 60: 0.079
- lag 100: **0.181** (resonance at period 100 = T_3)

The period-20 (= T_2 = 4*5) oscillation is the 5-adic structure showing through.

### 5. Consecutive j values are positively correlated
- corr(j(n), j(n+1)) = 0.328
- E[j(n+1) | j(n)=2] = 6.5 (well below mean 11)
- E[j(n+1) | j(n)=10] = 11.2 (at mean)
- When j(n) >= 10: P(j(n+1) >= 10) = 0.647 (vs unconditional ~0.43)

This is the carry persistence effect seen in Exp 3: if 2^n has many nonzero
trailing digits, 2^{n+1} inherits partial protection through the carry chain.

### 6. Record growth is slower than geometric predicts
- Actual slope: 20.88 * log(n)
- Expected for geometric: 94.91 * log(n)
- Ratio: 0.22

Extreme values are ~5x LESS extreme than a pure geometric model predicts.
The modular structure constrains how large j can get.

### 7. First zero is near the bottom of the number
- Median j/k = 0.0013 (first zero at the 0.1% mark from the bottom)
- Mean j/k = 0.0045
- The zero appears in the lowest few digits, not randomly placed

## Implications for Proof Strategy

### The modular structure is VERY strong
38% of j variance is explained by n mod 2500. This means for a given residue class,
j is substantially predictable. A proof could exploit this: show that for EVERY
residue class mod T_k, the predicted j is bounded, and then argue that 2^n must
eventually enter a residue class with small j.

### The autocorrelation is the carry persistence again
Same as Exp 3's finding: consecutive powers share trailing digit structure, creating
positive autocorrelation in the first-zero position. But the decorrelation is fast
(essentially gone by lag ~5, ignoring periodic terms).

### Period-20 resonance
The T_2 = 20 periodicity is a smoking gun for the 5-adic structure. It means the
modular approach (working with 2^n mod 10^k for small k) is genuinely informative
about the first-zero position, not just a formal device.

## Signal Strength: STRONG
Confirms and quantifies the modular structure of j(n). The eta^2 growth and
periodic autocorrelation provide concrete targets for a proof.
