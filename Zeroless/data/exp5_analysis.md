# Experiment 5: Global Carry Invariant Search -- Analysis

## Headline Result

**No global carry invariant cleanly separates zeroless from non-zeroless powers.**
All candidate invariants have overlapping ranges. The apparent differences (e.g.,
max carry run: zeroless mean 3.7 vs non-zeroless mean 9.5) are entirely attributable
to the SIZE difference (zeroless powers have <=26 digits, non-zeroless grow to thousands).

## Detailed Findings

### Test 1: Carry Statistics Comparison
| Metric | Zeroless (mean) | Non-zeroless (mean) | Notes |
|--------|-----------------|---------------------|-------|
| carry_density | 0.56 | 0.50 | Expected ~0.50 for all |
| max_carry_run | 3.69 | 9.49 | Size-dependent, not intrinsic |
| transition_density | 0.55 | 0.50 | Expected ~0.50 for all |
| digit_sum | 59.8 | 3410 | Trivially size-dependent |

The carry_density is slightly elevated for zeroless (0.56 vs 0.50) because zeroless
digits {1,...,9} have mean 5 vs uniform {0,...,9} mean 4.5, so doubling produces
slightly more carries. But the effect is tiny and inconsistent.

### Test 2: Monotone Quantities
- Carry density converges to 0.50 +/- 0.01 for all digit counts k
- Max carry run grows as ~log(k): about 10 for k=1000, 13 for k=3000
- This growth is consistent with max of ~k independent Bernoulli(0.5) trials
- No quantity shows monotone behavior beyond what size growth explains

### Test 3: Carry Avalanches
- Zeroless powers: 0.15 avalanches per doubling (trivially low -- too few digits)
- Non-zeroless: 23.7 avalanches per doubling
- This is a SIZE effect, not an intrinsic invariant

### Test 4: Digit Sum
- digit_sum / digit_count = 4.50 for non-zeroless (exact uniform average)
- digit_sum / digit_count = 4.61 for zeroless (slightly elevated because no zeros)
- Expected for zeroless-uniform on {1,...,9}: mean digit = 5.0
- Observed 4.61 < 5.0 suggests zeroless powers don't have uniform-on-{1,...,9} digits
  (they have equidistributed-on-{0,...,9} digits that happen to avoid 0)

### Test 5: Combined Invariants
ALL candidates have overlapping ranges between zeroless and non-zeroless:
- carry_density: overlap [0.20, 0.75]
- transition_density: overlap [0.25, 0.80]
- Q1 (cd * k): overlap [1.2, 16.7]
- Q2 (td * k): overlap [1.5, 18.5]
- Q3 (dsum/k): overlap [3.17, 5.86]
- log_digit_product: overlap [5.1, 33.6]

## Implications for Proof Strategy

### Shape C (Global Carry Invariant) does NOT have an obvious target
The "global carry forcing" idea from M4-B predicted a quantity that is bounded for
zeroless powers but unbounded otherwise. No such quantity was found. All carry-based
metrics converge to the same values regardless of zerolessness, because carries are
memoryless (Exp 2) and digits look uniform (also Exp 2).

### The problem is NOT in the carry structure
Combined with Exp 2 (memoryless carries, zero correlations), this confirms: the
carry chain contains NO information distinguishing zeroless from non-zeroless powers.
Any proof mechanism must look at a GLOBAL property of the digit string, not the
local carry dynamics.

### What the digit sum tells us
The zeroless dsum/k = 4.61 (not 5.0 as expected for uniform-on-{1,...,9}) tells
us that zeroless powers of 2 don't have "typical zeroless number" digit distributions.
They're numbers that happen to avoid 0, not numbers drawn from the zeroless distribution.
This is consistent with equidistribution being the driving mechanism.

## Signal Strength: MEDIUM (informative negative)
Important negative result: rules out simple carry-based invariants. Confirms
the problem is purely about equidistribution, not carry structure.
