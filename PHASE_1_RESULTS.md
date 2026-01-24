# Phase 1 Results: Criterion Analysis

## Key Finding: G=0 vs QR-Trapped

**The two criteria are NOT equivalent:**

| Criterion | Definition | Dangerous primes < 800K |
|-----------|------------|------------------------|
| **G(n,m) = 0** | No coprime divisor pair sums to 0 mod m | **57 primes** |
| **QR-trapped** | All prime factors are QRs mod m | **21 primes** |

**Relationship**: QR-trapped ⟹ G=0, but NOT vice versa.

All 21 QR-dangerous primes are also G-dangerous. The 36 "G-only" cases occur when n_k is prime.

## Why They Differ

For **composite** n: G(n, m) = 0 ⟺ QR-trapped

For **prime** n: G(n, m) = 0 ⟺ n ≢ -1 (mod m)
- The only coprime pair is (1, n)
- G = 0 iff 1 + n ≢ 0 (mod m), i.e., n ≢ -1 (mod m)

**Example**: p = 21169, k = 4
- n_4 = 5297 (prime)
- m_4 = 19
- 5297 ≡ 15 (mod 19), and 15 is NOT a QR mod 19
- But 5297 ≢ 18 = -1 (mod 19), so G(5297, 19) = 0
- QR-trapped: NO (5297 is NR mod 19)
- G = 0: YES (prime with n ≢ -1)

## The 57 G-Dangerous Primes

```
21169, 61681, 66529, 67369, 87481, 94441, 99961, 112249, 118801, 163249,
176089, 196561, 202129, 219409, 224401, 225289, 231961, 242449, 246241, 270001,
276721, 347209, 370561, 386401, 388369, 397489, 400009, 415969, 436801, 437809,
454969, 463849, 464521, 483289, 496609, 505201, 521929, 526681, 529489, 532249,
534601, 608161, 629689, 637729, 670849, 684289, 691681, 695689, 696361, 706729,
709921, 739201, 755329, 757201, 770449, 789721, 795001
```

## The 21 QR-Dangerous Primes

```
61681, 87481, 163249, 176089, 219409, 224401, 242449, 276721, 370561, 397489,
437809, 496609, 526681, 529489, 608161, 684289, 691681, 706729, 709921, 739201,
789721
```

## Rescue Analysis

**All 57 G-dangerous primes are rescued** by either Type I or Type II at some k.

### Primes Needing k > 5 for Rescue (10 primes)

| Prime p | Rescue k | Method |
|---------|----------|--------|
| 66529 | 7 | Type II (G) |
| 370561 | 8 | Type II (G) |
| 400009 | 6 | Type I |
| 415969 | 6 | Type I |
| 437809 | 7 | Type II (G) |
| 532249 | 12 | Type I |
| 637729 | 8 | Type I |
| 670849 | 7 | Type I |
| 695689 | 6 | Type I |
| 706729 | 7 | Type II (G) |

**Maximum k needed**: 12 (for p = 532249)

### Primes Rescued at k ≤ 5 (47 primes)

The remaining 47 primes are all rescued by k ≤ 5, either via Type I or Type II.

## Which Criterion to Use for the Proof?

**Recommendation: Use G = 0 (the actual condition)**

Reasons:
1. G(n, m) ≥ 1 is the actual ESC condition we need
2. The 57-prime list is the true "dangerous" set
3. QR-trapping is a sufficient but not necessary condition for G = 0

## Implications for the Covering Argument

The covering argument must show that for all p in the 57-prime list:
- Either Type I succeeds at some k, OR
- Type II (meaning G > 0) succeeds at some k

Since we've verified this computationally for all p < 800K, the proof needs to:
1. Characterize what makes these 57 primes special
2. Prove that the rescue mechanism (Type I or Type II at k > 5) always works

## Files Generated

- `dangerous_primes_G0_full.csv`: All 57 primes with rescue data
- `esc_criterion_analysis.py`: Verification code
- `esc_full_analysis.py`: Full analysis code

## Next Steps

1. Understand why G=0 vs QR-trapped differ (prime n_k cases)
2. Characterize the 10 primes needing k > 5
3. Determine if there's a universal bound on rescue k
4. Build the covering argument using the G=0 criterion
