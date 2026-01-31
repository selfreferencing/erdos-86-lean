# Experiment 12: Maximum Offset k Analysis for p ≡ 1 (mod 24)

## Setup

For each prime p ≡ 1 (mod 24) up to 50,000,000, we find the minimum offset k (in range 0..99) such that:
- A_k = (p+3)/4 + k
- delta_k = 3 + 4k
- There exists a divisor d of A_k^2 with delta_k | (d + A_k)

This is equivalent to finding the certificate needed for `exists_good_A_and_divisor`.

## Key Results

**374,902 primes** p ≡ 1 (mod 24) were tested, up to 50,000,000.

### 1. Maximum k needed: **26** (at prime p = 8,803,369)

### 2. Top 20 hardest primes

| Rank | Prime p | Min k needed |
|------|---------|-------------|
| 1 | 8,803,369 | 26 |
| 2 | 22,605,361 | 22 |
| 3 | 36,740,929 | 17 |
| 4 | 20,322,481 | 17 |
| 5 | 12,426,481 | 17 |
| 6 | 2,451,289 | 17 |
| 7 | 1,430,641 | 17 |
| 8 | 37,767,409 | 15 |
| 9 | 34,103,161 | 15 |
| 10 | 87,481 | 15 |
| 11 | 32,794,441 | 14 |
| 12 | 24,897,601 | 14 |
| 13 | 22,202,569 | 14 |
| 14 | 15,052,489 | 14 |
| 15 | 14,872,729 | 14 |
| 16 | 11,720,641 | 14 |
| 17 | 10,051,441 | 14 |
| 18 | 7,257,721 | 14 |
| 19 | 1,450,849 | 14 |
| 20 | 806,521 | 14 |

### 3-5. Failure Analysis

| Offset limit | Failures | Largest failing prime |
|-------------|----------|----------------------|
| k = 0..47 | **0** | N/A |
| k = 0..63 | **0** | N/A |
| k = 0..99 | **0** | N/A |

**All three offset limits suffice for every prime up to 50 million.** Even numOffsets = 27 would suffice.

### Full Distribution of Minimum k Values

| k | Count | Percentage | Cumulative |
|---|-------|-----------|------------|
| 0 | 221,035 | 58.96% | 58.96% |
| 1 | 124,397 | 33.18% | 92.14% |
| 2 | 18,795 | 5.01% | 97.15% |
| 3 | 4,194 | 1.12% | 98.27% |
| 4 | 2,916 | 0.78% | 99.05% |
| 5 | 2,314 | 0.62% | 99.67% |
| 6 | 249 | 0.07% | 99.73% |
| 7 | 643 | 0.17% | 99.90% |
| 8 | 83 | 0.02% | 99.93% |
| 9 | 143 | 0.04% | 99.96% |
| 10 | 20 | 0.01% | 99.97% |
| 11 | 68 | 0.02% | 99.99% |
| 12 | 8 | 0.00% | 99.99% |
| 13 | 12 | 0.00% | 99.99% |
| 14 | 15 | 0.00% | 100.00% |
| 15 | 3 | 0.00% | 100.00% |
| 17 | 5 | 0.00% | 100.00% |
| 22 | 1 | 0.00% | 100.00% |
| 26 | 1 | 0.00% | 100.00% |

Note: k = 16, 18-21, 23-25 have **zero** primes needing exactly that k value.

### Hardest Prime Certificate

For p = 8,803,369 (the unique prime requiring k = 26):
- A_0 = 2,200,843 is **prime** (no useful divisors of A_0^2 except 1 and itself)
- Offsets k = 1..25 all fail due to unfortunate factorization patterns
- At k = 26: A = 2,200,869 = 3^2 * 11^2 * 43 * 47
  - A^2 has 225 divisors
  - delta = 107
  - d = 121 = 11^2 satisfies d ≡ -A (mod 107) and d | A^2
  - Certificate: (d + A) / delta = 2,200,990 / 107 = 20,570

### Observations

1. **k = 0 suffices 59% of the time.** The base value A = (p+3)/4 already works for most primes.

2. **k = 0 or 1 suffices 92% of the time.** Adding just one offset handles the vast majority.

3. **k <= 5 covers 99.67%.** Only 0.33% of primes need k > 5.

4. **The distribution drops exponentially** but is not perfectly monotone (k=7 has more primes than k=6, k=9 more than k=8, k=11 more than k=10). This is because odd k values produce delta = 3+4k that may be prime (harder to satisfy the congruence), while even k values produce delta that may have small factors (easier).

5. **numOffsets = 48 is vastly more than sufficient** for all primes up to 50 million. Even numOffsets = 27 would work. The growth of max-k with p appears very slow (sublogarithmic).

6. **The hardest primes have A_0 prime.** When (p+3)/4 is itself prime, A_0^2 has only 3 divisors {1, A_0, A_0^2}, making the congruence condition hard to satisfy. The algorithm then needs to search for an offset where A_k has rich factorization.
