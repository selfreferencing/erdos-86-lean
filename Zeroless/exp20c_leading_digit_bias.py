#!/usr/bin/env python3
"""
Experiment 20c: Quantifying the Leading Digit Bias for Small Orbit Indices

KEY INSIGHT FROM EXP 20b PART D:
For small orbit indices i < C*m, the upper digits have much higher P(digit=0)
than the global average of 1/10. At m=9, digit 9 has P(0|small) = 0.63.

This makes perfect sense: if n = m + i and i < C*m, then 2^n has exactly
m digits (D(n) = m). The orbit element is 2^n itself (no mod reduction needed
since 2^n < 10^m). The leading digit of 2^n is determined by the fractional
part of n * log10(2).

For the last few digits (close to the leading position), the digit can only
be nonzero if 2^n is large enough. Since 2^n has exactly m digits:
- 10^{m-1} <= 2^n < 10^m
- The j-th digit from the right (j = m is leading) equals floor(2^n / 10^{j-1}) mod 10

For j close to m, floor(2^n / 10^{j-1}) is the top (m-j+1) digits of 2^n.
The top digits of 2^n follow Benford's distribution.

THIS EXPERIMENT:
1. For each m, compute the EXACT P(digit j = 0) for small indices i < C*m
2. Compare to the theoretical prediction from Benford's law
3. Determine the EFFECTIVE survival rate for small indices
4. Show that the effective survival rate -> 0 exponentially
"""

import sys
import os
import time
import math
import numpy as np

sys.set_int_max_str_digits(100000)

M_MAX = 25  # Go much higher since this is cheap per element
C_CRIT = 1.0 / math.log10(2)
LOG10_2 = math.log10(2)


def digit_count(n):
    """Number of base-10 digits of 2^n."""
    return int(n * LOG10_2) + 1


def part_A_exact_bias(max_m=20):
    """Compute exact P(digit j = 0 | i in transition zone) for each m."""
    print("=" * 100)
    print("PART A: Exact Digit-Zero Probability for Transition Zone Indices")
    print("=" * 100)

    for m in range(3, min(max_m + 1, M_MAX + 1)):
        # Transition zone: n such that D(n) = m
        # D(n) = floor(n * log10(2)) + 1 = m iff (m-1)/log10(2) <= n < m/log10(2)
        n_low = math.ceil((m - 1) / LOG10_2)
        n_high = math.ceil(m / LOG10_2) - 1

        if n_high < n_low:
            continue

        candidates = list(range(n_low, n_high + 1))
        L = len(candidates)

        if L == 0:
            continue

        # For each candidate, compute all digit-zero indicators
        digit_zeros = np.zeros((L, m), dtype=int)  # digit_zeros[i][j] = 1 if digit j+1 is 0

        for idx, n in enumerate(candidates):
            val = pow(2, n)
            s = str(val)
            # s[0] is the leading digit, s[-1] is the ones digit
            # digit j+1 (1-indexed from right) corresponds to s[-(j+1)] if j+1 <= len(s)
            for j in range(min(m, len(s))):
                digit = int(s[-(j + 1)])
                if digit == 0:
                    digit_zeros[idx][j] = 1
            # If 2^n has fewer than m digits, the top digits are implicitly 0
            if len(s) < m:
                for j in range(len(s), m):
                    digit_zeros[idx][j] = 1

        # P(digit j = 0) for each digit position
        p_zero = np.mean(digit_zeros, axis=0)

        # Effective survival probability = Product (1 - P(digit j = 0))
        survival_factors = 1.0 - p_zero
        effective_survival = np.prod(survival_factors)

        # Comparison: if all were 1/10, survival would be 0.9^m
        benford_survival = 0.9 ** m

        print(f"\nm={m}: {L} candidates (n={n_low}..{n_high}), "
              f"effective_survival={effective_survival:.6e}, "
              f"0.9^m={benford_survival:.6e}, "
              f"ratio={effective_survival/benford_survival:.6f}")

        if m <= 12:
            print(f"  {'digit':>5}  {'P(0)':>8}  {'1-P(0)':>8}  {'log_factor':>12}")
            print("  " + "-" * 40)
            for j in range(m):
                pz = p_zero[j]
                sf = survival_factors[j]
                lf = math.log(sf) if sf > 0 else float('-inf')
                print(f"  {j+1:>5}  {pz:>8.4f}  {sf:>8.4f}  {lf:>12.6f}")


def part_B_extended_range(max_m=60):
    """Track the effective survival probability for larger m.

    For large m, 2^n has about 3-4 candidates with D(n) = m.
    The survival probability should decrease with m.
    """
    print("\n" + "=" * 100)
    print("PART B: Effective Survival Probability to m=60")
    print("=" * 100)

    print(f"\n{'m':>4}  {'L':>4}  {'n_range':>15}  {'eff_surv':>14}  "
          f"{'0.9^m':>14}  {'ratio':>10}  {'any_zeroless':>12}  {'max_p0':>8}")
    print("-" * 100)

    for m in range(3, min(max_m + 1, 80)):
        n_low = math.ceil((m - 1) / LOG10_2)
        n_high = math.ceil(m / LOG10_2) - 1

        if n_high < n_low:
            continue

        candidates = list(range(n_low, n_high + 1))
        L = len(candidates)

        if L == 0:
            continue

        # Check each candidate for zerolessness
        any_zeroless = False
        max_p0 = 0.0
        digit_zeros = np.zeros(m, dtype=float)

        for n in candidates:
            val = pow(2, n)
            s = str(val)
            if '0' not in s:
                any_zeroless = True

            for j in range(min(m, len(s))):
                digit = int(s[-(j + 1)])
                if digit == 0:
                    digit_zeros[j] += 1

        digit_zeros /= L
        max_p0 = float(np.max(digit_zeros))

        survival_factors = 1.0 - digit_zeros
        # Clip to avoid log(0)
        survival_factors = np.clip(survival_factors, 1e-10, 1.0)
        effective_survival = float(np.prod(survival_factors))
        benford_survival = 0.9 ** m
        ratio = effective_survival / benford_survival if benford_survival > 0 else 0

        zl_mark = "YES" if any_zeroless else "no"

        print(f"{m:>4}  {L:>4}  {n_low:>7}-{n_high:<7}  {effective_survival:>14.6e}  "
              f"{benford_survival:>14.6e}  {ratio:>10.6f}  {zl_mark:>12}  {max_p0:>8.4f}")


def part_C_per_candidate_survival(max_m=30):
    """For each individual candidate n, compute its per-digit survival product.

    The effective survival is actually computed per-candidate, not averaged.
    For each n with D(n) = m, compute Product_{j=1}^{m} (1 - indicator(digit j = 0)).
    This is just 0 or 1 depending on whether 2^n is zeroless.

    But we can compute the MARGINAL survival probability more carefully:
    for each n, how many zero digits does 2^n have?
    """
    print("\n" + "=" * 100)
    print("PART C: Per-Candidate Digit Profile for n > 86")
    print("=" * 100)

    print(f"\n{'n':>6}  {'D(n)':>5}  {'#zeros':>6}  {'first_zero':>10}  "
          f"{'prefix':>25}  {'all_zero_positions'}")
    print("-" * 100)

    for m in range(27, min(max_m + 1, 80)):
        n_low = math.ceil((m - 1) / LOG10_2)
        n_high = math.ceil(m / LOG10_2) - 1

        for n in range(max(87, n_low), n_high + 1):
            if digit_count(n) != m:
                continue
            val = pow(2, n)
            s = str(val)
            zero_positions = []
            for pos, ch in enumerate(s):
                if ch == '0':
                    # Position from right: len(s) - pos
                    zero_positions.append(len(s) - pos)
            n_zeros = len(zero_positions)
            first_zero_from_right = zero_positions[-1] if zero_positions else None

            prefix = s[:min(25, len(s))]
            if len(s) > 25:
                prefix = s[:12] + "..." + s[-10:]

            zero_str = str(zero_positions[:10])
            if n_zeros > 10:
                zero_str += f" ... ({n_zeros} total)"

            print(f"{n:>6}  {m:>5}  {n_zeros:>6}  "
                  f"{str(first_zero_from_right):>10}  "
                  f"{prefix:>25}  {zero_str}")


def part_D_benford_prediction(max_m=40):
    """Theoretical prediction: for small orbit index i, what is P(digit j = 0)?

    When n = m + i with i < C*m, the orbit element is 2^n = 2^{m+i}.
    Since D(n) = m, we have 10^{m-1} <= 2^n < 10^m.

    The j-th digit from the right of 2^n is:
    d_j = floor(2^n / 10^{j-1}) mod 10

    For the leading digit (j = m): d_m = floor(2^n / 10^{m-1}).
    Since 2^n < 10^m, we have d_m in {1, ..., 9}.

    For near-leading digits (j close to m):
    d_j = floor(2^n / 10^{j-1}) mod 10

    The fractional part of log10(2^n) = frac(n * log10(2)) determines
    the leading digits via Benford's law.

    Let alpha = frac(n * log10(2)). Then:
    2^n = 10^{m-1} * 10^alpha, so the top digits are determined by 10^alpha.

    For j from the top (j = m), the digit is floor(10^alpha).
    For j = m-1, the digit is floor(10^{alpha+1}) mod 10.
    For j = m-k, the digit is floor(10^{alpha+k}) mod 10.

    So digit j (counting from right, j=1 is ones, j=m is leading) = digit
    at position m-j from the top = floor(10^{alpha + m - j}) mod 10.

    P(digit j = 0) = P(floor(10^{alpha + m - j}) mod 10 = 0)
    = measure of alpha in [0,1) such that the (m-j+1)-th digit of 10^alpha is 0.

    For the ones digit (j=1): this involves the (m)-th digit of 10^alpha,
    which is essentially random (equidistributed) => P = 1/10.

    For the leading digit (j=m): this involves the 1st digit of 10^alpha,
    which is never 0 (since 10^alpha in [1, 10)) => P = 0.

    For digit j = m-k (k-th from top): the (k+1)-th digit of 10^alpha.
    For small k, this is constrained. For k=0 (leading): always nonzero.
    For k=1: digit 2 of 10^alpha. Since 10^alpha in [1,10), the second
    digit is 0 iff 10^alpha in [1.0, 1.1) union [2.0, 2.1) union ...
    = union_{d=1}^{9} [d, d+0.1) if floor(10*10^alpha) mod 10 = 0
    which means 10^{alpha+1} mod 10 in [0,1), i.e., 10^alpha in
    [1.0, 1.1) union [2.0, 2.1) union ... [9.0, 9.1).
    Measure = 9 * 0.1 / 9 = 0.1 in log-uniform measure... actually no.

    In Benford measure (log-uniform on [1, 10)):
    P(second digit = 0) = sum_{d=1}^{9} log10(1 + 1/(10d)) ~ 0.1197

    But our n is NOT random -- it's restricted to the 3-4 candidates
    with D(n) = m. So alpha = frac(n * log10(2)) for specific n.

    The actual question is deterministic, not probabilistic!
    For each n with D(n) = m, we can compute alpha = frac(n * log10(2))
    and determine exactly which digits are zero.

    What matters is: can we prove that for ALL n with D(n) = m and m >= 27,
    at least one digit of 2^n is zero?

    The transition zone has 3-4 candidates. Each corresponds to a specific
    alpha value. If these alpha values avoid the "all digits nonzero" region,
    we're done.
    """
    print("\n" + "=" * 100)
    print("PART D: Alpha Values and Digit Structure")
    print("  alpha = frac(n * log10(2)) for each candidate n")
    print("=" * 100)

    print(f"\n{'m':>4}  {'n':>6}  {'alpha':>12}  {'lead_digit':>10}  "
          f"{'d2':>4}  {'d3':>4}  {'d4':>4}  {'d5':>4}  "
          f"{'first_zero':>10}  {'zeroless':>8}")
    print("-" * 90)

    for m in range(3, min(max_m + 1, 80)):
        n_low = math.ceil((m - 1) / LOG10_2)
        n_high = math.ceil(m / LOG10_2) - 1

        for n in range(n_low, n_high + 1):
            if digit_count(n) != m:
                continue

            alpha = (n * LOG10_2) - math.floor(n * LOG10_2)
            val = pow(2, n)
            s = str(val)

            # Leading digits (from top)
            d1 = int(s[0])  # leading
            d2 = int(s[1]) if len(s) > 1 else -1
            d3 = int(s[2]) if len(s) > 2 else -1
            d4 = int(s[3]) if len(s) > 3 else -1
            d5 = int(s[4]) if len(s) > 4 else -1

            first_zero = None
            for pos, ch in enumerate(s):
                if ch == '0':
                    first_zero = pos + 1  # 1-indexed from left
                    break

            zeroless = '0' not in s
            zl_mark = "YES" if zeroless else "no"

            print(f"{m:>4}  {n:>6}  {alpha:>12.8f}  {d1:>10}  "
                  f"{d2:>4}  {d3:>4}  {d4:>4}  {d5:>4}  "
                  f"{str(first_zero):>10}  {zl_mark:>8}")


def part_E_zero_count_trend():
    """For candidates n with D(n) = m, how does the number of zero digits grow?

    If #zeros grows with m, finiteness follows immediately.
    """
    print("\n" + "=" * 100)
    print("PART E: Number of Zero Digits vs m")
    print("=" * 100)

    print(f"\n{'m':>4}  {'n':>6}  {'#zeros':>6}  {'#digits':>7}  "
          f"{'zero_frac':>10}  {'expected':>10}  {'ratio':>8}")
    print("-" * 70)

    for m in range(3, 80):
        n_low = math.ceil((m - 1) / LOG10_2)
        n_high = math.ceil(m / LOG10_2) - 1

        for n in range(n_low, n_high + 1):
            if digit_count(n) != m:
                continue

            val = pow(2, n)
            s = str(val)
            n_zeros = s.count('0')
            zero_frac = n_zeros / m
            expected_frac = 1 / 10
            ratio = zero_frac / expected_frac

            print(f"{m:>4}  {n:>6}  {n_zeros:>6}  {m:>7}  "
                  f"{zero_frac:>10.4f}  {expected_frac:>10.4f}  {ratio:>8.4f}")


def main():
    print("=" * 100)
    print("EXPERIMENT 20c: LEADING DIGIT BIAS AND BENFORD PREDICTION")
    print("=" * 100)
    print()

    t_start = time.time()

    part_A_exact_bias(max_m=15)
    part_B_extended_range(max_m=60)
    part_D_benford_prediction(max_m=30)
    part_E_zero_count_trend()

    total = time.time() - t_start
    print(f"\nTotal elapsed: {total:.1f}s")


if __name__ == '__main__':
    main()
