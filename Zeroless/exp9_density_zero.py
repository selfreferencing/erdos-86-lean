#!/usr/bin/env python3
"""
Experiment 9: Density-Zero via Conditional Survival Analysis

Decompose the zeroless property level-by-level along the actual orbit of 2^n
and test whether the survival product decays fast enough to prove density zero.

Sub-experiments:
A. Zeroless census and death-level histogram
B. Conditional survival rates S_m at each digit level
C. Per-n survival product comparison with heuristic
D. Orbit-position uniformity test
E. Sliding-window effective density
F. Correlation structure (autocorrelation of zeroless indicator)
G. Running count comparison Z(N) vs heuristic
"""

import sys
import os
import json
import time
import math
import numpy as np
from collections import Counter

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

# Maximum n to check
N_MAX = 50000


# ============================================================
# Helpers
# ============================================================

def is_fully_zeroless(x):
    """Check if x has no digit 0 in its decimal representation."""
    while x > 0:
        if x % 10 == 0:
            return False
        x //= 10
    return True


def first_zero_position(x):
    """Return position (1-indexed from right) of first digit 0, or 0 if none."""
    pos = 1
    while x > 0:
        if x % 10 == 0:
            return pos
        x //= 10
        pos += 1
    return 0


def digit_at_position(x, pos):
    """Return the digit at position pos (1-indexed from right)."""
    return (x // (10 ** (pos - 1))) % 10


def num_digits(n):
    """Number of digits of 2^n."""
    return int(math.floor(n * math.log10(2))) + 1


# ============================================================
# Part A: Zeroless census and death-level histogram
# ============================================================

def part_A():
    """For each n=1..N_MAX, find death level (which digit position has first 0)."""
    print("=" * 70)
    print("PART A: Zeroless Census and Death-Level Histogram")
    print("=" * 70)

    death_levels = []
    zeroless_ns = []
    power = 1  # 2^0 = 1

    for n in range(1, N_MAX + 1):
        power *= 2
        fzp = first_zero_position(power)
        if fzp == 0:
            # Fully zeroless
            zeroless_ns.append(n)
            death_levels.append(0)  # 0 means no death
        else:
            death_levels.append(fzp)

    # Death level histogram (for n > 86)
    death_after_86 = [d for i, d in enumerate(death_levels) if i >= 86 and d > 0]
    hist = Counter(death_after_86)

    print(f"\nTotal zeroless n in [1, {N_MAX}]: {len(zeroless_ns)}")
    print(f"Max zeroless n: {max(zeroless_ns) if zeroless_ns else 'none'}")
    print(f"\nDeath-level histogram (n > 86, position of first zero from right):")
    print(f"{'level':>6} {'count':>8} {'fraction':>10}")
    total = len(death_after_86)
    cumulative = 0
    for level in sorted(hist.keys()):
        frac = hist[level] / total
        cumulative += frac
        print(f"{level:6d} {hist[level]:8d} {frac:10.6f}  (cum: {cumulative:.6f})")
        if level > 20:
            break

    # Geometric distribution fit
    if death_after_86:
        mean_level = np.mean(death_after_86)
        print(f"\nMean death level: {mean_level:.4f}")
        print(f"Geometric parameter p (if geometric): p = 1/mean = {1/mean_level:.4f}")
        print(f"Expected p if digits were i.i.d.: 0.1 (since P(digit=0)=0.1)")
        print(f"Geometric mean prediction: 1/0.1 = 10.0")

    return death_levels, zeroless_ns


# ============================================================
# Part B: Conditional survival rates S_m at each digit level
# ============================================================

def part_B():
    """Compute S_m = P(digit m nonzero | digits 1..m-1 all nonzero) along orbit."""
    print("\n" + "=" * 70)
    print("PART B: Conditional Survival Rates S_m")
    print("=" * 70)

    max_level = 30
    # Count how many n have digits 1..m-1 all nonzero (survivors at level m-1)
    # and how many of those also have digit m nonzero (survivors at level m)
    survived_to = np.zeros(max_level + 1, dtype=int)  # survived_to[m] = count of n surviving to level m
    total_checked = np.zeros(max_level + 1, dtype=int)

    power = 1
    for n in range(1, N_MAX + 1):
        power *= 2
        k = num_digits(n)
        # Check each digit from right
        x = power
        all_nonzero = True
        for m in range(1, min(k, max_level) + 1):
            d = x % 10
            x //= 10
            if all_nonzero:
                total_checked[m] += 1
                if d != 0:
                    survived_to[m] += 1
                else:
                    all_nonzero = False

    print(f"\n{'level':>6} {'checked':>10} {'survived':>10} {'S_m':>10} {'1-S_m':>10}")
    print("-" * 50)
    survival_rates = {}
    for m in range(1, max_level + 1):
        if total_checked[m] > 0:
            sm = survived_to[m] / total_checked[m]
            survival_rates[m] = sm
            print(f"{m:6d} {total_checked[m]:10d} {survived_to[m]:10d} "
                  f"{sm:10.6f} {1 - sm:10.6f}")

    if survival_rates:
        vals = list(survival_rates.values())
        print(f"\nMean S_m: {np.mean(vals):.6f}")
        print(f"Std  S_m: {np.std(vals):.6f}")
        print(f"Min  S_m: {min(vals):.6f} at level {min(survival_rates, key=survival_rates.get)}")
        print(f"Max  S_m: {max(vals):.6f} at level {max(survival_rates, key=survival_rates.get)}")
        print(f"Expected S_m for random digits: 0.9")

    return survival_rates


# ============================================================
# Part C: Per-n survival product
# ============================================================

def part_C():
    """For each n, compute cumulative survival product and compare with (9/10)^k."""
    print("\n" + "=" * 70)
    print("PART C: Per-n Survival Product")
    print("=" * 70)

    # Track conditional survival rates as running averages
    max_level = 25
    level_counts = np.zeros(max_level + 1, dtype=int)
    level_survived = np.zeros(max_level + 1, dtype=int)

    # For selected n values, compute the survival product
    checkpoints = [100, 500, 1000, 5000, 10000, 20000, 50000]
    checkpoint_idx = 0

    power = 1
    for n in range(1, N_MAX + 1):
        power *= 2
        k = num_digits(n)
        x = power
        all_nonzero = True
        for m in range(1, min(k, max_level) + 1):
            d = x % 10
            x //= 10
            if all_nonzero:
                level_counts[m] += 1
                if d != 0:
                    level_survived[m] += 1
                else:
                    all_nonzero = False

        if checkpoint_idx < len(checkpoints) and n == checkpoints[checkpoint_idx]:
            # Compute survival product
            product = 1.0
            terms = 0
            for m in range(1, max_level + 1):
                if level_counts[m] > 10:
                    sm = level_survived[m] / level_counts[m]
                    product *= sm
                    terms += 1
            heuristic = 0.9 ** terms
            ratio = product / heuristic if heuristic > 0 else float('inf')
            print(f"  n={n:6d}: product(S_1..S_{terms}) = {product:.8e}, "
                  f"(0.9)^{terms} = {heuristic:.8e}, ratio = {ratio:.6f}")
            checkpoint_idx += 1

    # Final analysis
    print("\nFinal conditional survival rates by level:")
    for m in range(1, max_level + 1):
        if level_counts[m] > 0:
            sm = level_survived[m] / level_counts[m]
            print(f"  S_{m:2d} = {sm:.6f}  "
                  f"(deviation from 0.9: {sm - 0.9:+.6f})")


# ============================================================
# Part D: Orbit-position uniformity test
# ============================================================

def part_D():
    """Test uniformity of orbit positions among survivors at each level."""
    print("\n" + "=" * 70)
    print("PART D: Orbit-Position Uniformity Test")
    print("=" * 70)

    max_level = 12

    for m in range(2, max_level + 1):
        mod = 10 ** m
        mod_prev = 10 ** (m - 1)
        period = 4 * (5 ** (m - 1))

        # Enumerate orbit and find survivors at level m-1
        survivors_prev = []
        x = 1
        for n in range(period):
            if n > 0:
                x = (2 * x) % mod
            # Check if last m-1 digits are all nonzero
            is_surv = True
            y = x
            for _ in range(m - 1):
                if y % 10 == 0:
                    is_surv = False
                    break
                y //= 10
            if is_surv:
                survivors_prev.append((n, x))

        if not survivors_prev:
            continue

        # For each survivor at m-1, check digit at position m
        digit_counts = Counter()
        survived_count = 0
        for n, val in survivors_prev:
            dm = digit_at_position(val, m)
            digit_counts[dm] += 1
            if dm != 0:
                survived_count += 1

        total = len(survivors_prev)
        s_m = survived_count / total if total > 0 else 0

        # Chi-squared test for uniformity of digit m among survivors
        expected = total / 10  # uniform would give each digit with prob 1/10
        chi2 = sum((digit_counts.get(d, 0) - expected) ** 2 / expected
                    for d in range(10))
        # For 9 degrees of freedom, chi2 > 16.92 is significant at 5%

        print(f"\n  Level m={m}: {total} survivors at m-1, "
              f"{survived_count} survive to m (S_m={s_m:.6f})")
        print(f"    Digit distribution at position {m}: "
              f"{{d: digit_counts.get(d, 0) for d in range(10)}}")
        digits_str = " ".join(f"{d}:{digit_counts.get(d, 0)}" for d in range(10))
        print(f"    {digits_str}")
        print(f"    Chi-squared (vs uniform): {chi2:.2f} "
              f"({'SIGNIFICANT' if chi2 > 16.92 else 'not significant'} at 5%)")
        print(f"    Zero digit fraction: {digit_counts.get(0, 0) / total:.6f} "
              f"(expected 0.1)")


# ============================================================
# Part E: Sliding-window effective density
# ============================================================

def part_E(zeroless_ns):
    """Compute sliding-window density of zeroless powers."""
    print("\n" + "=" * 70)
    print("PART E: Sliding-Window Effective Density")
    print("=" * 70)

    zeroless_set = set(zeroless_ns)

    for W in [100, 500, 1000, 5000]:
        print(f"\nWindow size W={W}:")
        densities = []
        for start in range(1, N_MAX - W + 1, W):
            count = sum(1 for n in range(start, start + W) if n in zeroless_set)
            density = count / W
            densities.append((start, density))

        # Print summary
        d_vals = [d for _, d in densities]
        if d_vals:
            print(f"  Windows: {len(d_vals)}")
            print(f"  First window [{densities[0][0]}, {densities[0][0]+W}): "
                  f"density = {densities[0][1]:.6f}")
            if len(densities) > 1:
                print(f"  Last window [{densities[-1][0]}, {densities[-1][0]+W}): "
                      f"density = {densities[-1][1]:.6f}")
            # Density at selected points
            for start, d in densities:
                if start in [1, 101, 501, 1001, 5001, 10001, 20001, 40001]:
                    print(f"    [{start:6d}, {start + W:6d}): {d:.6f}")

        # After n=86, density should be 0
        post86 = [d for s, d in densities if s > 86]
        if post86:
            nonzero_windows = sum(1 for d in post86 if d > 0)
            print(f"  Windows after n=86 with nonzero density: "
                  f"{nonzero_windows}/{len(post86)}")


# ============================================================
# Part F: Correlation structure
# ============================================================

def part_F():
    """Autocorrelation of k-digit-zeroless indicator along the orbit."""
    print("\n" + "=" * 70)
    print("PART F: Correlation Structure")
    print("=" * 70)

    # For several values of k, compute autocorrelation of the indicator
    # I_k(n) = 1 if last k digits of 2^n are all nonzero

    for k in [3, 5, 7, 9, 11]:
        mod = 10 ** k
        period = 4 * (5 ** (k - 1))
        if period > 2000000:
            print(f"\n  k={k}: period={period} too large, skipping")
            continue

        # Build indicator sequence
        indicator = np.zeros(period, dtype=int)
        x = 1
        for n in range(period):
            # Check zeroless
            zl = True
            y = x
            for _ in range(k):
                if y % 10 == 0:
                    zl = False
                    break
                y //= 10
            indicator[n] = 1 if zl else 0
            x = (2 * x) % mod

        mean_I = indicator.mean()
        print(f"\n  k={k}: period={period}, P(zeroless)={mean_I:.6f}, "
              f"(0.9)^{k}={(0.9**k):.6f}, ratio={mean_I/(0.9**k):.6f}")

        # Autocorrelation at small lags
        max_lag = min(20, period // 10)
        print(f"    Autocorrelation (lags 1..{max_lag}):")
        centered = indicator.astype(float) - mean_I
        var = np.sum(centered ** 2)
        if var > 0:
            for lag in range(1, max_lag + 1):
                corr = np.sum(centered[:period - lag] * centered[lag:]) / var
                print(f"      lag {lag:3d}: {corr:+.6f}")


# ============================================================
# Part G: Running count comparison
# ============================================================

def part_G(zeroless_ns):
    """Compare Z(N) = #{n <= N : zeroless} with heuristic prediction."""
    print("\n" + "=" * 70)
    print("PART G: Running Count Z(N) vs Heuristic")
    print("=" * 70)

    zeroless_set = set(zeroless_ns)

    # Heuristic: sum_{n=1}^N (9/10)^{k(n)} where k(n) = number of digits of 2^n
    print(f"\n{'N':>8} {'Z(N)':>8} {'Heur':>10} {'Z/Heur':>8} {'Z/N':>10}")
    print("-" * 48)

    z = 0
    heur = 0.0
    checkpoints = [10, 20, 50, 86, 87, 100, 200, 500, 1000, 2000,
                    5000, 10000, 20000, 50000]

    for n in range(1, N_MAX + 1):
        if n in zeroless_set:
            z += 1
        k = num_digits(n)
        heur += 0.9 ** k

        if n in checkpoints:
            ratio_h = z / heur if heur > 0 else float('inf')
            ratio_n = z / n
            print(f"{n:8d} {z:8d} {heur:10.4f} {ratio_h:8.4f} {ratio_n:10.6f}")

    print(f"\nFinal: Z({N_MAX}) = {z}")
    print(f"Heuristic sum = {heur:.4f}")
    print(f"The heuristic sum converges (it's a convergent series)")
    print(f"  because (0.9)^k with k ~ 0.301*n gives a geometric series in n.")
    print(f"Sum formula: sum (0.9)^(0.301*n) = sum (0.9^0.301)^n "
          f"= sum {0.9**0.301:.6f}^n")
    r = 0.9 ** 0.301
    print(f"  Ratio = {r:.6f}, geometric sum = {r / (1 - r):.4f}")
    print(f"\nIf Z(N) is bounded, density = Z(N)/N -> 0.")
    print(f"Z({N_MAX})/{N_MAX} = {z / N_MAX:.6f}")


# ============================================================
# Main
# ============================================================

def main():
    print("Experiment 9: Density-Zero via Conditional Survival Analysis")
    print("=" * 70)
    print(f"Scanning n = 1..{N_MAX}")
    print()

    t0 = time.time()
    death_levels, zeroless_ns = part_A()
    print(f"\n  [Part A: {time.time() - t0:.1f}s]")

    t0 = time.time()
    survival_rates = part_B()
    print(f"\n  [Part B: {time.time() - t0:.1f}s]")

    t0 = time.time()
    part_C()
    print(f"\n  [Part C: {time.time() - t0:.1f}s]")

    t0 = time.time()
    part_D()
    print(f"\n  [Part D: {time.time() - t0:.1f}s]")

    t0 = time.time()
    part_E(zeroless_ns)
    print(f"\n  [Part E: {time.time() - t0:.1f}s]")

    t0 = time.time()
    part_F()
    print(f"\n  [Part F: {time.time() - t0:.1f}s]")

    t0 = time.time()
    part_G(zeroless_ns)
    print(f"\n  [Part G: {time.time() - t0:.1f}s]")

    # Save results
    output = {
        'N_MAX': N_MAX,
        'zeroless_count': len(zeroless_ns),
        'max_zeroless': max(zeroless_ns) if zeroless_ns else 0,
        'zeroless_ns': zeroless_ns,
        'survival_rates': {str(k): v for k, v in survival_rates.items()},
        'death_level_histogram': dict(Counter(
            d for d in death_levels if d > 0
        )),
    }

    path = os.path.join(DATA_DIR, "exp9_results.json")
    with open(path, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\n\nResults saved to {path}")

    # Final summary
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    print(f"\n1. Zeroless powers: {len(zeroless_ns)} total, max n = "
          f"{max(zeroless_ns) if zeroless_ns else 'none'}")
    print(f"2. After n=86: ZERO zeroless powers in {N_MAX - 86} checked")
    print(f"3. Density Z(N)/N = {len(zeroless_ns)}/{N_MAX} = "
          f"{len(zeroless_ns)/N_MAX:.6f}")
    print(f"4. Mean conditional survival rate: "
          f"{np.mean(list(survival_rates.values())):.6f} (expected ~0.9)")
    print(f"5. Heuristic predicts bounded Z(N), consistent with density zero")


if __name__ == "__main__":
    main()
