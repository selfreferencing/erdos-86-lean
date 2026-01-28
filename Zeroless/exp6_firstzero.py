#!/usr/bin/env python3
import sys
sys.set_int_max_str_digits(100000)
"""
EXPERIMENT 6: First-Zero Position Deep Analysis

Synthesis motivation: M3-B2's computational analysis of j(n), the position of the
first zero digit from the right in 2^n. Verify and extend.

Computes:
- j(n) for n = 87..50000
- Distribution statistics, geometric fit
- Correlation of j(n) with n mod 4*5^m
- Autocorrelation of j(n) sequence
- Record-value growth
- Relative position j(n)/k(n) distribution
"""

import numpy as np
import os
import json
from collections import defaultdict

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


def first_zero_from_right(n):
    """
    Position of first zero digit from the right (1-indexed) in 2^n.
    Returns 0 if 2^n has no zero digit (only for small n).
    """
    s = str(pow(2, n))
    for pos, ch in enumerate(reversed(s)):
        if ch == '0':
            return pos + 1  # 1-indexed
    return 0  # No zero found (2^n is zeroless)


def test1_basic_statistics():
    """Basic j(n) statistics for n = 87..50000."""
    print("=" * 70)
    print("TEST 1: Basic j(n) statistics")
    print("=" * 70)

    max_n = 50000
    j_values = []
    n_values = []

    for n in range(87, max_n + 1):
        j = first_zero_from_right(n)
        j_values.append(j)
        n_values.append(n)

    j_arr = np.array(j_values)

    print(f"\nj(n) statistics for n = 87..{max_n} ({len(j_arr)} values):")
    print(f"  Mean:   {j_arr.mean():.4f}")
    print(f"  Median: {np.median(j_arr):.1f}")
    print(f"  Std:    {j_arr.std():.4f}")
    print(f"  Max:    {j_arr.max()} at n={n_values[j_arr.argmax()]}")
    print(f"  Min:    {j_arr.min()}")

    percentiles = [1, 5, 10, 25, 50, 75, 90, 95, 99]
    print(f"\n  Percentiles:")
    for p in percentiles:
        print(f"    {p}th: {np.percentile(j_arr, p):.1f}")

    # Histogram
    max_j = min(50, int(j_arr.max()))
    print(f"\n  Distribution (j = 1..{max_j}):")
    hist, _ = np.histogram(j_arr, bins=range(1, max_j + 2))
    for j_val in range(1, max_j + 1):
        count = hist[j_val - 1]
        frac = count / len(j_arr)
        bar = '#' * int(frac * 200)
        print(f"    j={j_val:3d}: {count:6d} ({frac:.4f}) {bar}")

    return j_values, n_values


def test2_geometric_fit(j_values):
    """Fit j(n) to geometric distribution."""
    print("\n" + "=" * 70)
    print("TEST 2: Geometric distribution fit")
    print("=" * 70)

    j_arr = np.array(j_values)

    # For geometric distribution with parameter p:
    # P(j = k) = (1-p)^{k-1} * p
    # E[j] = 1/p => p = 1/mean
    # If digit=0 probability is ~1/10, then p = 1/10 and E[j] = 10

    mean_j = j_arr.mean()
    p_estimate = 1.0 / mean_j

    print(f"\n  Estimated p from mean: {p_estimate:.6f} (expected: 0.1)")
    print(f"  Mean j: {mean_j:.4f} (expected for geometric(0.1): 10.0)")

    # Compare observed vs geometric frequencies
    print(f"\n  Observed vs Geometric(p={p_estimate:.4f}) frequencies:")
    print(f"  {'j':>4}  {'observed':>10}  {'geometric':>10}  {'ratio':>8}")
    print("  " + "-" * 40)

    for j_val in range(1, 31):
        observed = np.sum(j_arr == j_val) / len(j_arr)
        geometric = (1 - p_estimate) ** (j_val - 1) * p_estimate
        ratio = observed / geometric if geometric > 0 else 0
        print(f"  {j_val:4d}  {observed:10.6f}  {geometric:10.6f}  {ratio:8.4f}")

    # Also fit against p = 0.1 exactly
    print(f"\n  Observed vs Geometric(p=0.1) frequencies:")
    print(f"  {'j':>4}  {'observed':>10}  {'geo(0.1)':>10}  {'ratio':>8}")
    print("  " + "-" * 40)

    for j_val in range(1, 31):
        observed = np.sum(j_arr == j_val) / len(j_arr)
        geometric = 0.9 ** (j_val - 1) * 0.1
        ratio = observed / geometric if geometric > 0 else 0
        print(f"  {j_val:4d}  {observed:10.6f}  {geometric:10.6f}  {ratio:8.4f}")

    # Chi-squared test (manual)
    n_total = len(j_arr)
    chi2 = 0
    for j_val in range(1, 51):
        observed = np.sum(j_arr == j_val)
        expected = n_total * 0.9 ** (j_val - 1) * 0.1
        if expected > 5:
            chi2 += (observed - expected) ** 2 / expected
    print(f"\n  Chi-squared (j=1..50, vs geometric(0.1)): {chi2:.2f}")
    print(f"  Degrees of freedom: ~48")
    print(f"  Chi2/df: {chi2/48:.2f} (should be ~1 for good fit)")


def test3_modular_correlation(j_values, n_values):
    """Correlation of j(n) with n mod T_k for various k."""
    print("\n" + "=" * 70)
    print("TEST 3: Correlation with modular structure")
    print("=" * 70)

    j_arr = np.array(j_values)
    n_arr = np.array(n_values)

    for k in range(1, 8):
        period = 4 * (5 ** (k - 1))
        residues = n_arr % period

        # For each residue class, compute mean j
        residue_means = defaultdict(list)
        for i, n in enumerate(n_arr):
            residue_means[n % period].append(j_values[i])

        # Compute variance of residue-class means
        class_means = [np.mean(v) for v in residue_means.values() if len(v) > 10]
        grand_mean = j_arr.mean()
        between_var = np.var(class_means) if class_means else 0
        total_var = np.var(j_arr)
        eta_squared = between_var / total_var if total_var > 0 else 0

        # Top and bottom residue classes
        sorted_classes = sorted(residue_means.items(),
                                key=lambda x: np.mean(x[1]) if len(x[1]) > 10 else 0,
                                reverse=True)

        print(f"\n  k={k}: period T_k = {period}")
        print(f"    Number of residue classes with >10 samples: {len(class_means)}")
        print(f"    Grand mean j: {grand_mean:.4f}")
        print(f"    Between-class variance / total variance (eta^2): {eta_squared:.6f}")

        if sorted_classes:
            top = sorted_classes[0]
            bot = sorted_classes[-1]
            if len(top[1]) > 10 and len(bot[1]) > 10:
                print(f"    Highest mean: residue {top[0]} -> mean j = {np.mean(top[1]):.2f} (n={len(top[1])})")
                print(f"    Lowest mean:  residue {bot[0]} -> mean j = {np.mean(bot[1]):.2f} (n={len(bot[1])})")


def test4_autocorrelation(j_values):
    """Autocorrelation of the j(n) sequence."""
    print("\n" + "=" * 70)
    print("TEST 4: Autocorrelation of j(n)")
    print("=" * 70)

    j_arr = np.array(j_values, dtype=float)
    j_centered = j_arr - j_arr.mean()
    var_j = np.var(j_arr)

    max_lag = 100
    print(f"\n  Autocorrelation of j(n) sequence (lag 1..{max_lag}):")
    print(f"  {'lag':>4}  {'autocorr':>10}")
    print("  " + "-" * 20)

    for lag in range(1, max_lag + 1):
        n = len(j_centered) - lag
        autocorr = np.sum(j_centered[:n] * j_centered[lag:lag + n]) / (n * var_j)
        if lag <= 20 or lag % 10 == 0:
            print(f"  {lag:4d}  {autocorr:10.6f}")


def test5_record_growth(j_values, n_values):
    """Track record values of j(n) and their growth rate."""
    print("\n" + "=" * 70)
    print("TEST 5: Record value growth")
    print("=" * 70)

    current_max = 0
    records = []

    for i, j in enumerate(j_values):
        if j > current_max:
            current_max = j
            records.append((n_values[i], j))

    print(f"\n  Record j(n) values:")
    print(f"  {'n':>8}  {'j(n)':>6}  {'log(n)':>8}")
    print("  " + "-" * 30)
    for n, j in records:
        print(f"  {n:8d}  {j:6d}  {np.log(n):.4f}")

    # Check if max j grows like log(n)
    if len(records) > 5:
        ns = np.array([r[0] for r in records])
        js = np.array([r[1] for r in records])
        log_ns = np.log(ns)

        fit = np.polyfit(log_ns, js, 1)
        print(f"\n  Linear fit: max_j ~ {fit[0]:.2f} * log(n) + {fit[1]:.2f}")
        print(f"  Expected for geometric: max_j ~ 10 * log(n)/log(10/9)")
        expected_slope = 10 / np.log(10 / 9)
        print(f"  Expected slope: {expected_slope:.2f}")
        print(f"  Actual slope: {fit[0]:.2f}")
        print(f"  Ratio: {fit[0] / expected_slope:.4f}")


def test6_relative_position(n_values, j_values):
    """Distribution of j(n)/k(n) where k(n) is the digit count of 2^n."""
    print("\n" + "=" * 70)
    print("TEST 6: Relative position j(n)/k(n)")
    print("=" * 70)

    ratios = []
    for i, n in enumerate(n_values):
        k = len(str(pow(2, n)))
        j = j_values[i]
        ratios.append(j / k)

    r_arr = np.array(ratios)
    print(f"\n  j(n)/k(n) statistics:")
    print(f"    Mean:   {r_arr.mean():.6f}")
    print(f"    Median: {np.median(r_arr):.6f}")
    print(f"    Std:    {r_arr.std():.6f}")
    print(f"    Max:    {r_arr.max():.6f}")

    # If j is geometric(0.1) and k ~ 0.301*n, then j/k ~ geometric(0.1)/(0.301*n)
    # For large n, j/k -> 0 since j is O(1) while k grows linearly

    # Distribution of j/k
    print(f"\n  j(n)/k(n) percentiles:")
    for p in [1, 5, 10, 25, 50, 75, 90, 95, 99]:
        print(f"    {p}th: {np.percentile(r_arr, p):.6f}")


def test7_consecutive_j_analysis(j_values, n_values):
    """
    Look at j(n) vs j(n+1). Since 2^{n+1} = 2*2^n, there's a structural
    relationship between their digit patterns.
    """
    print("\n" + "=" * 70)
    print("TEST 7: j(n) vs j(n+1) relationship")
    print("=" * 70)

    # Need consecutive n values
    j_by_n = {}
    for i, n in enumerate(n_values):
        j_by_n[n] = j_values[i]

    pairs = []
    for n in sorted(j_by_n.keys()):
        if n + 1 in j_by_n:
            pairs.append((j_by_n[n], j_by_n[n + 1]))

    if len(pairs) < 10:
        print("  Not enough consecutive pairs")
        return

    j1 = np.array([p[0] for p in pairs])
    j2 = np.array([p[1] for p in pairs])

    corr = np.corrcoef(j1, j2)[0, 1]
    print(f"\n  Correlation between j(n) and j(n+1): {corr:.6f}")

    # Conditional: when j(n) is large, what is j(n+1)?
    print(f"\n  Mean j(n+1) conditioned on j(n):")
    for j_cond in range(1, 11):
        mask = j1 == j_cond
        if mask.sum() > 10:
            print(f"    j(n)={j_cond}: mean j(n+1) = {j2[mask].mean():.4f} (n={mask.sum()})")

    # When j(n) is large (say >= 10), is j(n+1) also large?
    large_mask = j1 >= 10
    if large_mask.sum() > 0:
        print(f"\n  When j(n) >= 10 ({large_mask.sum()} cases):")
        print(f"    Mean j(n+1): {j2[large_mask].mean():.4f}")
        print(f"    P(j(n+1) >= 10): {(j2[large_mask] >= 10).sum() / large_mask.sum():.4f}")


if __name__ == "__main__":
    print("EXPERIMENT 6: FIRST-ZERO POSITION DEEP ANALYSIS")
    print("=" * 70)

    j_values, n_values = test1_basic_statistics()
    test2_geometric_fit(j_values)
    test3_modular_correlation(j_values, n_values)
    test4_autocorrelation(j_values)
    test5_record_growth(j_values, n_values)
    test6_relative_position(n_values, j_values)
    test7_consecutive_j_analysis(j_values, n_values)

    # Save results
    output = {
        'mean_j': float(np.mean(j_values)),
        'max_j': int(np.max(j_values)),
        'max_j_at_n': int(n_values[np.argmax(j_values)]),
    }
    with open(os.path.join(DATA_DIR, "exp6_results.json"), 'w') as f:
        json.dump(output, f, indent=2)

    print(f"\n{'='*70}")
    print("EXPERIMENT 6 COMPLETE")
    print(f"{'='*70}")
