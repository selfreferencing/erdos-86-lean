#!/usr/bin/env python3
import sys
sys.set_int_max_str_digits(100000)
"""
EXPERIMENT 5: Global Carry Invariant Search

Synthesis motivation: Global carry forcing (Shape C in M4-B), ranked as
"most plausible structural proof shape."

For each n, compute the full carry chain when doubling 2^{n-1} to get 2^n,
and search for global invariants that distinguish zeroless powers.
"""

import numpy as np
import os
import json
from collections import defaultdict

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


def get_carry_chain(n):
    """
    Compute the carry chain when doubling 2^{n-1} to get 2^n.
    Returns (digits_prev, digits_result, carries) all LSB-first.
    """
    prev = pow(2, n - 1)
    prev_digits = [int(c) for c in str(prev)][::-1]

    carry = 0
    result_digits = []
    carries = []

    for d in prev_digits:
        s = 2 * d + carry
        result_digits.append(s % 10)
        carry = s // 10
        carries.append(carry)

    if carry > 0:
        result_digits.append(carry)
        carries.append(0)  # No further carry

    return prev_digits, result_digits, carries


def is_zeroless_digits(digits):
    """Check if digit list (LSB first) has no zeros."""
    return all(d != 0 for d in digits)


def digit_stats(digits):
    """Compute statistics of a digit list."""
    d = np.array(digits)
    return {
        'mean': float(d.mean()),
        'std': float(d.std()),
        'min': int(d.min()),
        'max': int(d.max()),
        'zeros': int(np.sum(d == 0)),
        'entropy': float(-np.sum(np.array([np.sum(d == i) for i in range(10)]) / len(d) *
                                  np.log2(np.array([max(np.sum(d == i), 1) for i in range(10)]) / len(d)))),
    }


def test1_carry_statistics():
    """
    For each n, compute carry chain statistics and compare zeroless vs non-zeroless.
    """
    print("=" * 70)
    print("TEST 1: Carry chain statistics per power of 2")
    print("=" * 70)

    max_n = 5000

    # Track statistics
    stats_data = []

    for n in range(2, max_n + 1):
        prev_digits, result_digits, carries = get_carry_chain(n)
        k = len(result_digits)

        is_zl = is_zeroless_digits(result_digits)
        carry_arr = np.array(carries[:-1]) if len(carries) > 1 else np.array(carries)

        # Carry statistics
        total_carries = int(np.sum(carry_arr))
        carry_density = total_carries / len(carry_arr) if len(carry_arr) > 0 else 0

        # Carry runs
        run_lengths = []
        current_run = 1
        for i in range(1, len(carry_arr)):
            if carry_arr[i] == carry_arr[i - 1]:
                current_run += 1
            else:
                run_lengths.append(current_run)
                current_run = 1
        run_lengths.append(current_run)
        max_run = max(run_lengths) if run_lengths else 0

        # Carry transitions
        transitions = 0
        for i in range(1, len(carry_arr)):
            if carry_arr[i] != carry_arr[i - 1]:
                transitions += 1
        transition_density = transitions / (len(carry_arr) - 1) if len(carry_arr) > 1 else 0

        # Digit statistics
        d_arr = np.array(result_digits)
        digit_sum = int(d_arr.sum())
        zero_count = int(np.sum(d_arr == 0))

        stats_data.append({
            'n': n,
            'k': k,
            'is_zeroless': is_zl,
            'carry_density': carry_density,
            'max_carry_run': max_run,
            'transition_density': transition_density,
            'digit_sum': digit_sum,
            'zero_count': zero_count,
        })

    # Analyze: compare zeroless vs non-zeroless
    zl_stats = [s for s in stats_data if s['is_zeroless']]
    nzl_stats = [s for s in stats_data if not s['is_zeroless']]

    print(f"\nZeroless powers (n <= 86): {len(zl_stats)} values")
    print(f"Non-zeroless powers: {len(nzl_stats)} values")

    metrics = ['carry_density', 'max_carry_run', 'transition_density', 'digit_sum']
    for metric in metrics:
        zl_vals = [s[metric] for s in zl_stats if s['k'] > 3]  # Skip very small
        nzl_vals = [s[metric] for s in nzl_stats]

        if zl_vals and nzl_vals:
            print(f"\n  {metric}:")
            print(f"    Zeroless:     mean={np.mean(zl_vals):.4f}, std={np.std(zl_vals):.4f}, "
                  f"range=[{min(zl_vals):.4f}, {max(zl_vals):.4f}]")
            print(f"    Non-zeroless: mean={np.mean(nzl_vals):.4f}, std={np.std(nzl_vals):.4f}, "
                  f"range=[{min(nzl_vals):.4f}, {max(nzl_vals):.4f}]")

    return stats_data


def test2_monotone_quantities():
    """
    Search for quantities that are monotone with n (or with k = digit count).
    """
    print("\n" + "=" * 70)
    print("TEST 2: Searching for monotone quantities")
    print("=" * 70)

    max_n = 10000

    # Track running max/min of various quantities
    carry_density_max = 0
    carry_density_min = 1
    transition_density_max = 0
    max_run_max = 0

    # For each digit count k, track mean values
    by_k = defaultdict(list)

    for n in range(2, max_n + 1):
        prev_digits, result_digits, carries = get_carry_chain(n)
        k = len(result_digits)
        carry_arr = np.array(carries[:-1]) if len(carries) > 1 else np.array(carries)

        cd = np.mean(carry_arr) if len(carry_arr) > 0 else 0

        transitions = sum(1 for i in range(1, len(carry_arr)) if carry_arr[i] != carry_arr[i - 1])
        td = transitions / (len(carry_arr) - 1) if len(carry_arr) > 1 else 0

        run_lengths = []
        current_run = 1
        for i in range(1, len(carry_arr)):
            if carry_arr[i] == carry_arr[i - 1]:
                current_run += 1
            else:
                run_lengths.append(current_run)
                current_run = 1
        run_lengths.append(current_run)
        mr = max(run_lengths) if run_lengths else 0

        carry_density_max = max(carry_density_max, cd)
        carry_density_min = min(carry_density_min, cd)
        transition_density_max = max(transition_density_max, td)
        max_run_max = max(max_run_max, mr)

        by_k[k].append({
            'n': n,
            'carry_density': cd,
            'transition_density': td,
            'max_run': mr,
        })

    print(f"\n  Overall ranges (n=2..{max_n}):")
    print(f"    Carry density: [{carry_density_min:.4f}, {carry_density_max:.4f}]")
    print(f"    Transition density: [0, {transition_density_max:.4f}]")
    print(f"    Max carry run: [1, {max_run_max}]")

    print(f"\n  By digit count k (mean +/- std):")
    print(f"  {'k':>4}  {'n_count':>8}  {'carry_dens':>12}  {'trans_dens':>12}  {'max_run':>10}")
    print("  " + "-" * 52)

    for k in sorted(by_k.keys()):
        if len(by_k[k]) < 3:
            continue
        cd_vals = [s['carry_density'] for s in by_k[k]]
        td_vals = [s['transition_density'] for s in by_k[k]]
        mr_vals = [s['max_run'] for s in by_k[k]]
        print(f"  {k:4d}  {len(by_k[k]):8d}  {np.mean(cd_vals):8.4f}+/-{np.std(cd_vals):.4f}  "
              f"{np.mean(td_vals):8.4f}+/-{np.std(td_vals):.4f}  {np.mean(mr_vals):6.2f}+/-{np.std(mr_vals):.2f}")


def test3_carry_avalanche_analysis():
    """
    Analyze "carry avalanches" -- long consecutive runs of carries.
    These are the mechanism by which zeros propagate or are created.
    """
    print("\n" + "=" * 70)
    print("TEST 3: Carry avalanche analysis")
    print("=" * 70)

    max_n = 10000
    avalanche_counts = defaultdict(int)  # n -> number of avalanches (runs >= 5)
    max_avalanches = []

    for n in range(2, max_n + 1):
        _, result_digits, carries = get_carry_chain(n)
        carry_arr = carries[:-1] if len(carries) > 1 else carries

        # Find runs of carry=1
        run_len = 0
        avalanches = 0
        max_aval = 0
        for c in carry_arr:
            if c == 1:
                run_len += 1
            else:
                if run_len >= 5:
                    avalanches += 1
                max_aval = max(max_aval, run_len)
                run_len = 0
        if run_len >= 5:
            avalanches += 1
        max_aval = max(max_aval, run_len)

        avalanche_counts[n] = avalanches
        max_avalanches.append(max_aval)

    print(f"\nAvalanche (carry=1 run >= 5) statistics for n=2..{max_n}:")
    aval_arr = np.array([avalanche_counts[n] for n in range(2, max_n + 1)])
    print(f"  Mean avalanches per doubling: {aval_arr.mean():.4f}")
    print(f"  Max avalanches: {aval_arr.max()}")

    max_aval_arr = np.array(max_avalanches)
    print(f"\n  Max carry run length statistics:")
    print(f"  Mean: {max_aval_arr.mean():.4f}")
    print(f"  Max: {max_aval_arr.max()}")

    # Check if zeroless powers have distinctive avalanche patterns
    zl_n = set(range(0, 87)) | {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19,
                                  24, 25, 27, 28, 31, 32, 33, 34, 35, 36, 37, 39, 49, 51,
                                  67, 72, 76, 77, 81, 86}
    zl_aval = [avalanche_counts[n] for n in range(2, max_n + 1) if n in zl_n]
    nzl_aval = [avalanche_counts[n] for n in range(87, max_n + 1)]

    if zl_aval and nzl_aval:
        print(f"\n  Zeroless powers (n in E): mean avalanches = {np.mean(zl_aval):.4f}")
        print(f"  Non-zeroless (n >= 87): mean avalanches = {np.mean(nzl_aval):.4f}")


def test4_digit_sum_constraint():
    """
    For zeroless 2^n, digit sum >= k (each digit >= 1).
    Check if this gives any useful constraint combined with known
    digit sum properties of 2^n.
    """
    print("\n" + "=" * 70)
    print("TEST 4: Digit sum analysis")
    print("=" * 70)

    max_n = 10000

    print(f"\n  Digit sum of 2^n vs digit count k:")
    print(f"  {'n':>6}  {'k':>4}  {'dsum':>6}  {'dsum/k':>8}  {'zeroless':>10}")
    print("  " + "-" * 40)

    dsum_over_k = []
    dsum_over_k_zl = []

    for n in range(1, max_n + 1):
        val = pow(2, n)
        s = str(val)
        k = len(s)
        dsum = sum(int(c) for c in s)
        is_zl = '0' not in s

        ratio = dsum / k
        dsum_over_k.append(ratio)
        if is_zl:
            dsum_over_k_zl.append(ratio)

        if n <= 90 or (is_zl and n > 86):
            print(f"  {n:6d}  {k:4d}  {dsum:6d}  {ratio:8.4f}  {'YES' if is_zl else 'no'}")

    dok = np.array(dsum_over_k)
    print(f"\n  digit_sum / digit_count statistics (n=1..{max_n}):")
    print(f"    All:      mean={dok.mean():.4f}, std={dok.std():.4f}")
    if dsum_over_k_zl:
        dok_zl = np.array(dsum_over_k_zl)
        print(f"    Zeroless: mean={dok_zl.mean():.4f}, std={dok_zl.std():.4f}")
    print(f"    Expected (random digits): 4.5")
    print(f"    Minimum for zeroless: 1.0 (all digits = 1)")


def test5_combined_invariant():
    """
    Search for a combined invariant that separates zeroless from non-zeroless.
    Test: carry_density * digit_count or similar products.
    """
    print("\n" + "=" * 70)
    print("TEST 5: Combined invariant search")
    print("=" * 70)

    max_n = 5000

    zl_data = []
    nzl_data = []

    for n in range(10, max_n + 1):
        prev_digits, result_digits, carries = get_carry_chain(n)
        k = len(result_digits)
        carry_arr = np.array(carries[:-1]) if len(carries) > 1 else np.array(carries)

        cd = float(np.mean(carry_arr)) if len(carry_arr) > 0 else 0
        is_zl = is_zeroless_digits(result_digits)

        # Various candidate invariants
        d_arr = np.array(result_digits)
        dsum = float(d_arr.sum())
        dmin = int(d_arr.min())
        dprod_log = float(np.sum(np.log(d_arr[d_arr > 0] + 0.1)))  # log product of nonzero digits

        transitions = sum(1 for i in range(1, len(carry_arr)) if carry_arr[i] != carry_arr[i - 1])
        td = transitions / (len(carry_arr) - 1) if len(carry_arr) > 1 else 0

        entry = {
            'n': n, 'k': k,
            'carry_density': cd,
            'transition_density': td,
            'digit_sum': dsum,
            'digit_min': dmin,
            'log_digit_product': dprod_log,
            'Q1': cd * k,  # carry_density * digit_count
            'Q2': td * k,  # transition_density * digit_count
            'Q3': dsum / k,  # digit_sum / digit_count
        }

        if is_zl:
            zl_data.append(entry)
        else:
            nzl_data.append(entry)

    # Check each candidate invariant
    candidates = ['carry_density', 'transition_density', 'Q1', 'Q2', 'Q3', 'log_digit_product']

    for cand in candidates:
        zl_vals = [e[cand] for e in zl_data]
        nzl_vals = [e[cand] for e in nzl_data]

        if not zl_vals or not nzl_vals:
            continue

        zl_min = min(zl_vals)
        zl_max = max(zl_vals)
        nzl_min = min(nzl_vals)
        nzl_max = max(nzl_vals)

        # Check for separation
        separated = zl_max < nzl_min or nzl_max < zl_min
        overlap = not separated

        print(f"\n  {cand}:")
        print(f"    Zeroless: [{zl_min:.4f}, {zl_max:.4f}] (mean {np.mean(zl_vals):.4f})")
        print(f"    Non-zl:   [{nzl_min:.4f}, {nzl_max:.4f}] (mean {np.mean(nzl_vals):.4f})")
        print(f"    Separated: {separated}")
        if not separated:
            # Measure overlap
            overlap_lo = max(zl_min, nzl_min)
            overlap_hi = min(zl_max, nzl_max)
            print(f"    Overlap region: [{overlap_lo:.4f}, {overlap_hi:.4f}]")


if __name__ == "__main__":
    print("EXPERIMENT 5: GLOBAL CARRY INVARIANT SEARCH")
    print("=" * 70)

    stats = test1_carry_statistics()
    test2_monotone_quantities()
    test3_carry_avalanche_analysis()
    test4_digit_sum_constraint()
    test5_combined_invariant()

    print(f"\n{'='*70}")
    print("EXPERIMENT 5 COMPLETE")
    print(f"{'='*70}")
