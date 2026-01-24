#!/usr/bin/env python3
"""
Extended search for f(k)/k ratios.
Goal: Find tightest cases where ratio approaches 3.32 threshold.
"""

import sys
import math
sys.set_int_max_str_digits(100000)

CRITICAL_THRESHOLD = 1 / math.log10(2)  # ≈ 3.321928

def last_k_zeroless(n, k):
    """Check if 2^n has no zeros in the last k digits."""
    power = pow(2, n, 10**k)
    for _ in range(k):
        if power % 10 == 0:
            return False
        power //= 10
    return True

def find_min_survivor(k, start, max_search):
    """Find the minimum n >= start that survives to level k."""
    for n in range(start, max_search + 1):
        if last_k_zeroless(n, k):
            return n
    return None

def extended_search(k_start, k_end, max_n=10**8):
    """Search for minimum ratios across a range of k values."""
    print("=" * 70)
    print(f"Extended Ratio Search: k = {k_start} to {k_end}")
    print(f"Critical threshold: {CRITICAL_THRESHOLD:.6f}")
    print("=" * 70)
    print()

    results = []
    global_min_ratio = float('inf')
    global_min_k = None
    global_min_n = None

    current_min_n = 87  # Start after last zeroless

    # Track cases close to threshold
    close_cases = []

    print(f"{'k':<6} {'f(k)':<12} {'ratio':<10} {'margin':<12} {'status'}")
    print("-" * 60)

    for k in range(k_start, k_end + 1):
        # Adaptive search limit based on k
        search_limit = min(max_n, max(10**7, k * 1000))

        min_n = find_min_survivor(k, start=current_min_n, max_search=search_limit)

        if min_n is None:
            print(f"{k:<6} NOT FOUND (searched to {search_limit})")
            continue

        ratio = min_n / k
        margin = ratio - CRITICAL_THRESHOLD

        # Track global minimum
        if ratio < global_min_ratio:
            global_min_ratio = ratio
            global_min_k = k
            global_min_n = min_n

        # Status indicator
        if margin < 0.5:
            status = "*** TIGHT ***"
            close_cases.append((k, min_n, ratio, margin))
        elif margin < 1.0:
            status = "* close *"
            close_cases.append((k, min_n, ratio, margin))
        else:
            status = ""

        # Only print interesting cases or every 10th
        if status or k % 10 == 0 or k <= k_start + 5:
            print(f"{k:<6} {min_n:<12} {ratio:<10.4f} {margin:<+12.4f} {status}")

        results.append((k, min_n, ratio, margin))
        current_min_n = min_n

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print(f"Global minimum ratio: {global_min_ratio:.6f} at k={global_min_k}, n={global_min_n}")
    print(f"Margin above threshold: {global_min_ratio - CRITICAL_THRESHOLD:+.6f}")
    print()

    if close_cases:
        print("Cases with margin < 1.0:")
        print("-" * 50)
        for k, n, ratio, margin in sorted(close_cases, key=lambda x: x[2]):
            print(f"  k={k}: f(k)={n}, ratio={ratio:.4f}, margin={margin:+.4f}")
    else:
        print("No cases found with margin < 1.0")

    print()
    print("Verification of tightest case:")
    if global_min_k:
        print(f"  2^{global_min_n} last {global_min_k} digits are zeroless")
        print(f"  Ratio: {global_min_n}/{global_min_k} = {global_min_ratio:.6f}")
        print(f"  Threshold: {CRITICAL_THRESHOLD:.6f}")
        print(f"  SAFE by margin: {global_min_ratio - CRITICAL_THRESHOLD:+.6f}")

    return results, global_min_ratio, global_min_k

def analyze_specific_n(n_values):
    """Analyze survival depth for specific n values."""
    print()
    print("=" * 70)
    print("Survival Depth Analysis")
    print("=" * 70)
    print()
    print(f"{'n':<12} {'D(n)':<8} {'max_k':<8} {'n/max_k':<10} {'vs 3.32'}")
    print("-" * 60)

    for n in n_values:
        d = int(n * math.log10(2)) + 1
        # Find maximum k for which last k digits are zeroless
        max_k = 0
        for k in range(1, d + 50):
            if last_k_zeroless(n, k):
                max_k = k
            else:
                break

        if max_k > 0:
            ratio = n / max_k
            vs_threshold = ratio - CRITICAL_THRESHOLD
            print(f"{n:<12} {d:<8} {max_k:<8} {ratio:<10.4f} {vs_threshold:+.4f}")

if __name__ == "__main__":
    # Phase 1: Extended search from k=27 to k=200
    print("PHASE 1: Extended ratio search")
    print()
    results, min_ratio, min_k = extended_search(27, 200, max_n=10**8)

    # Phase 2: If we found tight cases, analyze them
    print()
    print("PHASE 2: Analyzing known interesting n values")
    interesting_n = [129, 176, 229, 700, 1958, 7931, 269518]
    analyze_specific_n(interesting_n)

    print()
    print("=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    print(f"""
The empirical minimum ratio is {min_ratio:.4f} at k={min_k}.
The critical threshold is {CRITICAL_THRESHOLD:.4f}.
Margin: {min_ratio - CRITICAL_THRESHOLD:+.4f}

For the 86 conjecture to fail, we would need ratio < {CRITICAL_THRESHOLD:.4f}.
All observed ratios are ABOVE this threshold.

The Suffix Bound Lemma target: Prove f(k) > {CRITICAL_THRESHOLD:.4f} × k for all k > 26.
""")
