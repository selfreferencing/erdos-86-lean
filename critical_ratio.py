#!/usr/bin/env python3
"""
MICRO Analysis: The Critical Ratio
If min_n/k > 1/log10(2) ≈ 3.32 for all k > k0, the conjecture is true.
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

def find_survival_depth(n, max_k=1000):
    """Find the maximum k such that last k digits of 2^n are zeroless."""
    for k in range(1, max_k + 1):
        if not last_k_zeroless(n, k):
            return k - 1
    return max_k

def analyze_critical_ratio():
    print("=" * 70)
    print("MICRO Analysis: The Critical Ratio")
    print(f"Critical threshold: 1/log10(2) = {CRITICAL_THRESHOLD:.6f}")
    print("=" * 70)
    print()

    print("Part 1: Ratio min_n/k for k = 27 to 100")
    print("-" * 60)
    print(f"{'k':<5} {'min_n':<10} {'ratio':<10} {'above 3.32?':<12}")
    print("-" * 60)

    results = []
    current_min = 87  # Start after last zeroless

    for k in range(27, 101):
        # Find minimum n that survives to level k
        min_n = find_min_survivor(k, start=current_min, max_search=10**7)

        if min_n is None:
            print(f"{k:<5} NOT FOUND")
            continue

        ratio = min_n / k
        above = "YES" if ratio > CRITICAL_THRESHOLD else "NO"
        margin = ratio - CRITICAL_THRESHOLD

        print(f"{k:<5} {min_n:<10} {ratio:<10.4f} {above:<12} (margin: {margin:+.4f})")
        results.append((k, min_n, ratio))

        # Update starting point for next search
        current_min = min_n

    print()
    print("Part 2: Statistics")
    print("-" * 60)

    ratios = [r for _, _, r in results]
    min_ratio = min(ratios)
    max_ratio = max(ratios)
    avg_ratio = sum(ratios) / len(ratios)

    print(f"Minimum ratio: {min_ratio:.4f}")
    print(f"Maximum ratio: {max_ratio:.4f}")
    print(f"Average ratio: {avg_ratio:.4f}")
    print(f"Critical threshold: {CRITICAL_THRESHOLD:.4f}")
    print()

    below_threshold = [r for r in ratios if r < CRITICAL_THRESHOLD]
    if below_threshold:
        print(f"WARNING: {len(below_threshold)} ratios below threshold!")
        print(f"Minimum below: {min(below_threshold):.4f}")
    else:
        print("All ratios above critical threshold!")

    print()
    print("Part 3: What is the survival depth of specific n?")
    print("-" * 60)
    print("(How deep does 2^n survive before hitting a zero?)")
    print()

    test_cases = [87, 88, 89, 100, 129, 176, 229, 500, 1000, 1958, 7931]

    print(f"{'n':<8} {'D(n)':<8} {'max_k':<8} {'max_k/D(n)':<12} {'zeroless?':<10}")
    print("-" * 60)

    for n in test_cases:
        d = int(n * math.log10(2)) + 1
        max_k = find_survival_depth(n, max_k=min(d + 100, 500))
        ratio = max_k / d
        is_zeroless = (max_k >= d)
        print(f"{n:<8} {d:<8} {max_k:<8} {ratio:<12.4f} {'YES' if is_zeroless else 'no'}")

    print()
    print("Part 4: Key insight")
    print("-" * 60)
    print(f"""
For 2^n to be zeroless:
  - Need last D(n) digits to be zeroless
  - D(n) = 0.301n

From the data:
  - min{{m : last k digits of 2^m zeroless}} ≈ {avg_ratio:.2f} × k

For zeroless at n:
  - Need n to survive to level k = D(n) = 0.301n
  - min_survivor(k) ≈ {avg_ratio:.2f} × k = {avg_ratio:.2f} × 0.301n = {avg_ratio * 0.301:.2f}n

Since {avg_ratio * 0.301:.2f} > 1, we have min_survivor(D(n)) > n for large n.
This means n CANNOT survive to level D(n), so 2^n has a zero!

The ratio {avg_ratio:.2f} × 0.301 = {avg_ratio * 0.301:.3f} > 1 is the key.
""")

if __name__ == "__main__":
    analyze_critical_ratio()
