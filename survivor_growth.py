#!/usr/bin/env python3
"""
MICRO Analysis: Survivor Tree Growth
Investigate whether min{n : survives to level k} grows exponentially.
"""

import sys
sys.set_int_max_str_digits(100000)

def get_last_k_digits(n, k):
    """Get last k digits of 2^n as a list (LSB first)."""
    power = pow(2, n, 10**k)
    digits = []
    for _ in range(k):
        digits.append(power % 10)
        power //= 10
    return digits

def survives_to_level(n, k):
    """Check if 2^n has no zeros in the last k digits."""
    if n < k:
        # If n < k, we need all digits of 2^n to be nonzero
        digits = []
        power = 2**n
        while power > 0:
            digits.append(power % 10)
            power //= 10
        return 0 not in digits and len(digits) >= k

    digits = get_last_k_digits(n, k)
    return 0 not in digits

def find_min_survivor(k, max_search=10**7):
    """Find the minimum n > 0 that survives to level k."""
    for n in range(1, max_search + 1):
        if survives_to_level(n, k):
            return n
    return None

def find_all_survivors_in_period(k):
    """Find all n in one period that survive to level k."""
    period = 4 * (5 ** (k - 1)) if k >= 1 else 4
    survivors = []
    for n in range(max(k, 1), period + max(k, 1)):
        if survives_to_level(n, k):
            survivors.append(n)
    return survivors, period

def analyze_growth():
    """Main analysis: does min survivor grow exponentially?"""
    print("=" * 60)
    print("MICRO Analysis: Survivor Tree Growth")
    print("=" * 60)
    print()

    print("Part 1: Minimum n surviving to level k")
    print("-" * 40)
    print(f"{'k':<4} {'min_n':<12} {'period':<12} {'ratio':<10} {'log_5(min_n)':<12}")
    print("-" * 40)

    prev_min = None
    results = []

    for k in range(1, 16):
        period = 4 * (5 ** (k - 1))

        # Find minimum survivor
        min_n = find_min_survivor(k, max_search=period * 2)

        if min_n is None:
            print(f"{k:<4} {'NOT FOUND':<12}")
            break

        ratio = min_n / prev_min if prev_min else "-"
        import math
        log5 = math.log(min_n) / math.log(5) if min_n > 0 else 0

        ratio_str = f"{ratio:.3f}" if isinstance(ratio, float) else ratio
        print(f"{k:<4} {min_n:<12} {period:<12} {ratio_str:<10} {log5:.3f}")

        results.append((k, min_n, period))
        prev_min = min_n

    print()
    print("Part 2: Number of survivors at each level")
    print("-" * 40)
    print(f"{'k':<4} {'survivors':<12} {'period':<12} {'density':<12} {'ratio_to_prev':<12}")
    print("-" * 40)

    prev_count = None
    for k in range(1, 10):
        survivors, period = find_all_survivors_in_period(k)
        count = len(survivors)
        density = count / period
        ratio = count / prev_count if prev_count else "-"
        ratio_str = f"{ratio:.3f}" if isinstance(ratio, float) else ratio

        print(f"{k:<4} {count:<12} {period:<12} {density:.6f}     {ratio_str:<12}")
        prev_count = count

    print()
    print("Part 3: Distribution of survivors within period")
    print("-" * 40)

    for k in range(1, 6):
        survivors, period = find_all_survivors_in_period(k)
        print(f"k={k}: {len(survivors)} survivors in period {period}")
        if len(survivors) <= 20:
            print(f"    n mod {period}: {[s % period for s in survivors]}")
        else:
            print(f"    First 10: {[s % period for s in survivors[:10]]}")
            print(f"    Last 10:  {[s % period for s in survivors[-10:]]}")
        print()

    print()
    print("Part 4: Key question - what is min_n / 5^k?")
    print("-" * 40)
    for k, min_n, period in results:
        ratio_to_5k = min_n / (5 ** k)
        print(f"k={k}: min_n={min_n}, 5^k={5**k}, ratio={ratio_to_5k:.6f}")

if __name__ == "__main__":
    analyze_growth()
