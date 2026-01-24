#!/usr/bin/env python3
"""
MICRO Analysis: Survivor Tree Growth (Extended)
Focus on k > 26 where zeroless powers run out.
"""

import sys
sys.set_int_max_str_digits(100000)

# Known zeroless powers of 2 (n where 2^n has no digit 0)
ZEROLESS = {1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19, 24, 25, 27, 28,
            31, 32, 33, 34, 35, 36, 37, 39, 49, 51, 67, 72, 76, 77, 81, 86}

def get_last_k_digits(n, k):
    """Get last k digits of 2^n as a list (LSB first)."""
    power = pow(2, n, 10**k)
    digits = []
    for _ in range(k):
        digits.append(power % 10)
        power //= 10
    return digits

def last_k_zeroless(n, k):
    """Check if 2^n has no zeros in the last k digits."""
    digits = get_last_k_digits(n, k)
    return 0 not in digits

def find_min_survivor_extended(k, start=1, max_search=10**8):
    """Find the minimum n >= start that survives to level k."""
    for n in range(start, max_search + 1):
        if last_k_zeroless(n, k):
            return n
    return None

def digit_count(n):
    """Number of digits in 2^n."""
    import math
    return int(n * math.log10(2)) + 1

def analyze_extended():
    print("=" * 70)
    print("MICRO Analysis: Survivor Growth Beyond Zeroless Powers")
    print("=" * 70)
    print()

    print("Part 1: Cross-reference with zeroless powers")
    print("-" * 50)
    print(f"{'k':<4} {'min_n':<10} {'D(min_n)':<10} {'zeroless?':<10} {'k vs D':<10}")
    print("-" * 50)

    import math

    for k in range(1, 30):
        min_n = find_min_survivor_extended(k, start=k, max_search=10**6)
        if min_n is None:
            print(f"{k:<4} NOT FOUND")
            continue

        d = digit_count(min_n)
        is_zeroless = min_n in ZEROLESS
        comparison = "k <= D" if k <= d else "k > D"

        print(f"{k:<4} {min_n:<10} {d:<10} {'YES' if is_zeroless else 'no':<10} {comparison:<10}")

    print()
    print("Part 2: For k > 26, find minimum n with last k digits zeroless")
    print("-" * 50)
    print("(These are NOT fully zeroless - just suffix-zeroless)")
    print()
    print(f"{'k':<4} {'min_n':<12} {'period':<15} {'n/period':<12}")
    print("-" * 50)

    for k in range(27, 40):
        period = 4 * (5 ** (k - 1))
        # Search more extensively
        min_n = find_min_survivor_extended(k, start=k, max_search=min(period + k, 10**8))
        if min_n is None:
            print(f"{k:<4} NOT FOUND (searched up to {min(period + k, 10**8)})")
            continue

        ratio = min_n / period
        print(f"{k:<4} {min_n:<12} {period:<15} {ratio:.6e}")

    print()
    print("Part 3: Detailed look at k=27,28,29,30")
    print("-" * 50)

    for k in [27, 28, 29, 30]:
        print(f"\nk = {k}:")
        print(f"  Period = 4 * 5^{k-1} = {4 * 5**(k-1):.2e}")

        # Find first few survivors
        survivors = []
        n = k
        count = 0
        while count < 5 and n < 10**7:
            if last_k_zeroless(n, k):
                survivors.append(n)
                count += 1
            n += 1

        if survivors:
            print(f"  First survivors: {survivors}")
            # Check if any are fully zeroless
            for s in survivors:
                digits = get_last_k_digits(s, k)
                d_total = digit_count(s)
                print(f"    n={s}: D(n)={d_total}, last {k} digits zeroless")
        else:
            print(f"  No survivors found up to 10^7")

    print()
    print("Part 4: THE CRITICAL QUESTION")
    print("-" * 50)
    print("For large k, does min_n grow like 5^k or like k?")
    print()

    # Collect data
    data = []
    for k in range(10, 35):
        period = 4 * (5 ** (k - 1))
        min_n = find_min_survivor_extended(k, start=k, max_search=min(10**7, period + k))
        if min_n:
            data.append((k, min_n, period))

    print(f"{'k':<4} {'min_n':<12} {'min_n/k':<12} {'log5(min_n)':<12}")
    print("-" * 50)
    import math
    for k, min_n, period in data:
        ratio_k = min_n / k
        log5 = math.log(min_n) / math.log(5)
        print(f"{k:<4} {min_n:<12} {ratio_k:<12.2f} {log5:<12.3f}")

if __name__ == "__main__":
    analyze_extended()
