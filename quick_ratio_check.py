#!/usr/bin/env python3
"""Quick ratio check - limited range for fast results."""

import sys
import math
sys.set_int_max_str_digits(100000)

CRITICAL = 1 / math.log10(2)  # ≈ 3.321928

def last_k_zeroless(n, k):
    power = pow(2, n, 10**k)
    for _ in range(k):
        if power % 10 == 0:
            return False
        power //= 10
    return True

def find_min(k, start, limit):
    for n in range(start, limit + 1):
        if last_k_zeroless(n, k):
            return n
    return None

print(f"Critical threshold: {CRITICAL:.6f}")
print(f"{'k':<5} {'f(k)':<10} {'ratio':<8} {'margin':<10}")
print("-" * 40)

min_ratio = float('inf')
min_k = None
current = 87

for k in range(27, 151):
    n = find_min(k, current, 10**7)
    if n is None:
        print(f"{k:<5} NOT FOUND")
        continue
    ratio = n / k
    margin = ratio - CRITICAL
    if ratio < min_ratio:
        min_ratio = ratio
        min_k = k
    if margin < 1.5 or k <= 40:
        print(f"{k:<5} {n:<10} {ratio:<8.4f} {margin:+.4f}")
    current = n

print()
print(f"MINIMUM: ratio={min_ratio:.4f} at k={min_k}")
print(f"Margin above 3.32: {min_ratio - CRITICAL:+.4f}")
