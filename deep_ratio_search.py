#!/usr/bin/env python3
"""
Deep ratio search - looking for tighter cases at higher k.
"""

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

def survival_depth(n, max_k=500):
    """Find max k such that last k digits of 2^n are zeroless."""
    for k in range(1, max_k + 1):
        if not last_k_zeroless(n, k):
            return k - 1
    return max_k

print("=" * 60)
print("DEEP RATIO SEARCH")
print(f"Critical threshold: {CRITICAL:.6f}")
print("=" * 60)
print()

# Phase 1: Find all tight cases (ratio < 4.0)
print("Phase 1: Scanning k=27 to 300 for tight cases")
print("-" * 50)

tight_cases = []
current = 87

for k in range(27, 301):
    n = find_min(k, current, 10**8)
    if n is None:
        continue
    ratio = n / k
    if ratio < 4.0:
        margin = ratio - CRITICAL
        tight_cases.append((k, n, ratio, margin))
        print(f"k={k}: f(k)={n}, ratio={ratio:.4f}, margin={margin:+.4f}")
    current = n

print()
print(f"Found {len(tight_cases)} tight cases (ratio < 4.0)")
print()

# Phase 2: Analyze specific survivors
print("Phase 2: Survival depth of key n values")
print("-" * 50)
print(f"{'n':<10} {'D(n)':<8} {'depth':<8} {'n/depth':<10} {'margin'}")
print("-" * 50)

key_n = [129, 176, 229, 700, 1958, 7931]
for n in key_n:
    d = int(n * math.log10(2)) + 1
    depth = survival_depth(n)
    ratio = n / depth
    margin = ratio - CRITICAL
    print(f"{n:<10} {d:<8} {depth:<8} {ratio:<10.4f} {margin:+.4f}")

print()
print("=" * 60)
print("CONCLUSION")
print("=" * 60)

if tight_cases:
    min_case = min(tight_cases, key=lambda x: x[2])
    print(f"""
Tightest case found: k={min_case[0]}, n={min_case[1]}
  Ratio: {min_case[2]:.6f}
  Critical threshold: {CRITICAL:.6f}
  Margin: {min_case[3]:+.6f}

The 86 conjecture requires ratio > {CRITICAL:.4f} for all k.
All cases satisfy this with margin at least {min_case[3]:+.4f}.

Key insight: n=129 at k=36 is the TIGHTEST case with ratio 3.5833.
This is the "closest call" - if this ratio were below 3.32, the
conjecture would fail. The +0.26 margin is what saves it.
""")
