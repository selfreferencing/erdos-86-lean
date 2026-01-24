#!/usr/bin/env python3
"""
Check Type II for primes p ≡ 3 (mod 4).

For p ≡ 1 (mod 4): x_k = (p + 4k + 3)/4 works because p + 3 ≡ 0 (mod 4)
For p ≡ 3 (mod 4): p + 3 ≡ 2 (mod 4), so this doesn't divide evenly.

Need to find the right parameterization for p ≡ 3 (mod 4).
"""

import math
from typing import List, Tuple, Optional

def get_divisors(n: int) -> List[int]:
    if n <= 0:
        return []
    divs = []
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            divs.append(i)
            if i != n // i:
                divs.append(n // i)
    return sorted(divs)

def coprime_pairs(n: int) -> List[Tuple[int, int]]:
    divs = get_divisors(n)
    pairs = []
    for i, a in enumerate(divs):
        for b in divs[i:]:
            if math.gcd(a, b) == 1:
                pairs.append((a, b))
    return pairs

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(math.isqrt(n)) + 1, 2):
        if n % i == 0: return False
    return True

print("=" * 70)
print("ANALYZING p ≡ 3 (mod 4)")
print("=" * 70)

# First, check the original Type II formula
print("\nFor p ≡ 3 (mod 4), checking (p + 4k + 3) mod 4:")
p = 7  # Example: 7 ≡ 3 (mod 4)
for k in range(5):
    m_k = 4*k + 3
    val = p + m_k
    print(f"  k={k}: p + m_k = {p} + {m_k} = {val}, mod 4 = {val % 4}")

print("\nThe original Type II formula doesn't give integers for p ≡ 3 (mod 4)!")

# What's the correct parameterization?
print("\n" + "=" * 70)
print("FINDING THE RIGHT PARAMETERIZATION")
print("=" * 70)

print("""
For p ≡ 3 (mod 4), we need (p + m) ≡ 0 (mod 4).
Since p ≡ 3 (mod 4), we need m ≡ 1 (mod 4).
So m_k = 4k + 1 for k = 0, 1, 2, ...
""")

# Check: for p ≡ 3 (mod 4), use m_k = 4k + 1
print("For p ≡ 3 (mod 4), using m_k = 4k + 1:")
p = 7
for k in range(5):
    m_k = 4*k + 1
    val = p + m_k
    x_k = val // 4
    print(f"  k={k}: p + m_k = {p} + {m_k} = {val}, x_k = {x_k}")

# Now let's verify Type II works for p ≡ 3 (mod 4) with the adjusted formula
print("\n" + "=" * 70)
print("TYPE II FOR p ≡ 3 (mod 4): Using m_k = 4k + 1")
print("=" * 70)

def has_type_ii_3mod4(p: int, k: int) -> Optional[Tuple[int, int]]:
    """Check Type II for p ≡ 3 (mod 4) with m_k = 4k + 1."""
    m_k = 4 * k + 1
    if m_k <= 0:
        return None
    if (p + m_k) % 4 != 0:
        return None

    x_k = (p + m_k) // 4
    divs = get_divisors(x_k)

    for a in divs:
        for b in divs:
            if a <= b and math.gcd(a, b) == 1 and (a + b) % m_k == 0:
                return (a, b)
    return None

# Test on primes ≡ 3 (mod 4)
primes_3mod4 = [p for p in range(3, 1000) if is_prime(p) and p % 4 == 3][:50]

print(f"\nTesting {len(primes_3mod4)} primes ≡ 3 (mod 4):")

results = []
for p in primes_3mod4:
    first_success = None
    for k in range(100):
        result = has_type_ii_3mod4(p, k)
        if result:
            first_success = k
            break
    results.append((p, first_success))

successes = sum(1 for _, k in results if k is not None)
print(f"Successes: {successes}/{len(results)}")

if successes < len(results):
    failures = [(p, k) for p, k in results if k is None]
    print(f"Failures: {failures[:10]}")

# Distribution of first success
success_ks = [k for _, k in results if k is not None]
if success_ks:
    print(f"\nFirst success k distribution:")
    print(f"  Min: {min(success_ks)}")
    print(f"  Max: {max(success_ks)}")
    print(f"  Avg: {sum(success_ks)/len(success_ks):.2f}")
    print(f"  k=0: {sum(1 for k in success_ks if k == 0)}")

# Check if there's an issue with k=0 (m_k = 1, which is degenerate)
print("\n" + "=" * 70)
print("ISSUE: k=0 gives m_k = 1, which is trivial")
print("=" * 70)

print("""
For k=0: m_k = 4(0) + 1 = 1
The condition a + b ≡ 0 (mod 1) is ALWAYS true!
So k=0 always "succeeds" but this might be vacuous.

Let's check if this gives valid ESC solutions.
""")

# Verify actual ESC solutions
from fractions import Fraction

def verify_esc(p, x, y, z):
    """Verify 4/p = 1/x + 1/y + 1/z."""
    lhs = Fraction(4, p)
    rhs = Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
    return lhs == rhs

# For k=0, m_0 = 1, x_0 = (p + 1)/4
# We need coprime pair (a, b) | x_0 with a + b ≡ 0 (mod 1) - always true!
# Then the ESC solution would be derived from this.

print("Checking k=0 solutions for p ≡ 3 (mod 4):")

for p in [3, 7, 11, 19, 23][:5]:
    m_0 = 1
    x_0 = (p + 1) // 4
    pairs = coprime_pairs(x_0)
    print(f"\n  p = {p}:")
    print(f"    x_0 = (p + 1)/4 = {x_0}")
    print(f"    coprime pairs: {pairs[:5]}...")

    # The k=0 case with m_k=1 is degenerate. We should start from k=1.

print("\n" + "=" * 70)
print("CORRECTED: Start from k=1 for p ≡ 3 (mod 4)")
print("=" * 70)

def has_type_ii_3mod4_corrected(p: int, k: int) -> Optional[Tuple[int, int]]:
    """Check Type II for p ≡ 3 (mod 4) with m_k = 4k + 1, k ≥ 1."""
    if k < 1:
        return None
    m_k = 4 * k + 1
    if (p + m_k) % 4 != 0:
        return None

    x_k = (p + m_k) // 4
    divs = get_divisors(x_k)

    for a in divs:
        for b in divs:
            if a <= b and math.gcd(a, b) == 1 and (a + b) % m_k == 0:
                return (a, b)
    return None

print(f"\nTesting with k ≥ 1:")

results_corrected = []
for p in primes_3mod4:
    first_success = None
    for k in range(1, 200):  # Start from k=1
        result = has_type_ii_3mod4_corrected(p, k)
        if result:
            first_success = k
            break
    results_corrected.append((p, first_success))

successes = sum(1 for _, k in results_corrected if k is not None)
print(f"Successes: {successes}/{len(results_corrected)}")

failures = [(p, k) for p, k in results_corrected if k is None]
if failures:
    print(f"Failures: {failures}")

success_ks = [k for _, k in results_corrected if k is not None]
if success_ks:
    print(f"\nFirst success k distribution (k ≥ 1):")
    print(f"  Min: {min(success_ks)}")
    print(f"  Max: {max(success_ks)}")
    print(f"  Avg: {sum(success_ks)/len(success_ks):.2f}")

# Show some examples
print("\nExamples:")
for p, k in results_corrected[:10]:
    if k is not None:
        m_k = 4*k + 1
        x_k = (p + m_k) // 4
        pair = has_type_ii_3mod4_corrected(p, k)
        print(f"  p={p:4d}: k={k}, m_k={m_k}, x_k={x_k}, pair={pair}")
