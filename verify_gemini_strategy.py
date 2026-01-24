#!/usr/bin/env python3
"""
Verify Gemini's strategy: For any Mordell-hard prime p,
at least one x_k has a prime factor q with (p/q) = -1.

Key insight from Gemini: (q/m_k) = (p/q) for q | x_k
So if (p/q) = -1 for some q | x_k, the obstruction fails for k.
"""

from math import gcd

K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

def legendre(a, p):
    """Compute Legendre symbol (a/p) for odd prime p."""
    if a % p == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return result if result == 1 else -1

def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True

def prime_factors(n):
    """Return list of prime factors of n."""
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            if d not in factors:
                factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def x_k(p, k):
    return (p + 4*k + 3) // 4

def m_k(k):
    return 4*k + 3

print("=" * 70)
print("VERIFYING GEMINI'S STRATEGY")
print("=" * 70)
print()
print("Gemini's claim: (q/m_k) = (p/q) for q | x_k")
print("So obstruction fails if any q | x_k has (p/q) = -1")
print()

# First verify the reciprocity relation
print("Verifying the reciprocity relation for small examples...")
print("-" * 50)

for p in [1009, 1201, 1489]:  # Some Mordell-hard primes
    for k in K10[:3]:
        x = x_k(p, k)
        m = m_k(k)
        factors = [q for q in prime_factors(x) if q > 2]

        for q in factors[:2]:
            leg_q_m = legendre(q, m) if is_prime(m) else None
            leg_p_q = legendre(p, q)

            # For composite m, need Jacobi symbol (skip for now)
            if is_prime(m):
                print(f"p={p}, k={k}: q={q} | x_k={x}")
                print(f"  (q/m_k) = ({q}/{m}) = {leg_q_m}")
                print(f"  (p/q) = ({p}/{q}) = {leg_p_q}")
                if leg_q_m == leg_p_q:
                    print(f"  ✓ Match!")
                else:
                    print(f"  ✗ MISMATCH!")
                print()

# Now test the main claim: for Mordell-hard primes,
# at least one k has a "bad" prime factor
print("=" * 70)
print("TESTING MAIN CLAIM")
print("=" * 70)
print()

# Generate Mordell-hard primes up to 10000
mordell_primes = []
for p in range(2, 10000):
    if is_prime(p) and (p % 840) in MORDELL_HARD:
        mordell_primes.append(p)

print(f"Testing {len(mordell_primes)} Mordell-hard primes up to 10000")
print()

failures = []

for p in mordell_primes:
    found_witness = False
    witness_info = None

    for k in K10:
        x = x_k(p, k)
        m = m_k(k)
        factors = prime_factors(x)

        for q in factors:
            if q == 2:
                continue  # Skip 2 for now

            leg_p_q = legendre(p, q)
            if leg_p_q == -1:
                # Found a witness! (p/q) = -1 means (q/m_k) = -1
                # This breaks the obstruction for k
                found_witness = True
                witness_info = (k, q, x)
                break

        if found_witness:
            break

    if not found_witness:
        failures.append(p)
        print(f"FAILURE: p = {p}")
        for k in K10:
            x = x_k(p, k)
            factors = prime_factors(x)
            legs = [(q, legendre(p, q)) for q in factors if q > 2]
            print(f"  k={k}: x_k={x}, factors={factors}")
            print(f"    Legendre symbols (p/q): {legs}")

if not failures:
    print("ALL Mordell-hard primes up to 10000 have a witness!")
else:
    print(f"FAILURES: {failures}")

print()
print("=" * 70)
print("DETAILED WITNESS ANALYSIS")
print("=" * 70)
print()

# Show which k values provide witnesses
k_witness_counts = {k: 0 for k in K10}

for p in mordell_primes[:100]:  # First 100
    for k in K10:
        x = x_k(p, k)
        factors = prime_factors(x)

        has_witness = False
        for q in factors:
            if q > 2 and legendre(p, q) == -1:
                has_witness = True
                break

        if has_witness:
            k_witness_counts[k] += 1

print("Witness counts by k (for first 100 Mordell-hard primes):")
for k, count in sorted(k_witness_counts.items(), key=lambda x: -x[1]):
    print(f"  k={k:2d}: {count} primes have witness at this k")

print()
print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()
print("Gemini's strategy: The obstruction at k holds iff (p/q) = 1")
print("for all odd primes q | x_k.")
print()
print("For a non-square p, there exist primes with (p/q) = -1.")
print("The question is whether any such prime divides some x_k.")
print()
print("If verified, this gives a COMPLETE PROOF of ten_k_cover_exists!")
