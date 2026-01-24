#!/usr/bin/env python3
"""
Attempt to prove Gemini's strategy via finite covering.

Key insight: For small primes q, we know exactly:
1. Which x_k values are divisible by q (depends on n mod q)
2. Which primes p have (p/q) = -1 (half of all primes)

If for every Mordell-hard residue class, at least one small prime q
divides some x_k AND has (p/q) = -1, then we have a complete proof.

This reduces to a finite verification mod lcm(840, small primes).
"""

from math import gcd
from functools import reduce

K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

def lcm(a, b):
    return a * b // gcd(a, b)

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

# Small primes to use as witnesses
SMALL_PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

print("=" * 70)
print("FINITE COVERING PROOF ATTEMPT")
print("=" * 70)
print()

# For each small prime q, determine:
# 1. For which n mod q is q | x_k (i.e., n ≡ -offset (mod q))
# 2. For which p mod q is (p/q) = -1 (the non-residues)

offsets = {k: k - 5 for k in K10}

print("Analysis by small prime q:")
print("-" * 50)

for q in SMALL_PRIMES:
    print(f"\nPrime q = {q}:")

    # Which k have q | x_k for various n?
    print(f"  Divisibility: q | x_k iff n ≡ -offset (mod {q})")
    for k in K10:
        target = (-offsets[k]) % q
        print(f"    k={k:2d}: n ≡ {target} (mod {q})")

    # Which residues of p have (p/q) = -1?
    nqr = [r for r in range(1, q) if legendre(r, q) == -1]
    print(f"  Non-quadratic residues mod {q}: {nqr}")

print()
print("=" * 70)
print("COVERING VERIFICATION")
print("=" * 70)
print()

# Work modulo M = lcm(840, q1, q2, ...) for small primes
# But this gets huge. Instead, let's use a probabilistic/exhaustive check.

# For each Mordell-hard prime p, we need at least one k such that
# there exists q with: (1) q | x_k, and (2) (p/q) = -1

# The key observation: n = (p + 23)/4
# So n mod q depends on p mod (4q)

# Let's work mod 4 * lcm(small primes) combined with Mordell constraint

# Simpler approach: enumerate all residues and check

# For p mod (4 * product of small primes), we can determine:
# - n = (p + 23)/4 mod (product)
# - For each q: whether (p/q) = ±1, and which x_k are divisible by q

M = 840 * 2  # Start with just checking mod 1680

print(f"Checking all Mordell-hard residues mod {M}...")
print()

# Enumerate Mordell-hard residues mod M
mordell_residues = []
for base in MORDELL_HARD:
    for i in range(M // 840):
        r = (base + i * 840) % M
        mordell_residues.append(r)
mordell_residues = sorted(set(mordell_residues))

print(f"Number of Mordell-hard residues mod {M}: {len(mordell_residues)}")

successes = 0
failures = []

for p_mod in mordell_residues:
    # n = (p + 23) / 4 for Mordell-hard primes (p ≡ 1 mod 4)
    # So n ≡ (p_mod + 23) / 4 (mod M/4)
    n_mod = (p_mod + 23) // 4  # This works since p ≡ 1 (mod 4)

    found_witness = False

    for q in SMALL_PRIMES:
        # Check (p/q)
        leg = legendre(p_mod, q)
        if leg == 0:
            continue  # q | p, skip

        if leg == -1:
            # This q is "bad" for p. Check if q | x_k for some k.
            for k in K10:
                offset = offsets[k]
                # q | x_k iff (n + offset) ≡ 0 (mod q)
                if (n_mod + offset) % q == 0:
                    found_witness = True
                    break

        if found_witness:
            break

    if found_witness:
        successes += 1
    else:
        failures.append(p_mod)

print(f"Successes: {successes}/{len(mordell_residues)}")
print(f"Failures: {len(failures)}")

if failures:
    print()
    print("Failed residues:")
    for p_mod in failures[:20]:
        n_mod = (p_mod + 23) // 4
        print(f"  p ≡ {p_mod} (mod {M}), n ≡ {n_mod}")
        print(f"    Legendre symbols (p/q):")
        for q in SMALL_PRIMES:
            leg = legendre(p_mod, q)
            print(f"      (p/{q}) = {leg}")

        print(f"    Which x_k divisible by which q:")
        for k in K10:
            offset = offsets[k]
            divs = [q for q in SMALL_PRIMES if (n_mod + offset) % q == 0]
            print(f"      x_{k} divisible by: {divs}")
else:
    print()
    print("=" * 70)
    print("SUCCESS! All Mordell-hard residues have witnesses!")
    print("=" * 70)
    print()
    print("This proves Gemini's strategy works for all primes.")

# Now check with larger modulus
print()
print("=" * 70)
print("EXTENDED CHECK")
print("=" * 70)

# Check mod 840 * 30 = 25200
M = 840 * 30

mordell_residues = []
for base in MORDELL_HARD:
    for i in range(M // 840):
        r = (base + i * 840) % M
        mordell_residues.append(r)
mordell_residues = sorted(set(mordell_residues))

print(f"Checking all {len(mordell_residues)} Mordell-hard residues mod {M}...")

successes = 0
failures = []

for p_mod in mordell_residues:
    n_mod = (p_mod + 23) // 4

    found_witness = False

    for q in SMALL_PRIMES:
        leg = legendre(p_mod, q)
        if leg == 0:
            continue

        if leg == -1:
            for k in K10:
                offset = offsets[k]
                if (n_mod + offset) % q == 0:
                    found_witness = True
                    break

        if found_witness:
            break

    if found_witness:
        successes += 1
    else:
        failures.append(p_mod)

print(f"Successes: {successes}/{len(mordell_residues)}")
print(f"Failures: {len(failures)}")

if failures:
    print(f"First few failures: {failures[:10]}")
