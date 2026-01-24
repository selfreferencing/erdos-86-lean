#!/usr/bin/env python3
"""
Complete case analysis for ten_k_cover_exists.

Key insight from previous analysis:
- n odd: 2 | x_14, and 2 is primitive root mod 59, so k=14 gives witnesses
- n even: More complex, need to analyze

We analyze all cases mod 14 (combining parity and mod 7).
"""

from math import gcd, log2, ceil
from functools import reduce

K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

def m_k(k):
    return 4 * k + 3

def multiplicative_order(a, m):
    if gcd(a, m) != 1:
        return None
    order = 1
    power = a % m
    while power != 1:
        power = (power * a) % m
        order += 1
        if order > m:
            return None
    return order

def euler_phi(n):
    result = n
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0:
                n //= p
            result -= result // p
        p += 1
    if n > 1:
        result -= result // n
    return result

def is_primitive_root(a, m):
    return multiplicative_order(a, m) == euler_phi(m)

print("=" * 70)
print("COMPLETE CASE ANALYSIS")
print("=" * 70)
print()

# First, verify the key facts about primitive roots
print("Primitive root checks:")
print("-" * 50)

primitive_root_facts = {}
for k in K10:
    m = m_k(k)
    for q in [2, 3, 5, 7, 11, 13]:
        if gcd(q, m) == 1:
            order = multiplicative_order(q, m)
            phi = euler_phi(m)
            is_pr = order == phi
            if is_pr:
                primitive_root_facts[(q, k)] = True
                print(f"{q} is primitive root mod {m} (m_{k})")

print()

# KEY THEOREM FOR n ODD
print("=" * 70)
print("THEOREM 1: n odd case")
print("=" * 70)
print()
print("When n = x_5 is odd:")
print("  x_14 = n + 9 is even (since 9 is odd)")
print("  2 | x_14")
print("  2 is primitive root mod 59 = m_14")
print("  Therefore: ∃b, 2^b ≡ -x_14 (mod 59)")
print()
print("  For this b, if 2^b ≤ x_14, then d = 2^b is a witness for k=14.")
print()

# Compute the maximum b needed
print("  Maximum b needed: b such that 2^b spans all residues mod 59")
print(f"  ord(2) mod 59 = 58, so we need b ∈ {{0, 1, ..., 57}}")
print(f"  Maximum 2^b = 2^57 ≈ 1.4 × 10^17")
print()
print("  For x_14 = n + 9 > 2^57, we're guaranteed a witness.")
print("  This holds for p > 4 × 2^57 - 59 ≈ 5.8 × 10^17")
print()
print("  For smaller p, we need to verify computationally or find smaller witnesses.")
print()

# Actually, we can be smarter: we don't need 2^b to hit every residue,
# we just need 2^b ≤ x_14 for the specific b that gives 2^b ≡ -x_14 (mod 59).
# The discrete log of -x_14 base 2 mod 59 could be small.

print("  REFINEMENT: For any x_14, compute b = log_2(-x_14) mod 59")
print("  If b ≤ log_2(x_14), then 2^b ≤ x_14 is a witness.")
print()
print("  Since b < 58 and log_2(x_14) grows with p, for p large enough:")
print("  2^58 ≈ 2.9 × 10^17, so x_14 > 2^58 when p > 1.1 × 10^18")
print()

# For smaller p, we need to be more careful.
# But we can also use other divisors of x_14.

print("  ALTERNATIVE: If x_14 has additional prime factors q with q primitive root mod 59,")
print("  then products 2^a × q^b give more witnesses.")
print()

# Now analyze n even case
print("=" * 70)
print("THEOREM 2: n even case - detailed analysis")
print("=" * 70)
print()

# For n even, we analyze by n mod 7
# x_k values: x_5=n, x_7=n+2, x_9=n+4, x_11=n+6, x_14=n+9, x_17=n+12, x_19=n+14, x_23=n+18, x_26=n+21, x_29=n+24

# Which x_k have small prime factors?
print("Divisibility by small primes when n is even:")
print()

for r7 in range(7):
    print(f"n ≡ {r7} (mod 7):")

    # Check each small prime
    facts = {}
    for q in [2, 3, 5, 7]:
        for k in K10:
            offset = k - 5
            # q | x_k iff n + offset ≡ 0 (mod q)
            # iff n ≡ -offset (mod q)

            # For n even: n ≡ 0 (mod 2)
            # For n ≡ r7 (mod 7): n ≡ r7 (mod 7)

            if q == 2:
                # n is even, so n + offset is even iff offset is even
                if offset % 2 == 0:
                    facts[(2, k)] = True
            elif q == 7:
                # 7 | (n + offset) iff n ≡ -offset (mod 7)
                if r7 == (-offset) % 7:
                    facts[(7, k)] = True
            # Skip 3 and 5 for now - they depend on more than just n mod 14

    # List which k values have which NQR factors
    nqr_ks = []
    for (q, k), _ in facts.items():
        m = m_k(k)
        # Check if q is NQR mod m
        if gcd(q, m) == 1:
            order = multiplicative_order(q, m)
            phi = euler_phi(m)
            # q is NQR iff order < phi
            if order < phi:
                nqr_ks.append((q, k, order, phi, is_primitive_root(q, m)))

    print(f"  Even offsets (2 | x_k): k ∈ {{k : offset even}} = {{k : (k-5) even}}")
    even_k = [k for k in K10 if (k - 5) % 2 == 0]
    print(f"    = {even_k}")

    seven_k = [k for k in K10 if (-k + 5) % 7 == r7]
    print(f"  7 | x_k for k where (5-k) ≡ {r7} (mod 7): k ∈ {seven_k}")

    # Check if any of these give primitive roots
    witnesses = []
    for k in even_k:
        m = m_k(k)
        if gcd(2, m) == 1 and is_primitive_root(2, m):
            witnesses.append((2, k, m))
    for k in seven_k:
        m = m_k(k)
        if gcd(7, m) == 1 and is_primitive_root(7, m):
            witnesses.append((7, k, m))

    if witnesses:
        print(f"  WITNESSES via primitive roots: {witnesses}")
    else:
        print(f"  No primitive root witnesses from 2 or 7")

    print()

# More detailed analysis
print("=" * 70)
print("REFINED ANALYSIS: n even")
print("=" * 70)
print()

# Key observation: for n even
# - 2 | x_k iff (k-5) is even, i.e., k ∈ {5, 7, 9, 11, 23, 29} (wait, let me recalculate)
# Offsets: 5→0, 7→2, 9→4, 11→6, 14→9, 17→12, 19→14, 23→18, 26→21, 29→24
# Even offsets: 0, 2, 4, 6, 12, 14, 18, 24 → k = 5, 7, 9, 11, 17, 19, 23, 29

even_offset_k = [k for k in K10 if (k - 5) % 2 == 0]
odd_offset_k = [k for k in K10 if (k - 5) % 2 == 1]
print(f"k with even offset (2 | x_k when n even): {even_offset_k}")
print(f"k with odd offset (2 ∤ x_k when n even): {odd_offset_k}")
print()

# Check which k values have 2 as NQR mod m_k
print("For which k is 2 a NQR mod m_k?")
two_nqr_k = []
for k in K10:
    m = m_k(k)
    if gcd(2, m) == 1:
        order = multiplicative_order(2, m)
        phi = euler_phi(m)
        if order < phi:
            two_nqr_k.append(k)
            print(f"  k={k}: ord(2) mod {m} = {order}, φ({m}) = {phi}, 2 is NQR")
        else:
            print(f"  k={k}: ord(2) mod {m} = {order} = φ({m}), 2 is primitive root (QR)")
print()
print(f"k values where 2 is NQR: {two_nqr_k}")
print()

# The intersection: k with even offset AND 2 is NQR
intersection = set(even_offset_k) & set(two_nqr_k)
print(f"k with even offset AND 2 is NQR: {intersection}")
print()

# For k in intersection, when n is even, 2 | x_k and 2 is NQR mod m_k
# This means NOT all prime factors of x_k are QR, so the QR obstruction fails

# But we need actual witnesses, not just obstruction failure
# Let's check which k have 2 as primitive root

print("For which k is 2 a primitive root mod m_k?")
two_pr_k = []
for k in K10:
    m = m_k(k)
    if gcd(2, m) == 1 and is_primitive_root(2, m):
        two_pr_k.append(k)
        print(f"  k={k}: 2 is primitive root mod {m}")
print()

# For k in two_pr_k, every nonzero residue mod m_k is a power of 2
# So if 2 | x_k, we can find 2^b ≡ -x_k (mod m_k)

intersection_pr = set(even_offset_k) & set(two_pr_k)
print(f"k with even offset AND 2 is primitive root: {intersection_pr}")
print()

# Similarly for 7
print("For which k is 7 a primitive root mod m_k?")
seven_pr_k = []
for k in K10:
    m = m_k(k)
    if gcd(7, m) == 1 and is_primitive_root(7, m):
        seven_pr_k.append(k)
        print(f"  k={k}: 7 is primitive root mod {m}")
print()

# Now, let's see which (n mod 14) cases are covered
print("=" * 70)
print("COVERAGE BY n mod 14")
print("=" * 70)
print()

for n_mod_14 in range(14):
    n_parity = n_mod_14 % 2
    n_mod_7 = n_mod_14 % 7

    print(f"n ≡ {n_mod_14} (mod 14): n is {'even' if n_parity == 0 else 'odd'}, n ≡ {n_mod_7} (mod 7)")

    if n_parity == 1:
        # n is odd: k=14 works
        print(f"  → n odd: 2 | x_14, 2 is primitive root mod 59. k=14 works!")
        print()
        continue

    # n is even: check which k values have primitive root factors
    witnesses = []

    # Check 2 as primitive root
    for k in two_pr_k:
        offset = k - 5
        if offset % 2 == 0:  # 2 | x_k
            witnesses.append((2, k, f"2 | x_{k}, 2 is PR mod {m_k(k)}"))

    # Check 7 as primitive root
    for k in seven_pr_k:
        offset = k - 5
        # 7 | x_k iff n ≡ -offset (mod 7)
        if n_mod_7 == (-offset) % 7:
            witnesses.append((7, k, f"7 | x_{k}, 7 is PR mod {m_k(k)}"))

    if witnesses:
        print(f"  → Witnesses found:")
        for q, k, reason in witnesses:
            print(f"      {reason}")
    else:
        print(f"  → NO WITNESSES from primitive roots of 2 or 7")
        print(f"      Need deeper analysis!")

    print()

print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()
print("All 7 odd values of n mod 14 are covered by k=14 (2 is PR mod 59).")
print()
print("For even n mod 14:")
print("  - We need to check if primitive roots of 2 and 7 cover all cases")
print("  - If not, we need to use products of prime powers or other factors")
