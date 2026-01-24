#!/usr/bin/env python3
"""
Direct verification that K_COMPLETE covers all primes in every residue class mod 840.

This tests actual primes rather than relying on CRT rule generation.
"""

from math import gcd
from collections import defaultdict

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

def is_prime(n):
    """Miller-Rabin primality test."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    if n < 9:
        return True
    if n % 3 == 0:
        return False

    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2

    witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for a in witnesses:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

def factor(n):
    """Return list of (prime, exponent) pairs."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                e += 1
                n //= d
            factors.append((d, e))
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append((n, 1))
    return factors

def divisors_of_square(n):
    """Return all divisors of n²."""
    facts = factor(n)
    divs = [1]
    for p, e in facts:
        new_divs = []
        for d in divs:
            power = 1
            for i in range(2*e + 1):
                new_divs.append(d * power)
                power *= p
        divs = new_divs
    return sorted(divs)

def find_witness(p, k):
    """Find a Type II witness for p at k."""
    m_k = 4 * k + 3
    if (p + m_k) % 4 != 0:
        return None
    x_k = (p + m_k) // 4
    if gcd(x_k, m_k) > 1:
        return None
    target = (-x_k) % m_k
    divs = divisors_of_square(x_k)
    for d in divs:
        if d % m_k == target:
            return (k, d, x_k, m_k)
    return None

def find_covering_k(p, K):
    """Find the first k in K that covers prime p."""
    for k in K:
        result = find_witness(p, k)
        if result is not None:
            return result
    return None

def get_admissible_classes(modulus=840):
    """Get all admissible residue classes mod modulus."""
    classes = []
    for r in range(1, modulus, 4):  # r ≡ 1 (mod 4)
        if gcd(r, modulus) == 1:
            classes.append(r)
    return classes

def main():
    print("=" * 70)
    print("DIRECT COVERAGE VERIFICATION")
    print("=" * 70)
    print(f"K_COMPLETE = {K_COMPLETE}")
    print(f"|K| = {len(K_COMPLETE)}")

    admissible = get_admissible_classes(840)
    print(f"\nAdmissible classes mod 840: {len(admissible)}")

    # For each class, find small primes and verify coverage
    uncovered_classes = []
    problematic_primes = []

    print("\nVerifying each residue class...")
    print("-" * 70)

    for r in admissible:
        # Find first 5 primes in this class
        primes_in_class = []
        p = r
        while len(primes_in_class) < 5 and p < 10**7:
            if p > 1 and p % 4 == 1 and is_prime(p):
                primes_in_class.append(p)
            p += 840

        # Check coverage for each prime
        all_covered = True
        for p in primes_in_class:
            result = find_covering_k(p, K_COMPLETE)
            if result is None:
                all_covered = False
                problematic_primes.append((r, p))

        if not all_covered:
            uncovered_classes.append(r)
            print(f"  Class {r}: UNCOVERED primes found!")
        else:
            # Show first covering witness as sample
            if primes_in_class:
                result = find_covering_k(primes_in_class[0], K_COMPLETE)
                if result:
                    k, d, x_k, m_k = result
                    # Just note it's covered
                    pass

    print("-" * 70)

    # Summary
    print(f"\n{'=' * 70}")
    print("VERIFICATION RESULTS")
    print(f"{'=' * 70}")
    print(f"Total admissible classes: {len(admissible)}")
    print(f"Classes with all sample primes covered: {len(admissible) - len(uncovered_classes)}")
    print(f"Classes with uncovered primes: {len(uncovered_classes)}")

    if uncovered_classes:
        print(f"\nUncovered classes: {uncovered_classes}")
        print(f"\nProblematic primes:")
        for r, p in problematic_primes[:20]:
            print(f"  Class {r}: p = {p}")
    else:
        print("\n*** ALL SAMPLE PRIMES COVERED BY K_COMPLETE ***")
        print("This suggests complete coverage mod 840.")

    # Double-check: verify 1000 primes ≡ 1 (mod 4) are all covered
    print(f"\n{'=' * 70}")
    print("ADDITIONAL VERIFICATION: First 1000 primes ≡ 1 (mod 4)")
    print(f"{'=' * 70}")

    count = 0
    uncovered = []
    p = 5
    while count < 1000:
        if is_prime(p):
            count += 1
            result = find_covering_k(p, K_COMPLETE)
            if result is None:
                uncovered.append(p)
        p += 4

    print(f"Checked {count} primes ≡ 1 (mod 4)")
    print(f"Uncovered: {len(uncovered)}")
    if uncovered:
        print(f"Uncovered primes: {uncovered[:20]}...")
    else:
        print("*** ALL 1000 PRIMES COVERED! ***")

    # Final verification: check up to 10^6
    print(f"\n{'=' * 70}")
    print("EXHAUSTIVE CHECK: All primes ≡ 1 (mod 4) up to 10^6")
    print(f"{'=' * 70}")

    uncovered = []
    p = 5
    count = 0
    while p < 10**6:
        if is_prime(p):
            count += 1
            result = find_covering_k(p, K_COMPLETE)
            if result is None:
                uncovered.append(p)
        p += 4

    print(f"Checked {count} primes")
    print(f"Uncovered: {len(uncovered)}")
    if uncovered:
        print(f"First uncovered primes: {uncovered[:20]}")
        # Analyze the uncovered primes
        print("\nAnalyzing uncovered primes:")
        for p in uncovered[:5]:
            print(f"  p = {p}, p mod 840 = {p % 840}")
    else:
        print("*** ALL PRIMES UP TO 10^6 COVERED! ***")

if __name__ == "__main__":
    main()
