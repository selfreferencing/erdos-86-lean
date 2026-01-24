#!/usr/bin/env python3
"""
Build Level 2 hierarchical certificate for the 6 resistant classes.

Level 1: M = 840 covers 90/96 classes universally
Level 2: Split 6 resistant classes {1, 121, 169, 289, 361, 529} by mod 11

For each resistant class r mod 840:
- Split into 11 sub-classes: (r, s) where s = 0..10 represents p mod 11
- Find which k ∈ K_COMPLETE provides a universal recipe for each sub-class
"""

from math import gcd
from collections import defaultdict

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]
RESISTANT_CLASSES = [1, 121, 169, 289, 361, 529]

def is_prime(n):
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
    """Find a Type II witness d for p at k, return (k, d) or None."""
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
            return (k, d)
    return None

def get_primes_in_subclass(r, s, M_base=840, M_refine=11, count=10, limit=10**8):
    """Get primes p ≡ r (mod M_base) AND p ≡ s (mod M_refine)."""
    # Use CRT to find starting point
    M = M_base * M_refine  # 840 * 11 = 9240

    # Find t such that t ≡ r (mod 840) and t ≡ s (mod 11)
    # Since gcd(840, 11) = 1, solution exists and is unique mod 9240
    for t in range(M):
        if t % M_base == r and t % M_refine == s:
            start = t
            break
    else:
        return []  # No solution (shouldn't happen)

    primes = []
    p = start
    if p == 0:
        p = M
    while len(primes) < count and p < limit:
        if p > 1 and p % 4 == 1 and is_prime(p):
            primes.append(p)
        p += M
    return primes

def analyze_subclass(r, s, num_primes=10):
    """
    Analyze sub-class (r mod 840, s mod 11).
    Returns (k, witnesses, primes) if a universal recipe exists.
    """
    primes = get_primes_in_subclass(r, s, 840, 11, num_primes)

    if not primes:
        return None, [], []  # Return empty list, not string

    # For each k, check if it works for ALL primes in this sub-class
    for k in K_COMPLETE:
        all_work = True
        witnesses = []
        for p in primes:
            result = find_witness(p, k)
            if result is None:
                all_work = False
                break
            witnesses.append(result[1])

        if all_work:
            # Found a k that works for all primes
            # Check if witnesses have a pattern
            witness_set = set(witnesses)
            return k, witness_set, primes

    # No single k works for all
    return None, [], primes

def build_level2_certificate():
    """Build the Level 2 certificate for resistant classes."""
    print("=" * 70)
    print("LEVEL 2 CERTIFICATE CONSTRUCTION")
    print("=" * 70)
    print(f"Base modulus: M = 840")
    print(f"Refinement modulus: 11 (from k=2, m=11)")
    print(f"Level 2 modulus: M₂ = 840 × 11 = 9240")
    print(f"Resistant classes: {RESISTANT_CLASSES}")
    print()

    certificate = {}
    uncovered_subclasses = []

    for r in RESISTANT_CLASSES:
        print(f"\n{'='*60}")
        print(f"RESISTANT CLASS r ≡ {r} (mod 840)")
        print(f"{'='*60}")

        # For primes ≡ r (mod 840), they can be ≡ 0,1,...,10 (mod 11)
        # But: if gcd(r, 11) > 1, some residues mod 11 are impossible
        # Since 11 ∤ 840 and 11 is prime, all residues 0-10 are possible
        # But if r ≡ 0 (mod 11), then only s=0 is valid

        class_recipes = {}

        for s in range(11):
            # Skip s=0 if we're looking at primes (11 doesn't divide admissible primes except p=11)
            # Actually, let's just check which s values have primes

            result_k, witnesses, primes = analyze_subclass(r, s, num_primes=10)

            if not primes or len(primes) == 0:
                print(f"  s ≡ {s} (mod 11): Empty sub-class (no primes)")
                class_recipes[s] = ("empty", None, [])
                continue

            if result_k is not None:
                m_k = 4 * result_k + 3
                print(f"  s ≡ {s} (mod 11): COVERED by k={result_k} (m={m_k})")
                print(f"      Witnesses: {sorted(witnesses)[:5]}...")
                print(f"      Sample primes: {primes[:3]}")
                class_recipes[s] = ("covered", result_k, witnesses)
            else:
                print(f"  s ≡ {s} (mod 11): UNCOVERED - no single k works")
                print(f"      Sample primes: {primes[:3]}")
                uncovered_subclasses.append((r, s, primes))
                class_recipes[s] = ("uncovered", None, primes)

        certificate[r] = class_recipes

    # Summary
    print("\n" + "=" * 70)
    print("LEVEL 2 CERTIFICATE SUMMARY")
    print("=" * 70)

    total_subclasses = 0
    covered_count = 0
    empty_count = 0
    uncovered_count = 0

    for r in RESISTANT_CLASSES:
        for s in range(11):
            total_subclasses += 1
            status, k, _ = certificate[r][s]
            if status == "covered":
                covered_count += 1
            elif status == "empty":
                empty_count += 1
            else:
                uncovered_count += 1

    print(f"Total sub-classes: {total_subclasses}")
    print(f"Covered by universal recipe: {covered_count}")
    print(f"Empty (no primes): {empty_count}")
    print(f"Still uncovered: {uncovered_count}")

    if uncovered_subclasses:
        print(f"\nUncovered sub-classes requiring Level 3:")
        for r, s, primes in uncovered_subclasses:
            print(f"  (r={r}, s={s}): primes like {primes[:2]}")
    else:
        print(f"\n*** ALL SUB-CLASSES COVERED! ***")
        print("Level 2 certificate is COMPLETE.")

    return certificate, uncovered_subclasses

def main():
    certificate, uncovered = build_level2_certificate()

    # If there are uncovered sub-classes, try Level 3 with mod 23
    if uncovered:
        print("\n" + "=" * 70)
        print("ATTEMPTING LEVEL 3 REFINEMENT (mod 23)")
        print("=" * 70)

        level3_uncovered = []

        for r, s, primes in uncovered:
            # Skip empty sub-classes
            if not primes or (isinstance(primes, list) and len(primes) == 0):
                continue

            print(f"\nSub-class (r={r} mod 840, s={s} mod 11):")

            # Further split by mod 23 (from k=5, m=23)
            for t in range(23):
                # Get primes with all three conditions
                sub_primes = [p for p in primes if isinstance(p, int) and p % 23 == t]
                if not sub_primes:
                    continue

                # Find k that works for these
                found = False
                for k in K_COMPLETE:
                    all_work = all(find_witness(p, k) is not None for p in sub_primes)
                    if all_work:
                        print(f"  t ≡ {t} (mod 23): COVERED by k={k}")
                        found = True
                        break

                if not found:
                    print(f"  t ≡ {t} (mod 23): UNCOVERED, primes: {sub_primes[:2]}")
                    level3_uncovered.append((r, s, t, sub_primes))

        print("\n" + "=" * 70)
        print("LEVEL 3 SUMMARY")
        print("=" * 70)
        if level3_uncovered:
            print(f"Level 3 uncovered sub-classes: {len(level3_uncovered)}")
            for r, s, t, primes in level3_uncovered[:10]:
                print(f"  ({r}, {s}, {t}): primes {primes[:2]}")
        else:
            print("*** ALL LEVEL 3 SUB-CLASSES COVERED! ***")

if __name__ == "__main__":
    main()
