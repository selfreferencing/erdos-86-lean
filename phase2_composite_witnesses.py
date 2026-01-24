#!/usr/bin/env python3
"""
Phase 2: Composite Witness Analysis for K13 Coverage

This script analyzes composite witnesses (d = 4, 6, 8, 9, ...) that can cover
residue classes where no small prime witness works.

Can run independently of Phase 1 - will be ready to process gap list when available.
"""

from math import gcd, isqrt
from collections import defaultdict
from typing import List, Tuple, Set, Dict, Optional

# K13 covering set
K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Mordell-hard residue classes mod 840
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

def m_k(k: int) -> int:
    """The modulus m_k = 4k + 3"""
    return 4 * k + 3

def x_k(p: int, k: int) -> int:
    """Compute x_k = (p + m_k) / 4"""
    mk = m_k(k)
    if (p + mk) % 4 != 0:
        return -1  # Not defined for this p
    return (p + mk) // 4

def divisors_of_square(n: int, limit: int) -> List[int]:
    """
    Return divisors d of n^2 with d <= limit.
    For witness checking, we need d | x^2 and d <= x.
    """
    if n <= 0:
        return []
    n2 = n * n
    divs = []
    i = 1
    while i * i <= n2 and i <= limit:
        if n2 % i == 0:
            divs.append(i)
            other = n2 // i
            if other != i and other <= limit:
                divs.append(other)
        i += 1
    return sorted(divs)

def is_type_ii_witness(x: int, m: int, d: int) -> bool:
    """
    Check if d is a Type II witness for (x, m):
    - d | x^2
    - d <= x
    - (x + d) ≡ 0 (mod m)
    """
    if d <= 0 or x <= 0 or m <= 0:
        return False
    if d > x:
        return False
    if (x * x) % d != 0:
        return False
    if (x + d) % m != 0:
        return False
    return True

def find_witness(p: int, k: int, max_d: int = None) -> Optional[int]:
    """
    Find any witness d for prime p at position k.
    Returns the witness d, or None if not found.

    IMPORTANT: Uses full divisor enumeration by default (max_d=None).
    Some witnesses can be large (e.g., d=1476 for p=87481).
    """
    mk = m_k(k)
    xk = x_k(p, k)
    if xk <= 0:
        return None

    # Full divisor enumeration of x_k^2
    xk2 = xk * xk
    d = 1
    while d * d <= xk2:
        if xk2 % d == 0:
            # Check d
            if d <= xk and (max_d is None or d <= max_d):
                if is_type_ii_witness(xk, mk, d):
                    return d
            # Check x_k^2 / d
            other = xk2 // d
            if other <= xk and other != d and (max_d is None or other <= max_d):
                if is_type_ii_witness(xk, mk, other):
                    return other
        d += 1
    return None

def find_composite_witness(p: int, k: int, composites: List[int] = None) -> Optional[int]:
    """
    Find a COMPOSITE witness d for prime p at position k.
    Excludes primes and 1.
    """
    if composites is None:
        # Standard composite witnesses to try
        composites = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25,
                      26, 27, 28, 30, 32, 33, 35, 36, 40, 42, 45, 48, 49, 50,
                      54, 56, 60, 63, 64, 70, 72, 75, 80, 81, 84, 90, 96, 98, 100]

    mk = m_k(k)
    xk = x_k(p, k)
    if xk <= 0:
        return None

    for d in composites:
        if is_type_ii_witness(xk, mk, d):
            return d
    return None

def analyze_composite_coverage_for_residue(mh_class: int, mod: int = 840) -> Dict:
    """
    For a Mordell-hard residue class, analyze which k values can use composite witnesses.

    Returns dict mapping k -> list of working composite witnesses (for sample primes).
    """
    results = {}

    # Test on sample primes in this residue class
    sample_primes = []
    for p in range(mh_class, 100000, mod):
        if p > 1 and is_prime(p):
            sample_primes.append(p)
        if len(sample_primes) >= 20:
            break

    for k in K13:
        mk = m_k(k)
        composite_hits = defaultdict(int)

        for p in sample_primes:
            xk = x_k(p, k)
            if xk <= 0:
                continue

            # Find all composite witnesses for this (p, k)
            for d in [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 36]:
                if is_type_ii_witness(xk, mk, d):
                    composite_hits[d] += 1

        # Record composites that work for most/all sample primes
        working = [(d, cnt) for d, cnt in composite_hits.items() if cnt >= len(sample_primes) // 2]
        results[k] = sorted(working, key=lambda x: -x[1])

    return results

def is_prime(n: int) -> bool:
    """Simple primality test"""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, isqrt(n) + 1, 2):
        if n % i == 0:
            return False
    return True

def analyze_gap_structure() -> None:
    """
    Analyze what residue conditions would cause a prime to escape ALL witnesses
    for a given k. This helps predict where gaps might occur.
    """
    print("=" * 70)
    print("GAP STRUCTURE ANALYSIS")
    print("=" * 70)
    print("\nFor each k, what residue conditions on x_k would block all small witnesses?\n")

    small_primes = [2, 3, 5, 7, 11, 13]

    for k in K13:
        mk = m_k(k)
        print(f"\nk={k}, m_k={mk}:")

        # For prime q to be a witness: q | x_k AND (x_k + q) ≡ 0 (mod m_k)
        # Second condition: x_k ≡ -q (mod m_k)

        # So prime q FAILS if: x_k ≢ -q (mod m_k) OR q ∤ x_k

        blocking_conditions = []
        for q in small_primes:
            # q fails as witness if x_k ≢ -q (mod m_k)
            # i.e., x_k mod m_k ≠ (-q) mod m_k
            target = (-q) % mk
            blocking_conditions.append(f"  q={q} blocked when x_k ≢ {target} (mod {mk})")

        for cond in blocking_conditions[:4]:
            print(cond)

        # Composite d=4 requires: 4 | x_k^2 (i.e., 2 | x_k) AND (x_k + 4) ≡ 0 (mod m_k)
        target_4 = (-4) % mk
        print(f"  d=4 works when 2|x_k AND x_k ≡ {target_4} (mod {mk})")

def verify_composite_sufficiency(limit: int = 10000) -> None:
    """
    For all Mordell-hard primes up to limit, verify that if all small prime
    witnesses fail, at least one composite witness works.
    """
    print("=" * 70)
    print(f"COMPOSITE WITNESS SUFFICIENCY TEST (primes up to {limit})")
    print("=" * 70)

    small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    composites = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 36, 40, 42, 45, 48, 49]

    for mh in MORDELL_HARD:
        print(f"\n--- Mordell-hard class {mh} mod 840 ---")

        cases_needing_composite = 0
        composite_success = 0
        composite_fail = 0

        for p in range(mh, limit, 840):
            if p < 2 or not is_prime(p):
                continue

            # For each k, check if it needs composite witness
            for k in K13:
                mk = m_k(k)
                xk = x_k(p, k)
                if xk <= 0:
                    continue

                # Check if any small prime works
                prime_works = False
                for q in small_primes:
                    if is_type_ii_witness(xk, mk, q):
                        prime_works = True
                        break

                # Also check d=1 (always divides x^2, always <= x for x >= 1)
                if is_type_ii_witness(xk, mk, 1):
                    prime_works = True

                if not prime_works:
                    cases_needing_composite += 1
                    # Check composites
                    comp_works = False
                    for d in composites:
                        if is_type_ii_witness(xk, mk, d):
                            comp_works = True
                            break
                    if comp_works:
                        composite_success += 1
                    else:
                        composite_fail += 1
                        if composite_fail <= 5:
                            print(f"  WARNING: p={p}, k={k} has no small prime OR composite witness!")

        print(f"  Cases needing composite: {cases_needing_composite}")
        print(f"  Composite success: {composite_success}")
        print(f"  Composite fail: {composite_fail}")

def full_coverage_test(limit: int = 50000) -> None:
    """
    Test that every Mordell-hard prime up to limit has at least one working k.
    """
    print("=" * 70)
    print(f"FULL K13 COVERAGE TEST (Mordell-hard primes up to {limit})")
    print("=" * 70)

    failures = []
    total_tested = 0

    for mh in MORDELL_HARD:
        for p in range(mh, limit, 840):
            if p < 2 or not is_prime(p):
                continue

            total_tested += 1

            # Check if any k works
            found = False
            for k in K13:
                mk = m_k(k)
                xk = x_k(p, k)
                if xk <= 0:
                    continue

                witness = find_witness(p, k, max_d=200)
                if witness is not None:
                    found = True
                    break

            if not found:
                failures.append(p)

    print(f"\nTotal Mordell-hard primes tested: {total_tested}")
    print(f"Failures (no k works): {len(failures)}")
    if failures:
        print(f"Failed primes: {failures[:20]}...")
    else:
        print("SUCCESS: All primes covered!")

def generate_witness_table() -> None:
    """
    Generate a table showing which witnesses work for each (Mordell-hard class, k) pair.
    This can be used for Lean formalization.
    """
    print("=" * 70)
    print("WITNESS TABLE FOR LEAN FORMALIZATION")
    print("=" * 70)

    print("\n-- For each (mh_class, k), list witnesses that work for ALL tested primes")
    print("-- Format: (mh_class, k) -> [d1, d2, ...]\n")

    for mh in MORDELL_HARD:
        print(f"\n-- Mordell-hard class {mh} mod 840:")

        # Test on first 50 primes in this class
        test_primes = []
        for p in range(mh, 500000, 840):
            if p > 1 and is_prime(p):
                test_primes.append(p)
            if len(test_primes) >= 50:
                break

        for k in K13:
            mk = m_k(k)

            # Track which witnesses work for ALL test primes
            witness_counts = defaultdict(int)
            valid_primes = 0

            for p in test_primes:
                xk = x_k(p, k)
                if xk <= 0:
                    continue
                valid_primes += 1

                for d in range(1, 51):
                    if is_type_ii_witness(xk, mk, d):
                        witness_counts[d] += 1

            # Witnesses that work for all tested primes
            universal = [d for d, cnt in witness_counts.items() if cnt == valid_primes and valid_primes > 0]

            if universal:
                print(f"  ({mh}, {k}) -> {sorted(universal)[:10]}")  # First 10


def main():
    print("Phase 2: Composite Witness Analysis")
    print("=" * 70)

    # Test 1: Full coverage with all witness types
    full_coverage_test(limit=100000)

    # Test 2: Gap structure analysis
    analyze_gap_structure()

    # Test 3: Composite sufficiency
    verify_composite_sufficiency(limit=50000)

    # Test 4: Generate witness table for Lean
    generate_witness_table()

    print("\n" + "=" * 70)
    print("Phase 2 analysis complete.")
    print("Ready to process gaps from Phase 1 when available.")
    print("=" * 70)


if __name__ == "__main__":
    main()
