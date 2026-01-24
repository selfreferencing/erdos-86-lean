#!/usr/bin/env python3
"""
Analyze uncovered residue classes and find k values that could cover them.

For each uncovered class r mod 840, we:
1. Find small primes p ≡ r (mod 840)
2. For each such p, search for k values that provide witnesses
3. Identify which k values would be most useful to add
"""

from math import gcd, isqrt
from collections import defaultdict
import json

# From the certificate
UNCOVERED_CLASSES = [
    1, 17, 29, 73, 89, 101, 121, 169, 173, 193, 197, 241, 257, 269, 281, 289, 293,
    313, 341, 353, 361, 409, 437, 449, 461, 481, 509, 521, 529, 593, 617, 629, 649,
    677, 689, 701, 761, 773, 793
]

# Mordell-hard classes (perfect squares mod 840)
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
K_RESCUE = [3, 31, 39, 41]
K_FULL = K13 + K_RESCUE

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
            return d
    return None

def find_primes_in_class(r, modulus, count=10, max_search=10**8):
    """Find primes p ≡ r (mod modulus)."""
    primes = []
    # Start from smallest positive p ≡ r (mod modulus) with p ≡ 1 (mod 4)
    p = r
    while p <= max_search and len(primes) < count:
        if p > 1 and p % 4 == 1 and is_prime(p):
            primes.append(p)
        p += modulus
    return primes

def find_covering_k_for_prime(p, max_k=200):
    """Find all k values that provide a witness for prime p."""
    covering_k = []
    for k in range(max_k + 1):
        witness = find_witness(p, k)
        if witness is not None:
            covering_k.append((k, witness))
    return covering_k

def analyze_uncovered_classes():
    """Analyze which k values could cover the uncovered classes."""
    print("=" * 70)
    print("ANALYZING UNCOVERED RESIDUE CLASSES")
    print("=" * 70)

    print(f"\nTotal uncovered classes: {len(UNCOVERED_CLASSES)}")
    print(f"Mordell-hard classes in list: {[r for r in UNCOVERED_CLASSES if r in MORDELL_HARD]}")

    # Track which k values help with each class
    k_usefulness = defaultdict(list)  # k -> list of (class, prime) it helps

    print("\n" + "-" * 70)
    print("Analyzing each uncovered class...")
    print("-" * 70)

    for r in UNCOVERED_CLASSES:
        is_mordell = r in MORDELL_HARD
        print(f"\nClass r ≡ {r} (mod 840) {'[MORDELL-HARD]' if is_mordell else ''}")

        # Find small primes in this class
        primes = find_primes_in_class(r, 840, count=5)
        if not primes:
            print(f"  No small primes found")
            continue

        print(f"  Sample primes: {primes}")

        # For each prime, find covering k values
        for p in primes[:3]:  # Check first 3 primes
            covering = find_covering_k_for_prime(p, max_k=100)
            # Filter to k values not in K_FULL
            new_covering = [(k, w) for k, w in covering if k not in K_FULL]

            if new_covering:
                print(f"  p={p}: new k values that help: {[(k,w) for k,w in new_covering[:5]]}")
                for k, w in new_covering:
                    k_usefulness[k].append((r, p))
            else:
                # Check if already covered by K_FULL
                existing = [(k, w) for k, w in covering if k in K_FULL]
                if existing:
                    print(f"  p={p}: already covered by K_FULL via k={existing[0][0]}")
                else:
                    print(f"  p={p}: NO covering k found up to 100!")

    # Summarize most useful k values
    print("\n" + "=" * 70)
    print("MOST USEFUL NEW k VALUES")
    print("=" * 70)

    # Sort by number of classes helped
    k_sorted = sorted(k_usefulness.items(), key=lambda x: len(set(r for r, p in x[1])), reverse=True)

    print(f"\nTop 20 most useful k values (by number of classes covered):")
    for k, helps in k_sorted[:20]:
        classes_helped = set(r for r, p in helps)
        mordell_helped = [r for r in classes_helped if r in MORDELL_HARD]
        print(f"  k={k:3d} (m={4*k+3:4d}): helps {len(classes_helped):2d} classes, "
              f"Mordell-hard: {len(mordell_helped)}")
        if len(classes_helped) <= 5:
            print(f"       Classes: {sorted(classes_helped)}")

    return k_usefulness

def find_minimal_k_set():
    """Find a minimal set of k values to cover all uncovered classes."""
    print("\n" + "=" * 70)
    print("SEARCHING FOR MINIMAL K SET TO COVER ALL CLASSES")
    print("=" * 70)

    # For each uncovered class, find which k values (not in K_FULL) could help
    class_to_k = {}  # r -> set of k values that help

    for r in UNCOVERED_CLASSES:
        primes = find_primes_in_class(r, 840, count=3)
        helping_k = set()

        for p in primes:
            covering = find_covering_k_for_prime(p, max_k=100)
            for k, w in covering:
                if k not in K_FULL:
                    helping_k.add(k)

        class_to_k[r] = helping_k
        if not helping_k:
            print(f"  WARNING: Class {r} has no new k values that help!")

    # Greedy set cover
    uncovered = set(UNCOVERED_CLASSES)
    selected_k = []

    while uncovered:
        # Find k that covers the most remaining classes
        best_k = None
        best_coverage = 0

        for k in range(101):
            if k in K_FULL or k in selected_k:
                continue
            coverage = sum(1 for r in uncovered if k in class_to_k.get(r, set()))
            if coverage > best_coverage:
                best_coverage = coverage
                best_k = k

        if best_k is None or best_coverage == 0:
            print(f"\n  Cannot cover remaining classes: {sorted(uncovered)}")
            break

        selected_k.append(best_k)
        newly_covered = [r for r in uncovered if best_k in class_to_k.get(r, set())]
        uncovered -= set(newly_covered)
        print(f"  Add k={best_k} (m={4*best_k+3}): covers {len(newly_covered)} classes, "
              f"{len(uncovered)} remaining")

    if not uncovered:
        print(f"\n*** COMPLETE COVERAGE ACHIEVED with {len(selected_k)} additional k values ***")
        print(f"    New k values: {selected_k}")
        print(f"    Full K set: K_FULL ∪ {{{', '.join(map(str, selected_k))}}} = {len(K_FULL) + len(selected_k)} values")

    return selected_k, uncovered

def main():
    # First analyze
    k_usefulness = analyze_uncovered_classes()

    # Then find minimal set
    additional_k, remaining = find_minimal_k_set()

    # Summary
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    print(f"K_FULL = {K_FULL}")
    print(f"Additional k needed: {additional_k}")
    print(f"Remaining uncovered: {sorted(remaining) if remaining else 'NONE'}")

    if not remaining:
        full_k_set = sorted(K_FULL + additional_k)
        print(f"\nComplete K set: {full_k_set}")
        print(f"Total |K| = {len(full_k_set)}")

if __name__ == "__main__":
    main()
