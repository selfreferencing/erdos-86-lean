#!/usr/bin/env python3
"""
Find a minimal K set that covers all Mordell-hard primes up to a limit.
"""

import sys
from math import isqrt

MORDELL_HARD = [1, 121, 169, 289, 361, 529]

def is_prime(n):
    if n < 2: return False
    if n == 2 or n == 3: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def x_k(p, k):
    m = 4*k + 3
    return (p + m) // 4 if (p + m) % 4 == 0 else None

def has_witness(p, k):
    m = 4*k + 3
    x = x_k(p, k)
    if x is None:
        return False
    target = (-x) % m
    if target == 0:
        target = m
    x_sq = x * x
    d = target
    while d <= x:
        if d > 0 and x_sq % d == 0:
            return True
        d += m
    return False

def get_primes(limit):
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, isqrt(limit) + 1):
        if sieve[i]:
            sieve[i*i::i] = [False] * len(sieve[i*i::i])
    return [p for p in range(2, limit + 1) if sieve[p] and (p % 840) in MORDELL_HARD]

def find_coverage_failures(primes, k_set):
    """Find primes not covered by k_set."""
    failures = []
    for p in primes:
        covered = False
        for k in k_set:
            if has_witness(p, k):
                covered = True
                break
        if not covered:
            failures.append(p)
    return failures

def greedy_extend(primes, k_set, max_k=100):
    """Greedily add k values to cover failures."""
    k_set = list(k_set)
    failures = find_coverage_failures(primes, k_set)

    while failures:
        # Find k that covers most failures
        best_k = None
        best_count = 0
        for k in range(max_k + 1):
            if k in k_set:
                continue
            count = sum(1 for p in failures if has_witness(p, k))
            if count > best_count:
                best_count = count
                best_k = k

        if best_k is None or best_count == 0:
            print(f"Cannot cover {len(failures)} remaining failures!")
            break

        k_set.append(best_k)
        old_failures = len(failures)
        failures = find_coverage_failures(primes, k_set)
        print(f"Added k={best_k} (m_k={4*best_k+3}): covers {old_failures - len(failures)} primes, "
              f"{len(failures)} remaining")

    return sorted(k_set), failures

def main():
    limit = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**6

    print(f"Finding minimal K set for coverage up to {limit:,}")
    print("=" * 60)

    primes = get_primes(limit)
    print(f"Found {len(primes):,} Mordell-hard primes")

    # Start with K13
    K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
    print(f"\nStarting with K13 = {K13}")

    failures = find_coverage_failures(primes, K13)
    print(f"K13 failures: {len(failures)}")

    if failures:
        print(f"\nExtending K13 greedily...")
        extended_k, remaining = greedy_extend(primes, K13, max_k=100)
        print(f"\nExtended K set: {extended_k}")
        print(f"Size: {len(extended_k)}")
        print(f"Remaining failures: {len(remaining)}")

    # Also try starting from scratch with greedy
    print("\n" + "=" * 60)
    print("Building K set from scratch (greedy):")
    k_set, remaining = greedy_extend(primes, [], max_k=50)
    print(f"\nMinimal greedy K set: {k_set}")
    print(f"Size: {len(k_set)}")

if __name__ == "__main__":
    main()
