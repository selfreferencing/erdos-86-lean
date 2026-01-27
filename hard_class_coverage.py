#!/usr/bin/env python3
"""
Analyze D6 coverage of the 6 hard classes mod 840 as we add primes.

Uses CRT-based enumeration: for each of the 6 classes mod 840 and each
tuple of residues mod auxiliary primes, check if any D6 modulus covers it.

Key insight: D6 requires M ≡ 3 (mod 4). Primes ≡ 3 mod 4 (like 11, 19, 23, 31)
can appear directly as M. Primes ≡ 1 mod 4 (like 5, 13, 17, 29) only appear
in composite M values.
"""

import time
from math import gcd
from itertools import product as iterproduct


def divisors(n):
    if n <= 0: return []
    small, large = [], []
    i = 1
    while i * i <= n:
        if n % i == 0:
            small.append(i)
            if i != n // i:
                large.append(n // i)
        i += 1
    return small + large[::-1]


def get_residues_for_M(M):
    k = (M + 1) // 4
    if 4 * k - 1 != M:
        return set()
    seen = set()
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            res = (-4 * a * s * s) % M
            seen.add(res)
    return seen


def crt_pair(a, m, b, p):
    """CRT: x ≡ a mod m, x ≡ b mod p. Returns x mod (m*p). Requires gcd(m,p) = 1."""
    m_inv = pow(m, -1, p)
    t = ((b - a) * m_inv) % p
    return (a + m * t) % (m * p)


HARD_CLASSES_840 = [1, 121, 169, 289, 361, 529]


def check_coverage(aux_primes, verbose=True):
    """Check D6 coverage for hard classes with given auxiliary primes."""
    t0 = time.time()

    # Compute oddQ = 3 * 5 * 7 * product(aux_primes)
    oddQ = 3 * 5 * 7
    for p in aux_primes:
        oddQ *= p

    # D6 moduli: divisors of oddQ that are ≡ 3 mod 4
    all_divs = divisors(oddQ)
    M_values = [d for d in all_divs if d % 4 == 3 and d >= 3]

    # Compute D6 residues for each M
    M_data = {}
    for M in M_values:
        res = get_residues_for_M(M)
        if res:
            M_data[M] = res

    if verbose:
        print(f"  oddQ = {oddQ:,}, divisors: {len(all_divs)}, "
              f"M-values (≡3 mod 4): {len(M_values)}, with residues: {len(M_data)}")

    # Count tuples
    n_tuples = 1
    for p in aux_primes:
        n_tuples *= (p - 1)
    total = 6 * n_tuples

    if verbose:
        print(f"  Tuples per class: {n_tuples:,}, total: {total:,}")

    # Enumerate
    covered = 0
    uncov_count = 0
    uncov_samples = []

    for r840 in HARD_CLASSES_840:
        r105 = r840 % 105  # odd part of 840 = 105

        # Sort M_data by M size (smaller M more likely to hit)
        sorted_Ms = sorted(M_data.items(), key=lambda x: x[0])

        aux_ranges = [range(1, p) for p in aux_primes]

        for aux_tuple in iterproduct(*aux_ranges):
            # CRT to get x mod oddQ
            x = r105
            m = 105
            for i, p in enumerate(aux_primes):
                x = crt_pair(x, m, aux_tuple[i], p)
                m *= p

            # Check D6 coverage
            found = False
            for M, residues in sorted_Ms:
                if x % M in residues:
                    found = True
                    break

            if found:
                covered += 1
            else:
                uncov_count += 1
                if len(uncov_samples) < 20:
                    uncov_samples.append((r840, aux_tuple))

    elapsed = time.time() - t0
    pct = 100 * covered / total if total > 0 else 0

    if verbose:
        print(f"  Covered: {covered:,} / {total:,} ({pct:.4f}%)")
        print(f"  Uncovered: {uncov_count:,} ({100-pct:.4f}%)")
        print(f"  Time: {elapsed:.1f}s")

        if uncov_samples:
            print(f"  Sample uncovered:")
            for r840, atup in uncov_samples[:10]:
                labels = [f"mod{p}={atup[i]}" for i, p in enumerate(aux_primes)]
                print(f"    r840={r840}, {', '.join(labels)}")

    return uncov_count


def main():
    print("=" * 80)
    print("D6 COVERAGE ANALYSIS FOR 6 HARD CLASSES MOD 840")
    print("=" * 80)
    print()
    print("Hard classes mod 840: {1, 121, 169, 289, 361, 529}")
    print("These are p mod 7 ∈ {1,2,4} AND p mod 5 ∈ {1,4}, perfect squares mod 840.")
    print()

    # Test with increasing sets of auxiliary primes
    # Primes ≡ 3 mod 4 are most useful (direct D6 moduli): 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83
    # Primes ≡ 1 mod 4 appear in composite M: 13, 17, 29, 37, 41, 53, 61, 73

    configs = [
        [11],
        [11, 13],
        [11, 13, 17],
        [11, 13, 17, 19],
        [11, 13, 17, 19, 23],
    ]

    for aux in configs:
        print(f"\n--- Aux primes: {aux} ---")
        uncov = check_coverage(aux)
        if uncov == 0:
            print("\n*** COMPLETE D6 COVERAGE ACHIEVED! ***")
            break

    # If not done, try with more primes (but may be slow)
    if uncov > 0:
        print(f"\n--- Extended test: adding primes 31 and 43 ---")
        # This has 10*12*16*18*22*30*42 = 95,800,320 per class, way too many
        # Use sampling instead
        print("  (Too many tuples for exhaustive check, using targeted analysis)")

        # Instead, analyze the uncovered tuples from {11,13,17,19,23}
        # to understand what additional primes would help
        print(f"\n--- Analyzing uncovered structure from aux=[11,13,17,19,23] ---")
        aux = [11, 13, 17, 19, 23]
        analyze_uncovered(aux)


def analyze_uncovered(aux_primes):
    """Analyze the structure of uncovered tuples."""
    oddQ = 3 * 5 * 7
    for p in aux_primes:
        oddQ *= p

    M_values = [d for d in divisors(oddQ) if d % 4 == 3 and d >= 3]
    M_data = {}
    for M in M_values:
        res = get_residues_for_M(M)
        if res:
            M_data[M] = res

    sorted_Ms = sorted(M_data.items(), key=lambda x: x[0])

    # Collect uncovered residues mod each prime
    from collections import defaultdict
    uncov_by_prime = {p: defaultdict(int) for p in aux_primes}
    total_uncov = 0

    for r840 in HARD_CLASSES_840:
        r105 = r840 % 105
        aux_ranges = [range(1, p) for p in aux_primes]

        for aux_tuple in iterproduct(*aux_ranges):
            x = r105
            m = 105
            for i, p in enumerate(aux_primes):
                x = crt_pair(x, m, aux_tuple[i], p)
                m *= p

            found = False
            for M, residues in sorted_Ms:
                if x % M in residues:
                    found = True
                    break

            if not found:
                total_uncov += 1
                for i, p in enumerate(aux_primes):
                    uncov_by_prime[p][aux_tuple[i]] += 1

    print(f"  Total uncovered: {total_uncov:,}")
    print(f"\n  Residue distribution of uncovered:")
    for p in aux_primes:
        dist = dict(sorted(uncov_by_prime[p].items()))
        # Compute QR/QNR classification
        qr = set()
        for a in range(1, p):
            if pow(a, (p-1)//2, p) == 1:
                qr.add(a)
        qr_count = sum(v for k, v in dist.items() if k in qr)
        qnr_count = sum(v for k, v in dist.items() if k not in qr)
        print(f"  mod {p}: QR={qr_count}, QNR={qnr_count}")
        # Show which QNR residues remain
        qnr_remaining = {k for k in dist if k not in qr}
        if qnr_remaining:
            print(f"    QNR residues still uncovered: {sorted(qnr_remaining)}")
        if p <= 23:
            print(f"    Full dist: {dist}")


if __name__ == "__main__":
    main()
