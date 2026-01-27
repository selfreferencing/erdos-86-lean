#!/usr/bin/env python3
"""
Find a FINITE covering set for the 6 hard QR classes.
Combines D6 subcases (more M values) + divisor-pair (DP) congruences.

The sorry covers: p%24=1, p%7 in {1,2,4}, p%5 in {1,4}, p%11 not in {7,8,10}.
"""

from math import gcd
from collections import defaultdict

def lcm2(a, b):
    return a * b // gcd(a, b)

def divisors(n):
    if n <= 0: return []
    result = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            result.append(i)
            if i != n // i:
                result.append(n // i)
        i += 1
    return sorted(result)

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def get_d6_residues(M):
    k = (M + 1) // 4
    if 4 * k - 1 != M:
        return set()
    seen = set()
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            seen.add((-4 * a * s * s) % M)
    return seen

def get_d6_params(M, target_res):
    k = (M + 1) // 4
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            r = rem // s
            if (-4 * a * s * s) % M == target_res:
                return (a, r, s)
    return None

def main():
    print("=" * 78)
    print("COVERAGE ANALYSIS FOR 6 HARD CLASSES")
    print("=" * 78)

    # Collect hard primes up to 1M
    hard_primes = []
    for p in range(25, 1_000_001, 24):
        if not is_prime(p):
            continue
        if p % 7 not in (1, 2, 4) or p % 5 not in (1, 4):
            continue
        if p % 11 in (7, 8, 10):
            continue
        hard_primes.append(p)

    print(f"Hard primes up to 1M (after M=11 filter): {len(hard_primes)}")

    # Phase 1: D6 coverage with more M values
    print("\n--- Phase 1: D6 coverage ---")
    M_primes = [p for p in range(11, 200) if is_prime(p) and p % 4 == 3]
    # Also include composite M values
    M_all = sorted(set([M for M in range(3, 200) if M % 4 == 3]))

    d6_data = {}
    for M in M_all:
        res = get_d6_residues(M)
        if res:
            d6_data[M] = res

    uncovered = set(hard_primes)
    d6_witness = {}
    Ms_used = []

    for M in sorted(d6_data.keys()):
        residues = d6_data[M]
        newly = set()
        for p in uncovered:
            if p % M in residues:
                newly.add(p)
                d6_witness[p] = (M, get_d6_params(M, p % M))
        if newly:
            uncovered -= newly
            Ms_used.append(M)
            if len(uncovered) < len(hard_primes):
                pct = 100 * (1 - len(uncovered) / len(hard_primes))
                if M <= 50 or len(newly) > 10:
                    print(f"  M={M:3d}: +{len(newly):5d} covered, "
                          f"{len(uncovered):5d} remain ({pct:.1f}%)")
        if not uncovered:
            break

    print(f"\n  D6 total: {len(hard_primes) - len(uncovered)} / {len(hard_primes)}")
    print(f"  Uncovered by D6: {len(uncovered)}")

    # Phase 2: DP on remaining
    if uncovered:
        print(f"\n--- Phase 2: DP coverage ---")
        dp_witness = {}
        still_uncov = set()

        for p in sorted(uncovered):
            found = False
            for delta in range(3, 2001, 4):
                if (p + delta) % 4 != 0:
                    continue
                A = (p + delta) // 4
                for u in range(1, min(delta, 300)):
                    v = delta - u
                    if v <= 0:
                        break
                    if A % u != 0 or A % v != 0:
                        continue
                    b = A // u
                    c = A // v
                    if (p + delta) * (b + c) == 4 * delta * b * c:
                        dp_witness[p] = (delta, u, v, b, c, A)
                        found = True
                        break
                if found:
                    break
            if not found:
                still_uncov.add(p)

        print(f"  DP covered: {len(dp_witness)} / {len(uncovered)}")
        if still_uncov:
            print(f"  STILL UNCOVERED: {sorted(still_uncov)[:20]}")
        else:
            print(f"  ALL PRIMES COVERED!")

        # Analyze DP triples
        triple_counts = defaultdict(list)
        for p, (delta, u, v, b, c, A) in dp_witness.items():
            triple_counts[(delta, u, v)].append(p)

        print(f"\n  DP triples used: {len(triple_counts)}")
        print(f"  Top 20:")
        for (delta, u, v), primes in sorted(triple_counts.items(),
                                             key=lambda x: -len(x[1]))[:20]:
            L = 4 * lcm2(u, v)
            res = (-delta) % L
            print(f"    d={delta:4d} u={u:3d} v={v:3d} L={L:6d} "
                  f"res={res:6d} covers={len(primes):4d}")

    # Phase 3: Check which D6 M-values are essential
    print(f"\n--- Phase 3: Essential M-values ---")
    M_counts = defaultdict(int)
    for p, (M, params) in d6_witness.items():
        M_counts[M] += 1

    print(f"  D6 M-values used: {len(M_counts)}")
    for M, count in sorted(M_counts.items(), key=lambda x: -x[1])[:20]:
        print(f"    M={M:4d}: {count:5d} primes, "
              f"residues={sorted(d6_data[M])}")

    # Phase 4: Verify on primes up to 10M
    print(f"\n--- Phase 4: Verification up to 10M ---")
    total = 0
    failures = []
    for p in range(25, 10_000_001, 24):
        if not is_prime(p):
            continue
        if p % 7 not in (1, 2, 4) or p % 5 not in (1, 4):
            continue
        if p % 11 in (7, 8, 10):
            continue
        total += 1

        # D6 check
        found = False
        for M, residues in d6_data.items():
            if p % M in residues:
                found = True
                break

        if not found:
            # DP check
            for delta in range(3, 2001, 4):
                if (p + delta) % 4 != 0:
                    continue
                A = (p + delta) // 4
                for u in range(1, min(delta, 300)):
                    v = delta - u
                    if v <= 0: break
                    if A % u != 0 or A % v != 0: continue
                    found = True
                    break
                if found: break

        if not found:
            failures.append(p)

    print(f"  Checked: {total}")
    print(f"  Failures: {len(failures)}")
    if failures:
        print(f"  Failed: {failures[:20]}")
    else:
        print(f"  ALL VERIFIED!")

if __name__ == "__main__":
    main()
