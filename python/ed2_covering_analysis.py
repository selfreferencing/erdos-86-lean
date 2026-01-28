#!/usr/bin/env python3
"""
ed2_covering_analysis.py

Analyze covering system: greedy set cover, moduli structure, scaling.
Optimized to work with primes up to 1M in reasonable time.
"""

from __future__ import annotations
import math
import time
from collections import defaultdict, Counter


def sieve(n: int) -> bytearray:
    is_prime = bytearray(b'\x01') * (n + 1)
    is_prime[0] = is_prime[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if is_prime[i]:
            is_prime[i*i::i] = b'\x00' * len(is_prime[i*i::i])
    return is_prime


def main():
    limit = 1000000
    alpha_max, rs_max = 5, 30

    print(f"ED2 Covering Analysis up to {limit}")
    t0 = time.time()
    is_prime = sieve(limit)

    primes = [p for p in range(25, limit + 1)
              if p % 24 == 1 and is_prime[p]]
    print(f"Primes p ≡ 1 (mod 24): {len(primes)}")

    # Generate all distinct (M, residue) candidates
    # M = 4*alpha*s*r - 1, residue = (-4*alpha*s^2) % M
    all_candidates = {}
    for alpha in range(1, alpha_max + 1):
        for s in range(1, rs_max + 1):
            for r in range(1, rs_max + 1):
                M = 4 * alpha * s * r - 1
                if M < 2:
                    continue
                res = (-4 * alpha * s * s) % M
                key = (M, res)
                if key not in all_candidates:
                    all_candidates[key] = (alpha, r, s)

    print(f"Distinct (M, residue) candidates: {len(all_candidates)}")

    # Build index: for each modulus M, which primes have which residue
    # prime_by_mod[M][res] = set of primes
    print(f"Building prime residue index...")
    moduli = sorted(set(M for M, _ in all_candidates))
    prime_by_mod = {}
    for M in moduli:
        d = defaultdict(set)
        for p in primes:
            d[p % M].add(p)
        prime_by_mod[M] = d

    # Now build candidate -> covered primes
    candidate_primes = {}
    for (M, res) in all_candidates:
        covered = prime_by_mod[M].get(res, set())
        if covered:
            candidate_primes[(M, res)] = covered

    print(f"Candidates with coverage: {len(candidate_primes)}")
    print(f"Setup: {time.time() - t0:.1f}s")

    # Greedy set cover
    print(f"\n{'='*50}")
    print(f"GREEDY SET COVER")
    print(f"{'='*50}")
    t0 = time.time()

    uncovered = set(primes)
    chosen = []
    while uncovered:
        best = max(candidate_primes.keys(),
                   key=lambda k: len(candidate_primes[k] & uncovered))
        M, res = best
        alpha, r, s = all_candidates[best]
        n_covered = len(candidate_primes[best] & uncovered)
        if n_covered == 0:
            break
        chosen.append((alpha, r, s, M, res, n_covered))
        uncovered -= candidate_primes[best]

    print(f"Greedy cover: {len(chosen)} triples ({time.time() - t0:.1f}s)")
    if uncovered:
        print(f"UNCOVERED: {len(uncovered)} primes: {sorted(uncovered)[:10]}")

    # Display the cover
    print(f"\nTriples in greedy cover (sorted by coverage):")
    for i, (a, r, s, M, res, cnt) in enumerate(chosen):
        if i < 30 or cnt >= 5:
            print(f"  {i+1:3d}. (α={a}, r={r}, s={s})  M={M:5d}  "
                  f"p≡{res}(mod {M})  covers {cnt:5d}")
    triples_covering_1 = sum(1 for *_, cnt in chosen if cnt == 1)
    triples_covering_2 = sum(1 for *_, cnt in chosen if cnt == 2)
    print(f"\n  Covering 1 prime: {triples_covering_1}")
    print(f"  Covering 2 primes: {triples_covering_2}")

    # Cumulative coverage
    print(f"\n--- Cumulative Coverage ---")
    cumul = set()
    for i, (a, r, s, M, res, cnt) in enumerate(chosen):
        cumul |= candidate_primes.get((M, res), set())
        if (i+1) in [1, 2, 3, 5, 10, 20, 50, 100, 150, 200, 250,
                     300, len(chosen)]:
            pct = 100 * len(cumul) / len(primes)
            print(f"  Top {i+1:4d}: {len(cumul):6d}/{len(primes)} ({pct:.2f}%)")

    # Moduli analysis
    print(f"\n--- Moduli in Greedy Cover ---")
    greedy_moduli = Counter()
    for a, r, s, M, res, cnt in chosen:
        greedy_moduli[M] += 1
    for M, cnt in sorted(greedy_moduli.items()):
        print(f"  M={M:5d}: {cnt:3d} residue classes")

    # Scaling analysis
    print(f"\n--- Scaling: triples needed vs. limit ---")
    for sublimit in [10000, 50000, 100000, 200000, 500000, 1000000]:
        sub_p = set(p for p in primes if p <= sublimit)
        sub_uncov = set(sub_p)
        n_needed = 0
        for a, r, s, M, res, _ in chosen:
            before = len(sub_uncov)
            sub_uncov -= candidate_primes.get((M, res), set())
            if len(sub_uncov) < before:
                n_needed += 1
            if not sub_uncov:
                break
        print(f"  {sublimit:>8d}: {len(sub_p):6d} primes, {n_needed:4d} triples")

    # First-fit analysis: how many distinct triples does first-fit use?
    print(f"\n--- First-Fit vs Greedy ---")
    ff_usage = Counter()
    for p in primes:
        lo = (p + 3) // 4
        hi = (3 * p - 3) // 4
        for alpha in range(1, alpha_max + 1):
            found = False
            for s in range(1, rs_max + 1):
                val = p + 4 * alpha * s * s
                four_as = 4 * alpha * s
                for r in range(1, rs_max + 1):
                    M = four_as * r - 1
                    if M < 2 or val % M != 0:
                        continue
                    m = val // M
                    c = m * r - s
                    if c <= 0:
                        continue
                    A = alpha * s * c
                    if A < lo or A > hi:
                        continue
                    delta = 4 * A - p
                    if delta <= 0 or (s + c) % delta != 0:
                        continue
                    ff_usage[(alpha, r, s)] += 1
                    found = True
                    break
                if found:
                    break
            if found:
                break

    print(f"  First-fit uses {len(ff_usage)} distinct triples")
    print(f"  Greedy uses {len(chosen)} distinct triples")

    # Key structural question: are the moduli all ≡ 3 (mod 4)?
    print(f"\n--- Structural Properties ---")
    all_M = sorted(set(M for _, _, _, M, _, _ in chosen))
    print(f"  All M ≡ 3 (mod 4): {all(M % 4 == 3 for M in all_M)}")
    print(f"  Smallest M: {all_M[:10]}")
    print(f"  Largest M: {all_M[-5:]}")

    # Factorizations of moduli
    print(f"\n  Moduli factorizations:")
    for M in all_M[:20]:
        factors = []
        n = M
        for d in range(2, int(n**0.5) + 1):
            while n % d == 0:
                factors.append(d)
                n //= d
            if n == 1:
                break
        if n > 1:
            factors.append(n)
        label = '*'.join(map(str, factors)) if len(factors) > 1 else f"prime"
        print(f"    M={M:5d} = {label}")


if __name__ == "__main__":
    main()
