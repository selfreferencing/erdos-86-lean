#!/usr/bin/env python3
"""
ed2_covering_system.py

Find a finite set of (alpha, r, s) triples such that for every prime
p ≡ 1 (mod 24), at least one triple satisfies:

    (4*alpha*s*r - 1) | (p + 4*alpha*s^2)

The witness construction: given a covering triple,
    m = (p + 4*alpha*s^2) / M     where M = 4*alpha*s*r - 1
    c' = m*r - s
    A = alpha * s * c'
    b' = s, d' = r
Then A = alpha*b'*c' and (4A-p) | (b'+c').

Strategy: directly test primes and collect which triples are needed.

Usage:
    python3 ed2_covering_system.py
    python3 ed2_covering_system.py --limit 1000000
"""

from __future__ import annotations
import argparse
import math
import time
from collections import Counter
from typing import Optional


def sieve(n: int) -> bytearray:
    is_prime = bytearray(b'\x01') * (n + 1)
    is_prime[0] = is_prime[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if is_prime[i]:
            is_prime[i*i::i] = b'\x00' * len(is_prime[i*i::i])
    return is_prime


def find_triple(p: int, alpha_max: int = 5, rs_max: int = 30) -> Optional[tuple]:
    """Find smallest (alpha, r, s) covering prime p."""
    lo = (p + 3) // 4
    hi = (3 * p - 3) // 4
    for alpha in range(1, alpha_max + 1):
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
                return (alpha, r, s, A, s, c, delta)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=200000)
    ap.add_argument("--alpha-max", type=int, default=5)
    ap.add_argument("--rs-max", type=int, default=30)
    args = ap.parse_args()

    limit = args.limit
    print(f"ED2 Covering System: primes p ≡ 1 (mod 24) up to {limit}")

    t0 = time.time()
    is_prime = sieve(limit)

    usage = Counter()
    failures = []
    total = 0

    for p in range(25, limit + 1):
        if p % 24 != 1 or not is_prime[p]:
            continue
        total += 1
        result = find_triple(p, args.alpha_max, args.rs_max)
        if result is None:
            failures.append(p)
        else:
            alpha, r, s = result[0], result[1], result[2]
            usage[(alpha, r, s)] += 1

    elapsed = time.time() - t0
    print(f"Checked {total} primes in {elapsed:.1f}s")

    if failures:
        print(f"FAILURES ({len(failures)}): {failures[:20]}")
    else:
        print(f"All covered!")

    print(f"\nDistinct triples: {len(usage)}")
    print(f"\nBy frequency:")
    for (a, r, s), cnt in usage.most_common():
        M = 4*a*s*r - 1
        res = (-4*a*s*s) % M
        print(f"  (α={a}, r={r}, s={s})  M={M}  p≡{res}(mod {M})  x{cnt}")

    # Check coverage mod Q
    triples = sorted(usage.keys())
    moduli = [4*a*s*r - 1 for a, r, s in triples]
    Q = 24
    for m in moduli:
        Q = math.lcm(Q, m)
    if Q < 10**9:
        target = set(range(1, Q, 24))
        covered = set()
        for a, r, s in triples:
            M = 4*a*s*r - 1
            res = (-4*a*s*s) % M
            for t in target:
                if t % M == res:
                    covered.add(t)
        if covered == target:
            print(f"\nQ = {Q}: FULL coverage ({len(target)}/{len(target)})")
        else:
            print(f"\nQ = {Q}: {len(covered)}/{len(target)}")
            uncov = sorted(target - covered)[:20]
            print(f"  Uncovered: {uncov}")
    else:
        print(f"\nQ = {Q} (too large for direct check)")

    # Full p ≡ 1 (mod 4) check
    print(f"\n--- Full p ≡ 1 (mod 4) verification ---")
    fc = 0
    ff = []
    for p in range(5, limit + 1):
        if p % 4 != 1 or not is_prime[p]:
            continue
        fc += 1
        if p % 8 == 5 or p % 3 == 2:
            continue
        if find_triple(p, args.alpha_max, args.rs_max) is None:
            ff.append(p)
    if ff:
        print(f"  FAILURES: {ff[:20]}")
    else:
        print(f"  All {fc} primes covered!")


if __name__ == "__main__":
    main()
