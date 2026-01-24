#!/usr/bin/env python3
"""Stage 8 sanity-check: random sampling beyond 1e7.

This script is **not** part of the formal Lean development.
It exists to provide quick empirical reassurance that the K10 set
continues to find Bradford Type II witnesses beyond the Stage 7 dataset.

It samples Mordell-hard primes in an interval, then for each prime tries the
ten k values K10 = {5,7,9,11,14,17,19,23,26,29} and searches for a Type II
witness divisor d of x^2 with d ≡ -x (mod m), where m = 4k+3 and x = (p+m)/4.

Run:
  python3 scripts/stage8_k10_random_check.py
"""

from __future__ import annotations

import random
from collections import Counter
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Tuple

from sympy import factorint, nextprime


MH = {1, 121, 169, 289, 361, 529}
K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]


def m_of_k(k: int) -> int:
    return 4 * k + 3


def x_of_p_k(p: int, k: int) -> int:
    m = m_of_k(k)
    # For Mordell-hard primes we have p ≡ 1 (mod 4), so x = ceil(p/4)+k = (p+3)/4 + k = (p+m)/4.
    return (p + m) // 4


def divisors_of_x2(f: Dict[int, int]) -> List[int]:
    """All positive divisors of x^2 from factorization f of x."""
    divs = [1]
    for q, e in f.items():
        pow_list = [q ** t for t in range(2 * e + 1)]
        divs = [d * pp for d in divs for pp in pow_list]
    return divs


def find_typeII_witness_d(p: int, k: int) -> Optional[int]:
    m = m_of_k(k)
    x = x_of_p_k(p, k)
    target = (-x) % m
    f = factorint(x)
    for d in divisors_of_x2(f):
        if d % m == target:
            return d
    return None


def random_mordell_hard_primes(n: int, lo: int, hi: int, seed: int = 0) -> List[int]:
    rng = random.Random(seed)
    out: List[int] = []
    while len(out) < n:
        a = rng.randrange(lo, hi)
        p = int(nextprime(a))
        if p >= hi:
            continue
        if p % 840 in MH:
            out.append(p)
    return out


def main() -> None:
    lo = 10**7
    hi = 10**8
    n = 200
    primes = random_mordell_hard_primes(n, lo, hi, seed=0)

    k_hist = Counter()
    failures: List[int] = []

    for p in primes:
        found = False
        for k in K10:
            d = find_typeII_witness_d(p, k)
            if d is not None:
                k_hist[k] += 1
                found = True
                break
        if not found:
            failures.append(p)

    print(f"Sampled {n} Mordell-hard primes in [{lo}, {hi}).")
    print("k distribution (first k that works):")
    for k in K10:
        print(f"  k={k:2d}: {k_hist[k]}")
    if failures:
        print("Failures:", failures[:20], "..." if len(failures) > 20 else "")
    else:
        print("No failures in sample.")


if __name__ == "__main__":
    main()
