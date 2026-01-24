#!/usr/bin/env python3
"""Generate k-set certificates for Mordell-hard primes up to a bound.

This regenerates `data/kset_certificates_10M.jsonl` (default bound=10_000_000)
using the Bradford Type I/II congruence checks, restricted to the 10-k set.

Selection policy:
- Prefer Bradford Type II: search all k in KSET for a Type II witness first.
- Only fall back to Bradford Type I if **no** Type II witness exists in the 10-k set.

Usage:
  python3 scripts/make_kset_certificates.py --bound 10000000 --out data/kset_certificates_10M.jsonl
"""

from __future__ import annotations

import argparse
import json
from typing import Dict, List, Tuple


KSET = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
MORDELL_HARD_RESIDUES = {1, 121, 169, 289, 361, 529}


def sieve_primes(limit: int) -> List[int]:
    """Return list of primes <= limit via a simple bytearray sieve."""
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    import math
    for p in range(2, int(math.isqrt(limit)) + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start : limit + 1 : step] = b"\x00" * (((limit - start) // step) + 1)
    return [i for i in range(2, limit + 1) if sieve[i]]


def sieve_spf(limit: int) -> List[int]:
    """Smallest prime factor sieve up to limit."""
    spf = list(range(limit + 1))
    spf[0] = 0
    if limit >= 1:
        spf[1] = 1
    import math
    for i in range(2, int(math.isqrt(limit)) + 1):
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factorize(n: int, spf: List[int]) -> List[Tuple[int, int]]:
    out: List[Tuple[int, int]] = []
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out.append((p, e))
    return out


def divisors_square_from_factors(factors: List[Tuple[int, int]]) -> List[int]:
    divs = [1]
    for p, e in factors:
        new: List[int] = []
        powp = 1
        for _ in range(2 * e + 1):
            for d0 in divs:
                new.append(d0 * powp)
            powp *= p
        divs = new
    return divs


def divisors_square_leq_x(factors: List[Tuple[int, int]], x: int) -> List[int]:
    divs = [1]
    for p, e in factors:
        new: List[int] = []
        powp = 1
        for _ in range(2 * e + 1):
            for d0 in divs:
                v = d0 * powp
                if v <= x:
                    new.append(v)
            powp *= p
        divs = new
    return divs


def verify_identity(p: int, x: int, y: int, z: int) -> bool:
    return 4 * x * y * z == p * (x * y + x * z + y * z)


def typeII_solution(p: int, x: int, m: int, spf: List[int]):
    factors = factorize(x, spf)
    divs = divisors_square_leq_x(factors, x)
    target = (-x) % m
    for d in divs:
        if d % m != target:
            continue
        num_y = p * (x + d)
        if num_y % m:
            continue
        y = num_y // m
        x2_over_d = (x * x) // d
        num_z = p * (x + x2_over_d)
        if num_z % m:
            continue
        z = num_z // m
        if y > 0 and z > 0 and verify_identity(p, x, y, z):
            return d, y, z
    return None


def typeI_solution(p: int, x: int, m: int, spf: List[int]):
    factors = factorize(x, spf)
    divs = divisors_square_from_factors(factors)
    target = (-p * x) % m
    for d in divs:
        if d % m != target:
            continue
        num_y = p * x + d
        if num_y % m:
            continue
        y = num_y // m
        x2_over_d = (x * x) // d
        num_z = p * (x + p * x2_over_d)
        if num_z % m:
            continue
        z = num_z // m
        if y > 0 and z > 0 and verify_identity(p, x, y, z):
            return d, y, z
    return None


def find_cert(p: int, spf: List[int]) -> Dict:
    # Prefer Type II across the whole k-set
    for k in KSET:
        x = (p + 3) // 4 + k
        m = 3 + 4 * k
        t2 = typeII_solution(p, x, m, spf)
        if t2 is not None:
            d, y, z = t2
            return {
                "p": p,
                "residue_840": p % 840,
                "k": k,
                "m": m,
                "type": "II",
                "x": x,
                "d": d,
                "y": y,
                "z": z,
            }

    # Fallback: Type I (should be very rare)
    for k in KSET:
        x = (p + 3) // 4 + k
        m = 3 + 4 * k
        t1 = typeI_solution(p, x, m, spf)
        if t1 is not None:
            d, y, z = t1
            return {
                "p": p,
                "residue_840": p % 840,
                "k": k,
                "m": m,
                "type": "I",
                "x": x,
                "d": d,
                "y": y,
                "z": z,
            }

    raise RuntimeError(f"No certificate found for p={p}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bound", type=int, default=10_000_000)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    primes = sieve_primes(args.bound)
    hard_primes = [p for p in primes if (p % 840) in MORDELL_HARD_RESIDUES]

    max_x = (args.bound + 3) // 4 + max(KSET)
    spf = sieve_spf(max_x)

    with open(args.out, "w", encoding="utf-8") as f:
        for p in hard_primes:
            c = find_cert(p, spf)
            f.write(json.dumps(c, separators=(",", ":")) + "\n")

    print(f"Wrote {len(hard_primes)} certificates to {args.out}")


if __name__ == "__main__":
    main()
