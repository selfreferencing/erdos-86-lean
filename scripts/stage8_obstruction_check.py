#!/usr/bin/env python3
"""Stage 8 helper: explore QR obstruction patterns on the 10M hard-primes dataset.

This script is a data-mining aid used to support the conjectural covering lemma
in `ErdosStraus/CoveringUnbounded.lean`.

It computes, for each k in K10:
  - x_k = (p+3)//4 + k
  - m_k = 4k+3
and checks two predicates:
  - AllQR: every prime factor q of x_k is a square mod m_k
  - TargetNQR: -x_k is not a square mod m_k

Both predicates are computed in the literal ZMod sense, i.e. `a` is QR mod `m`
iff `a mod m` lies in the set {t^2 mod m : 0<=t<m}.

Usage:
  python3 scripts/stage8_obstruction_check.py data/kset_certificates_10M.jsonl

Notes:
  - This is not a proof. It just reproduces the empirical obstruction counts.
"""

from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict


def sieve_spf(n: int) -> list[int]:
    spf = list(range(n + 1))
    if n >= 0:
        spf[0] = 0
    if n >= 1:
        spf[1] = 1
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            step = i
            start = i * i
            for j in range(start, n + 1, step):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factor_spf(n: int, spf: list[int]) -> dict[int, int]:
    f: dict[int, int] = {}
    while n > 1:
        p = spf[n]
        if p <= 1:
            break
        c = 0
        while n % p == 0:
            n //= p
            c += 1
        f[p] = c
    return f


def squares_set(m: int) -> set[int]:
    return { (t * t) % m for t in range(m) }


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: stage8_obstruction_check.py <path_to_jsonl>", file=sys.stderr)
        return 2

    path = sys.argv[1]
    K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

    # Load primes
    ps: list[int] = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            obj = json.loads(line)
            ps.append(int(obj["p"]))

    max_p = max(ps)
    max_x = (max_p + 3) // 4 + max(K10)
    spf = sieve_spf(max_x)

    sq = { (4 * k + 3): squares_set(4 * k + 3) for k in K10 }

    obstruction_counts = Counter()
    all10 = 0

    for p in ps:
        x0 = (p + 3) // 4
        ok = True
        for k in K10:
            m = 4 * k + 3
            x = x0 + k
            factors = factor_spf(x, spf)
            allqr = all((q % m) in sq[m] for q in factors)
            targetnqr = ((-x) % m) not in sq[m]
            if allqr and targetnqr:
                obstruction_counts[k] += 1
            else:
                ok = False
        if ok:
            all10 += 1

    print(f"dataset size: {len(ps)}")
    print("obstruction counts (AllQR & TargetNQR):")
    for k in K10:
        print(f"  k={k:2d}  m={4*k+3:3d}  count={obstruction_counts[k]}")
    print(f"all-10 simultaneous obstructions: {all10}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
