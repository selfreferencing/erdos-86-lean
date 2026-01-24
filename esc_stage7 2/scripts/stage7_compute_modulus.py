"""Stage 7 helper: compute master moduli and factorizations.

This script is purely informational: it reproduces the numbers embedded in
`ErdosStraus/CoveringUnbounded.lean` and documented in `docs/stage7_covering_analysis.md`.

Run:
  python3 scripts/stage7_compute_modulus.py
"""

from __future__ import annotations

import math
from functools import reduce


def lcm(a: int, b: int) -> int:
    return a * b // math.gcd(a, b)


def factor(n: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            out.append((d, e))
        d = 3 if d == 2 else d + 2
    if n > 1:
        out.append((n, 1))
    return out


def main() -> None:
    K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
    mvals = [3 + 4 * k for k in K10]
    Mm = reduce(lcm, mvals, 1)
    M = lcm(840, Mm)

    print("K10:", K10)
    print("m-values:", mvals)
    print("Mm = lcm(m-values) =", Mm)
    print("factor(Mm) =", factor(Mm))
    print("M = lcm(840, Mm) =", M)
    print("factor(M) =", factor(M))


if __name__ == "__main__":
    main()
