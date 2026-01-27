#!/usr/bin/env python3
"""
ed2_witness_to_lean.py (GPT Part 3)

Given a prime p, search for (α, d', b', c') with:
  α>0, d'>0, b'>0, c'>0,
  p < 4*α*b'*c',
  b'+c' = (4*α*b'*c' - p) * d'

Then print the Lean 4 proof term:
  ⟨α, d', b', c', by norm_num, by norm_num, by norm_num, by norm_num,
   by norm_num, by norm_num⟩

Usage:
  python3 ed2_witness_to_lean.py 73         # single prime
  python3 ed2_witness_to_lean.py --test     # built-in tests
"""

from __future__ import annotations
import argparse
from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class Witness:
    a: int     # α
    d: int     # d'
    b: int     # b'
    c: int     # c'

    def check(self, p: int) -> bool:
        a, d, b, c = self.a, self.d, self.b, self.c
        if not (a > 0 and d > 0 and b > 0 and c > 0):
            return False
        lhs = b + c
        rhs_factor = 4 * a * b * c - p
        if not (p < 4 * a * b * c):
            return False
        return lhs == rhs_factor * d


def find_witness(p: int, A: int, B: int, C: int) -> Optional[Witness]:
    """Brute force: try small α, b', c' and solve d' by divisibility."""
    for a in range(1, A + 1):
        for b in range(1, B + 1):
            for c in range(1, C + 1):
                t = 4 * a * b * c - p
                if t <= 0:
                    continue
                s = b + c
                if s % t != 0:
                    continue
                d = s // t
                w = Witness(a=a, d=d, b=b, c=c)
                if w.check(p):
                    return w
    return None


def lean_term(w: Witness) -> str:
    return (
        f"⟨{w.a}, {w.d}, {w.b}, {w.c}, "
        f"by norm_num, by norm_num, by norm_num, by norm_num, "
        f"by norm_num, by norm_num⟩"
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("p", type=int, nargs="?", help="prime p")
    ap.add_argument("--A", type=int, default=50, help="search bound for α")
    ap.add_argument("--B", type=int, default=200, help="search bound for b'")
    ap.add_argument("--C", type=int, default=200, help="search bound for c'")
    ap.add_argument("--test", action="store_true", help="run built-in tests")
    args = ap.parse_args()

    if args.test:
        tests = [5, 13, 17, 29, 37, 41, 53]
        for p in tests:
            w = find_witness(p, args.A, args.B, args.C)
            if w is None:
                raise SystemExit(
                    f"FAIL: no witness found for p={p} with bounds "
                    f"A={args.A},B={args.B},C={args.C}"
                )
            if not w.check(p):
                raise SystemExit(
                    f"FAIL: witness does not verify for p={p}: {w}"
                )
            print(f"p={p}  witness=(α={w.a}, d'={w.d}, b'={w.b}, c'={w.c})")
            print(lean_term(w))
        print("OK: all tests passed.")
        return

    if args.p is None:
        raise SystemExit("Provide p or use --test")

    p = args.p
    w = find_witness(p, args.A, args.B, args.C)
    if w is None:
        raise SystemExit(
            f"no witness found for p={p} with bounds "
            f"A={args.A},B={args.B},C={args.C}"
        )
    if not w.check(p):
        raise SystemExit(
            f"internal error: found witness fails check for p={p}: {w}"
        )

    print(lean_term(w))


if __name__ == "__main__":
    main()
