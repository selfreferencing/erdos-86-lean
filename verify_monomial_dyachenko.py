#!/usr/bin/env python3
"""
Verify that L1C's monomial parametrization (x,y,z) maps to Dyachenko's (alpha,r,s).

For each certificate (p, delta, b, c):
  A = (p+delta)/4
  u = delta*b - A (L4A divisor)
  From Dyachenko: u = alpha*s^2, b = alpha*r*s, M = 4b-1

From monomial: d = x^2*y = u, A = x*y*z

Claim: y = alpha, x = s, z = A/(s*alpha)
"""

import csv
import math
from collections import Counter


def integer_sqrt_divisors(n):
    if n <= 0:
        return []
    results = []
    x = 1
    while x * x <= n:
        if n % (x * x) == 0:
            results.append(x)
        x += 1
    return results


def find_alpha_r_s(b, u):
    """Find (alpha, r, s) with b = alpha*r*s and u = alpha*s^2."""
    results = []
    # u = alpha*s^2, so s^2 | u
    s = 1
    while s * s <= u:
        if u % (s * s) == 0:
            alpha = u // (s * s)
            if alpha > 0:
                # Check b = alpha*r*s
                if b % (alpha * s) == 0:
                    r = b // (alpha * s)
                    if r > 0:
                        results.append((alpha, r, s))
        s += 1
    return results


def main():
    csv_path = "/Users/kvallie2/Desktop/esc_stage8/witnesses_1000000.csv"

    rows = []
    with open(csv_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append({
                "p": int(row["p"]),
                "delta": int(row["offset"]),
                "b": int(row["b"]),
                "c": int(row["c"]),
            })

    print(f"Testing {len(rows)} certificates\n")

    match_count = 0
    mismatch_count = 0
    mismatches = []

    for row in rows:
        p, delta, b, c = row["p"], row["delta"], row["b"], row["c"]
        A = (p + delta) // 4
        u = delta * b - A  # L4A divisor = d

        # Find Dyachenko (alpha, r, s) - use minimal alpha (= squarefree core)
        ars_list = find_alpha_r_s(b, u)
        if not ars_list:
            print(f"  NO Dyachenko decomposition for p={p}!")
            continue

        # Use the decomposition with smallest alpha (standard choice)
        alpha, r, s = min(ars_list, key=lambda t: t[0])

        # Find monomial (x, y, z) - use minimal x
        xs = integer_sqrt_divisors(u)
        mono = None
        for x in xs:
            y = u // (x * x)
            xy = x * y
            if A % xy == 0:
                z = A // xy
                if z > 0:
                    mono = (x, y, z)
                    break  # minimal x

        if mono is None:
            print(f"  NO monomial decomposition for p={p}!")
            continue

        x, y, z = mono

        # Check: does (x, y) = (s, alpha)?
        if x == s and y == alpha:
            match_count += 1
        else:
            mismatch_count += 1
            if len(mismatches) < 20:
                mismatches.append((p, x, y, z, s, alpha, r, u, A))

    print("=" * 70)
    print("MONOMIAL (x,y) vs DYACHENKO (s,alpha) COMPARISON")
    print("=" * 70)
    print(f"  (x=s, y=alpha) matches: {match_count}/{len(rows)} ({match_count/len(rows)*100:.1f}%)")
    print(f"  Mismatches: {mismatch_count}/{len(rows)}")

    if mismatches:
        print(f"\n  First {len(mismatches)} mismatches:")
        print(f"  {'p':>10s}  {'x':>5s}  {'y':>5s}  {'z':>8s}  {'s':>5s}  {'alpha':>5s}  {'r':>5s}  {'u':>8s}  {'A':>8s}")
        for p, x, y, z, s, alpha, r, u, A in mismatches:
            print(f"  {p:>10d}  {x:>5d}  {y:>5d}  {z:>8d}  {s:>5d}  {alpha:>5d}  {r:>5d}  {u:>8d}  {A:>8d}")

        # Check if they're permuted or related
        print("\n  Checking relationships:")
        for p, x, y, z, s, alpha, r, u, A in mismatches[:5]:
            print(f"    p={p}: x={x}, y={y} vs s={s}, alpha={alpha}")
            print(f"      x^2*y = {x*x*y}, alpha*s^2 = {alpha*s*s}, u = {u}")
            print(f"      x*y*z = {x*y*z}, A = {A}")
            print(f"      x/s = {x/s if s != 0 else 'N/A'}, y/alpha = {y/alpha if alpha != 0 else 'N/A'}")
    else:
        print("\n  PERFECT MATCH: For EVERY certificate, the minimal-x monomial")
        print("  decomposition gives (x, y) = (s, alpha) from Dyachenko.")
        print("  So z = A/(s*alpha) = A/u * s = (A*s)/u")
        print("\n  This means L1C's 'monomial parametrization' is EXACTLY the")
        print("  Dyachenko parametrization (alpha, r, s) in disguise:")
        print("    x = s (Dyachenko's s)")
        print("    y = alpha (Dyachenko's alpha)")
        print("    z = A/(s*alpha)")
        print("  The monomial adds ZERO new information.")


if __name__ == "__main__":
    main()
