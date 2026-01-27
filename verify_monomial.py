#!/usr/bin/env python3
"""
Verify GPT L1C's "monomial parametrization" claim on all 750 Type II certificates.

For each certificate (p, offset, b, c):
  A = (p + offset) / 4
  d = offset * b - A          (the smaller factor of A^2)

Monomial parametrization: find x, y, z > 0 with A = xyz, d = x^2 * y.
This forces d | A^2 automatically since x^2*y | (xyz)^2 = x^2*y^2*z^2.

Also test moving-modulus properties:
  delta = 4*A - p = 4*xyz - p
  Congruence: x^2*y + xyz = 0 mod delta, i.e., xy(x+z) = 0 mod delta
"""

import csv
import math
from collections import Counter


def integer_sqrt_divisors(n):
    """Return all positive x such that x^2 divides n."""
    if n <= 0:
        return []
    results = []
    x = 1
    while x * x <= n:
        if n % (x * x) == 0:
            results.append(x)
        x += 1
    return results


def factorize(n):
    """Simple trial division factorization."""
    if n <= 1:
        return {}
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def main():
    csv_path = "/Users/kvallie2/Desktop/esc_stage8/witnesses_1000000.csv"

    rows = []
    with open(csv_path, "r") as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append({
                "p": int(row["p"]),
                "offset": int(row["offset"]),
                "b": int(row["b"]),
                "c": int(row["c"]),
            })

    print(f"Loaded {len(rows)} Type II certificates.\n")

    # Counters
    sanity_pass = 0
    mono_success = 0
    mono_fail = 0
    failures = []

    x_vals_min = []  # minimal x for each cert
    y_vals_min = []
    z_vals_min = []
    num_decomps = Counter()

    # Moving modulus stats
    xy_xz_gcd_delta = []  # gcd(xy(x+z), delta)

    # Algebraic proof that monomial always works when d | A^2
    algebraic_always = True

    for row in rows:
        p = row["p"]
        delta = row["offset"]
        b = row["b"]
        c = row["c"]

        A = (p + delta) // 4
        d = delta * b - A
        e = delta * c - A

        if d * e != A * A:
            print(f"  SANITY FAIL: p={p}")
            continue
        sanity_pass += 1

        # Find ALL valid (x,y,z) decompositions
        xs = integer_sqrt_divisors(d)
        valid_decomps = []
        for x in xs:
            y = d // (x * x)
            if y <= 0:
                continue
            xy = x * y
            if A % xy == 0:
                z = A // xy
                if z > 0:
                    # Double-check
                    assert x * y * z == A
                    assert x * x * y == d
                    valid_decomps.append((x, y, z))

        num_decomps[len(valid_decomps)] += 1

        if valid_decomps:
            mono_success += 1
            # Take minimal x decomposition
            best = min(valid_decomps, key=lambda t: t[0])
            x0, y0, z0 = best
            x_vals_min.append(x0)
            y_vals_min.append(y0)
            z_vals_min.append(z0)

            # Moving modulus analysis for minimal decomposition
            xpz = x0 + z0
            product = x0 * y0 * xpz
            g = math.gcd(product, delta)
            xy_xz_gcd_delta.append(g)

            # Verify congruence: d + A = 0 mod delta
            # d + A = x^2*y + xyz = xy(x+z)
            # We need xy(x+z) = 0 mod delta
            assert (d + A) % delta == 0, f"d+A not 0 mod delta for p={p}"
            assert product % delta == 0, f"xy(x+z) not 0 mod delta for p={p}"
        else:
            mono_fail += 1
            failures.append((p, A, d, e, xs))

    # ============ RESULTS ============
    print("=" * 70)
    print("MONOMIAL PARAMETRIZATION: A = xyz, d = x^2*y")
    print("=" * 70)
    print(f"  Sanity (d*e = A^2): {sanity_pass}/{len(rows)}")
    print(f"  Monomial success: {mono_success}/{len(rows)} ({mono_success/len(rows)*100:.1f}%)")
    print(f"  Monomial failures: {mono_fail}/{len(rows)}")
    print()

    print("NUMBER OF DECOMPOSITIONS PER CERTIFICATE:")
    for k in sorted(num_decomps.keys()):
        print(f"  {k} decomposition(s): {num_decomps[k]} certificates")
    print()

    if failures:
        print("=" * 70)
        print(f"FIRST {min(20, len(failures))} FAILURES")
        print("=" * 70)
        for p, A, d, e, xs in failures[:20]:
            fA = factorize(A)
            fd = factorize(d)
            fA_str = " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(fA.items()))
            fd_str = " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(fd.items()))
            print(f"  p={p}: A={A} = {fA_str}")
            print(f"         d={d} = {fd_str}")
            print(f"         x values with x^2|d: {xs}")
            # Show why each x fails
            for x in xs:
                y = d // (x * x)
                xy = x * y
                if A % xy != 0:
                    print(f"         x={x}: y={y}, xy={xy}, A%xy={A%xy} != 0")
                else:
                    print(f"         x={x}: y={y}, z={A//xy} (should have worked!)")
            print()

        # Deeper failure analysis
        print("FAILURE PATTERN ANALYSIS:")
        for p, A, d, e, xs in failures[:10]:
            fA = factorize(A)
            fd = factorize(d)
            print(f"\n  p={p}, A={A}, d={d}")
            print(f"  A factors: {fA}")
            print(f"  d factors: {fd}")
            # Check: for each prime q in d, what's v_q(d) vs 2*v_q(A)?
            for q, vd in sorted(fd.items()):
                vA = fA.get(q, 0)
                print(f"    q={q}: v_q(d)={vd}, v_q(A)={vA}, 2*v_q(A)={2*vA}, "
                      f"need x_q in [{max(0,vd-vA)}, {vd//2}]")
                if max(0, vd - vA) > vd // 2:
                    print(f"      *** IMPOSSIBLE: interval empty!")
    else:
        print("NO FAILURES: monomial parametrization holds for ALL 750 certificates!")

    # Distribution stats (only if we have successes)
    if x_vals_min:
        print()
        print("=" * 70)
        print("MINIMAL-x DECOMPOSITION STATISTICS")
        print("=" * 70)

        x_ctr = Counter(x_vals_min)
        print("\n  x distribution (top 20):")
        for val, cnt in sorted(x_ctr.items(), key=lambda t: -t[1])[:20]:
            print(f"    x={val}: {cnt} certs ({cnt/len(x_vals_min)*100:.1f}%)")
        print(f"  Distinct x values: {len(x_ctr)}")
        print(f"  Range: [{min(x_vals_min)}, {max(x_vals_min)}], "
              f"mean={sum(x_vals_min)/len(x_vals_min):.2f}, "
              f"median={sorted(x_vals_min)[len(x_vals_min)//2]}")

        y_ctr = Counter(y_vals_min)
        print(f"\n  y distribution (top 20):")
        for val, cnt in sorted(y_ctr.items(), key=lambda t: -t[1])[:20]:
            print(f"    y={val}: {cnt} certs ({cnt/len(y_vals_min)*100:.1f}%)")
        print(f"  Distinct y values: {len(y_ctr)}")
        print(f"  Range: [{min(y_vals_min)}, {max(y_vals_min)}], "
              f"mean={sum(y_vals_min)/len(y_vals_min):.2f}, "
              f"median={sorted(y_vals_min)[len(y_vals_min)//2]}")

        print(f"\n  z distribution (top 20):")
        z_ctr = Counter(z_vals_min)
        for val, cnt in sorted(z_ctr.items(), key=lambda t: -t[1])[:20]:
            print(f"    z={val}: {cnt} certs ({cnt/len(z_vals_min)*100:.1f}%)")
        print(f"  Distinct z values: {len(z_ctr)}")
        print(f"  Range: [{min(z_vals_min)}, {max(z_vals_min)}], "
              f"mean={sum(z_vals_min)/len(z_vals_min):.2f}, "
              f"median={sorted(z_vals_min)[len(z_vals_min)//2]}")

    # Moving modulus analysis
    if xy_xz_gcd_delta:
        print()
        print("=" * 70)
        print("MOVING MODULUS ANALYSIS")
        print("=" * 70)
        print(f"  Verified xy(x+z) = 0 mod delta: {len(xy_xz_gcd_delta)}/{mono_success}")
        g_ctr = Counter(xy_xz_gcd_delta)
        print(f"\n  gcd(xy(x+z), delta) distribution (top 15):")
        for val, cnt in sorted(g_ctr.items(), key=lambda t: -t[1])[:15]:
            print(f"    gcd={val}: {cnt} certs")

        # Check: does delta always divide xy(x+z)?
        divides_count = sum(1 for g in xy_xz_gcd_delta if True)  # already asserted
        print(f"\n  delta | xy(x+z) for all: YES (verified by assertion)")

        # Ratio analysis: how much of delta does xy vs (x+z) contribute?
        print(f"\n  Key insight: d + A = xy(x+z) and delta | (d+A) always holds")
        print(f"  because d+A = delta*b - A + A = delta*b.")
        print(f"  So xy(x+z) = delta*b is TRIVIALLY TRUE.")
        print(f"  The monomial parametrization doesn't add information")
        print(f"  beyond what d|A^2 already gives.")

    # Theoretical analysis
    print()
    print("=" * 70)
    print("THEORETICAL ANALYSIS: IS MONOMIAL ALWAYS POSSIBLE?")
    print("=" * 70)
    print("  Given d | A^2, write A = prod p_i^{a_i}, d = prod p_i^{d_i}.")
    print("  Need x with 2*x_i <= d_i and x_i >= d_i - a_i for each prime p_i.")
    print("  This requires d_i - a_i <= d_i/2, i.e., d_i <= 2*a_i.")
    print("  But d | A^2 gives d_i <= 2*a_i. So the interval [d_i-a_i, d_i/2]")
    print("  is always non-empty.")
    print()
    if mono_fail == 0:
        print("  CONCLUSION: Monomial parametrization is ALWAYS possible when d | A^2.")
        print("  This is a TAUTOLOGICAL reformulation, not a new constraint.")
        print("  It adds no information beyond d | A^2.")
    else:
        print(f"  WARNING: {mono_fail} failures found! The theoretical argument")
        print(f"  may have a flaw. Check failure analysis above.")

    print()
    print("=" * 70)
    print("VERDICT ON L1C's MONOMIAL PARAMETRIZATION")
    print("=" * 70)
    print("  1. CORRECTNESS: The parametrization A=xyz, d=x^2*y exists whenever d|A^2")
    if mono_fail == 0:
        print("     Verified: 750/750 certificates admit the decomposition")
    print("  2. NOVELTY: LOW - it's a reformulation of d|A^2, not a new condition")
    print("  3. The 'moving modulus' xy(x+z) = 0 mod delta reduces to delta*b = delta*b")
    print("  4. The monomial parametrization does NOT simplify the core difficulty:")
    print("     finding d = -A mod delta (which is the L4A characterization)")
    print("  5. Blichfeldt/lattice approach in (x,y,z)-space is 3D vs 1D (d-space)")
    print("     This INCREASES dimensionality without adding constraints")


if __name__ == "__main__":
    main()
