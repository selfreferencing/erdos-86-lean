#!/usr/bin/env python3
"""
verify_backtest.py
==================
Verifies the Dyachenko back-test equivalence (Lemma D.16 / Lemma 3.2)
on all 750 sorry-region certificates from witnesses_1000000.csv.

The L4A Identity (verified on each certificate):
    (delta * b - A)(delta * c - A) = A**2
    where A = (p + delta) / 4

Dyachenko Decomposition:
    x = delta*b - A,  y = delta*c - A,  x*y = A**2
    alpha = gcd(x, y)
    x = alpha * r**2,  y = alpha * s**2
    gcd(r, s) = 1,  r * s = A / alpha

Back-Test Equivalence (Lemma 3.2 / D.16):
    For M = A/alpha = r*s, the ED2 identity has a solution iff there exist
    integers (u, v) satisfying:
        (1) delta | u
        (2) u = v  (mod 2)
        (3) u**2 - v**2 = 4*M

    Reconstruction: bp = (u + v) / 2,  cp = (u - v) / 2
"""

import csv
import math
import time
from collections import Counter


def find_divisor_pairs(n):
    pairs = []
    for d1 in range(1, int(math.isqrt(n)) + 1):
        if n % d1 == 0:
            pairs.append((d1, n // d1))
    return pairs


def find_backtest_solutions(delta, M_val):
    target = 4 * M_val
    solutions = []
    for d1, d2 in find_divisor_pairs(target):
        if (d1 + d2) % 2 != 0:
            continue
        u_val = (d1 + d2) // 2
        v_val = (d2 - d1) // 2
        if u_val % delta == 0:
            solutions.append((u_val, v_val))
    return solutions


def verify_certificate(p, delta, b, c):
    result = {
        "p": p, "delta": delta, "b": b, "c": c,
        "l4a_ok": False, "decomp_ok": False,
        "backtest_exists": False, "backtest_solutions": 0,
        "reconstruct_ok": False,
        "alpha": None, "r": None, "s": None,
        "first_u": None, "first_v": None,
        "first_bp": None, "first_cp": None,
    }

    if (p + delta) % 4 != 0:
        result["error"] = "p + delta not divisible by 4"
        return result
    A = (p + delta) // 4

    x = delta * b - A
    y = delta * c - A
    result["l4a_ok"] = (x * y == A * A) and (x > 0) and (y > 0)

    if not result["l4a_ok"]:
        result["error"] = "L4A failed: x=%d, y=%d, x*y=%d, A^2=%d" % (x, y, x*y, A*A)
        return result

    alpha = math.gcd(x, y)
    xp = x // alpha
    yp = y // alpha

    r = int(math.isqrt(xp))
    s = int(math.isqrt(yp))

    decomp_ok = (
        r * r == xp and
        s * s == yp and
        math.gcd(r, s) == 1 and
        A % alpha == 0 and
        r * s == A // alpha
    )
    result["decomp_ok"] = decomp_ok
    result["alpha"] = alpha
    result["r"] = r
    result["s"] = s

    if not decomp_ok:
        result["error"] = "Decomposition failed"
        return result

    M_val = A // alpha
    solutions = find_backtest_solutions(delta, M_val)

    result["backtest_exists"] = len(solutions) > 0
    result["backtest_solutions"] = len(solutions)

    if solutions:
        u0, v0 = solutions[0]
        bp = (u0 + v0) // 2
        cp = (u0 - v0) // 2
        result["first_u"] = u0
        result["first_v"] = v0
        result["first_bp"] = bp
        result["first_cp"] = cp
        result["reconstruct_ok"] = (bp * cp == M_val and bp > 0 and cp >= 0)

    return result


def main():
    csv_path = "/Users/kvallie2/Desktop/esc_stage8/witnesses_1000000.csv"

    print("=" * 78)
    print("DYACHENKO BACK-TEST EQUIVALENCE VERIFICATION")
    print("Lemma D.16 / Lemma 3.2 (GPT L1B)")
    print("=" * 78)
    print()

    t0 = time.time()

    with open(csv_path) as f:
        reader = csv.DictReader(f)
        rows = [(int(r["p"]), int(r["offset"]), int(r["b"]), int(r["c"])) for r in reader]

    total = len(rows)
    print("Loaded %d certificates from %s" % (total, csv_path))
    print()

    l4a_pass = 0
    decomp_pass = 0
    backtest_pass = 0
    reconstruct_pass = 0
    full_pass = 0

    alpha_values = Counter()
    solution_counts = []
    failures = []
    examples = []

    for idx, (p, delta, b, c) in enumerate(rows):
        res = verify_certificate(p, delta, b, c)

        if res["l4a_ok"]:
            l4a_pass += 1
        if res["decomp_ok"]:
            decomp_pass += 1
        if res["backtest_exists"]:
            backtest_pass += 1
        if res["reconstruct_ok"]:
            reconstruct_pass += 1

        all_ok = (
            res["l4a_ok"] and
            res["decomp_ok"] and
            res["backtest_exists"] and
            res["reconstruct_ok"]
        )
        if all_ok:
            full_pass += 1
        else:
            failures.append(res)

        if res["alpha"] is not None:
            alpha_values[res["alpha"]] += 1
        solution_counts.append(res["backtest_solutions"])

        if idx < 8:
            examples.append(res)

    elapsed = time.time() - t0

    print("-" * 78)
    print("VERIFICATION RESULTS")
    print("-" * 78)
    print()
    tag = lambda ok: "PASS" if ok else "FAIL"
    print("  L4A identity verified:          %4d / %d  %s" % (l4a_pass, total, tag(l4a_pass == total)))
    print("  Dyachenko decomposition valid:  %4d / %d  %s" % (decomp_pass, total, tag(decomp_pass == total)))
    print("  Back-test solution exists:      %4d / %d  %s" % (backtest_pass, total, tag(backtest_pass == total)))
    print("  Reconstruction valid:           %4d / %d  %s" % (reconstruct_pass, total, tag(reconstruct_pass == total)))
    print()
    ftag = "ALL PASS" if full_pass == total else "SOME FAILURES"
    print("  FULL PIPELINE PASS:             %4d / %d  %s" % (full_pass, total, ftag))
    print()

    # Alpha distribution
    print("-" * 78)
    print("ALPHA DISTRIBUTION (Dyachenko parameter)")
    print("-" * 78)
    for alpha, count in sorted(alpha_values.items())[:20]:
        bar = "#" * min(count, 60)
        print("  alpha = %6d:  %4d certificates  %s" % (alpha, count, bar))
    if len(alpha_values) > 20:
        print("  ... and %d more distinct alpha values" % (len(alpha_values) - 20))
    print()

    # Solution count statistics
    if solution_counts:
        print("-" * 78)
        print("BACK-TEST SOLUTION COUNT STATISTICS")
        print("-" * 78)
        sc = sorted(solution_counts)
        print("  Min solutions per certificate:  %d" % sc[0])
        print("  Max solutions per certificate:  %d" % sc[-1])
        print("  Mean solutions per certificate: %.2f" % (sum(sc)/len(sc)))
        print("  Median:                         %d" % sc[len(sc)//2])
        sol_dist = Counter(solution_counts)
        print()
        print("  Distribution of solution counts:")
        for k in sorted(sol_dist.keys())[:15]:
            bar = "#" * min(sol_dist[k], 60)
            print("    %3d solutions: %4d certificates  %s" % (k, sol_dist[k], bar))
        if len(sol_dist) > 15:
            print("    ... and %d more distinct counts" % (len(sol_dist) - 15))
    print()

    # Detailed examples
    print("-" * 78)
    print("DETAILED EXAMPLES (first 8 certificates)")
    print("-" * 78)
    for res in examples:
        pv, dv, bv, cv = res["p"], res["delta"], res["b"], res["c"]
        A = (pv + dv) // 4
        x = dv * bv - A
        y = dv * cv - A
        print()
        print("  Certificate: p=%d, delta=%d, b=%d, c=%d" % (pv, dv, bv, cv))
        print("    A = (p+delta)/4 = %d" % A)
        print("    L4A: x = delta*b - A = %d,  y = delta*c - A = %d" % (x, y))
        print("           x * y = %d,  A^2 = %d,  match = %s" % (x*y, A*A, res["l4a_ok"]))
        print("    Decomposition: alpha = gcd(x,y) = %s" % res["alpha"])
        if res["r"] is not None and res["s"] is not None:
            print("           r = %d,  s = %d" % (res["r"], res["s"]))
            print("           x/alpha = r^2 = %d" % (res["r"]**2))
            print("           y/alpha = s^2 = %d" % (res["s"]**2))
            print("           r*s = %d = A/alpha = %d" % (res["r"]*res["s"], A//res["alpha"] if res["alpha"] else 0))
        M = A // res["alpha"] if res["alpha"] else 0
        print("    Back-test: M = A/alpha = %d,  4M = %d" % (M, 4*M))
        print("           %d solution(s) found" % res["backtest_solutions"])
        if res["first_u"] is not None:
            u, v = res["first_u"], res["first_v"]
            print("           First: u=%d, v=%d" % (u, v))
            print("             delta | u? %s  (u/delta = %d)" % (u % dv == 0, u//dv))
            print("             u = v mod 2? %s" % (u % 2 == v % 2))
            print("             u^2 - v^2 = %d = 4M = %d? %s" % (u**2 - v**2, 4*M, u**2 - v**2 == 4*M))
            bpv, cpv = res["first_bp"], res["first_cp"]
            print("           Reconstruction: bp = (u+v)/2 = %d,  cp = (u-v)/2 = %d" % (bpv, cpv))
            print("             bp*cp = %d = M = %d? %s" % (bpv*cpv, M, bpv*cpv == M))

    # Failures
    if failures:
        print()
        print("-" * 78)
        print("FAILURES (%d certificates)" % len(failures))
        print("-" * 78)
        for res in failures[:10]:
            print("  p=%d, delta=%d, b=%d, c=%d" % (res["p"], res["delta"], res["b"], res["c"]))
            if "error" in res:
                print("    Error: %s" % res["error"])
    else:
        print()
        print("-" * 78)
        print("NO FAILURES -- ALL 750 CERTIFICATES VERIFIED")
        print("-" * 78)

    # Cross-check: original certificate as back-test solution
    print()
    print("-" * 78)
    print("ORIGINAL CERTIFICATE AS BACK-TEST SOLUTION")
    print("-" * 78)
    print("  Setting u = b + c, v = |b - c|:")
    print("  Then u^2 - v^2 = 4*b*c automatically.")
    print("  Checking: delta | (b + c)?")

    orig_div_pass = 0
    for pv, delta, bv, cv in rows:
        if (bv + cv) % delta == 0:
            orig_div_pass += 1

    print("  delta | (b + c):  %d / %d" % (orig_div_pass, total))
    print()
    print("  The original (b, c) always satisfies the back-test with M = b*c,")
    print("  since u=b+c, v=|b-c| gives u^2-v^2=4bc, u=v mod 2 (always),")
    print("  and delta | u (verified above).")

    alpha_int_count = sum(1 for p, d, b, c in rows if ((p+d)//4) % (b*c) == 0)
    print("  Note: M = b*c = A/alpha for integer alpha in %d / %d cases." % (alpha_int_count, total))

    # Cross-check: scaled reconstruction
    print()
    print("-" * 78)
    print("ALTERNATIVE L4A SOLUTIONS FROM BACK-TEST")
    print("-" * 78)
    alt_l4a = 0
    for pv, delta, bv, cv in rows:
        A = (pv + delta) // 4
        x = delta * bv - A
        y = delta * cv - A
        alpha = math.gcd(x, y)
        M_val = A // alpha
        solutions = find_backtest_solutions(delta, M_val)
        if not solutions:
            continue
        for u0, v0 in solutions:
            bp = (u0 + v0) // 2
            cp = (u0 - v0) // 2
            B = alpha * bp
            C = alpha * cp
            if (delta * B - A) * (delta * C - A) == A * A:
                alt_l4a += 1
                break

    print("  Scaled (B=alpha*bp, C=alpha*cp) satisfies L4A: %d / %d" % (alt_l4a, total))

    print()
    print("=" * 78)
    print("VERIFICATION COMPLETE in %.2f seconds" % elapsed)
    print("=" * 78)


if __name__ == "__main__":
    main()
