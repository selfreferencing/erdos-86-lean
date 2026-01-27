#!/usr/bin/env python3
"""
Comprehensive D.6 subcase generator for eliminating the sorry in Existence.lean:415.

For each M ≡ 3 mod 4, M = 4*b_param - 1:
  - Enumerate factorizations b_param = alpha * r * s
  - Compute covered residue class: p ≡ -4*alpha*s^2 mod M
  - Check CRT compatibility with p ≡ 1 mod 24
  - Generate Lean code for each subcase

The sorry region requires:
  - p ≡ 1 mod 24
  - p % 7 in {1, 2, 4}
  - p % 5 in {1, 4}
  - p % 11 not in {7, 8, 10}
  - p % 19 not in {14, 15, 18}
  - p % 23 not in {7, 10, 11, 15, 17, 19, 20, 21, 22}
"""

import csv
import math
from collections import defaultdict


def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def sorry_region(p):
    """Check if prime p is in the sorry region (all conditions)."""
    if p % 24 != 1:
        return False
    if p % 7 not in (1, 2, 4):
        return False
    if p % 5 not in (1, 4):
        return False
    if p % 11 in (7, 8, 10):
        return False
    if p % 19 in (14, 15, 18):
        return False
    if p % 23 in (7, 10, 11, 15, 17, 19, 20, 21, 22):
        return False
    return True


def ordered_factorizations_3(n):
    """Return all ordered triples (a, r, s) with a*r*s = n, a,r,s >= 1."""
    result = []
    for a in range(1, n + 1):
        if n % a != 0:
            continue
        rem = n // a
        for r in range(1, rem + 1):
            if rem % r != 0:
                continue
            s = rem // r
            result.append((a, r, s))
    return result


def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def crt_solve(r1, m1, r2, m2):
    """CRT: find x with x ≡ r1 mod m1, x ≡ r2 mod m2. Returns (x, lcm) or (None, None)."""
    g, p, q = extended_gcd(m1, m2)
    if (r2 - r1) % g != 0:
        return None, None
    lcm_val = m1 * m2 // g
    sol = (r1 + m1 * ((r2 - r1) // g) * p) % lcm_val
    return sol, lcm_val


def compute_case_data(M, alpha, r, s):
    """
    Compute all tuple parameters for a D.6 subcase.

    Returns dict with all parameters, or None if CRT incompatible.
    """
    b_param = (M + 1) // 4
    assert alpha * r * s == b_param

    res = (-4 * alpha * s * s) % M
    num_a = 4 * alpha * s * s

    # CRT: p ≡ 1 mod 24, p ≡ res mod M
    crt_val, crt_mod = crt_solve(1, 24, res, M)
    if crt_val is None:
        return None

    # c formula: c = alpha*r * (r*p + s) / M
    c_coeff = alpha * r
    if r == 1:
        c_num_expr = f"p + {s}"
        c_num_cast = f"\u2191p + {s}"
    else:
        c_num_expr = f"{r} * p + {s}"
        c_num_cast = f"{r} * \u2191p + {s}"

    if c_coeff == 1:
        c_coeff = 1  # no change needed

    return {
        "M": M,
        "res": res,
        "alpha": alpha,
        "r": r,
        "s": s,
        "num_a": num_a,
        "b": b_param,
        "c_coeff": c_coeff,
        "c_num_expr": c_num_expr,
        "c_num_cast": c_num_cast,
        "crt_mod": crt_mod,
        "crt_val": crt_val,
    }


def verify_case(case_data, p):
    """Verify the D.6 formula gives a valid solution for prime p."""
    M = case_data["M"]
    alpha = case_data["alpha"]
    r = case_data["r"]
    s = case_data["s"]
    b = case_data["b"]

    assert p % M == case_data["res"], f"p={p} not in residue class {case_data['res']} mod {M}"

    num_a = case_data["num_a"]
    assert (p + num_a) % M == 0, f"M does not divide p + num_a for p={p}"

    offset = (p + num_a) // M
    c_num = r * p + s
    assert c_num % M == 0, f"M does not divide rp+s for p={p}"
    c = alpha * r * c_num // M

    # Verify conditions
    assert offset % 4 == 3, f"offset % 4 != 3 for p={p}: offset={offset}"
    assert b > 0
    assert c > 0, f"c = 0 for p={p}"

    # Verify identity: (p + offset)(b + c) = 4 * offset * b * c
    lhs = (p + offset) * (b + c)
    rhs = 4 * offset * b * c
    assert lhs == rhs, f"Identity fails for p={p}: {lhs} != {rhs}"

    return offset, b, c


def main():
    # ============================================================
    # Step 1: Find sorry-region primes
    # ============================================================
    print("=" * 70)
    print("STEP 1: IDENTIFYING SORRY-REGION PRIMES")
    print("=" * 70)

    sorry_primes = []
    for p in range(5, 1_000_001):
        if is_prime(p) and sorry_region(p):
            sorry_primes.append(p)

    print(f"  Sorry-region primes up to 10^6: {len(sorry_primes)}")
    print(f"  First 10: {sorry_primes[:10]}")
    print(f"  Last 10: {sorry_primes[-10:]}")

    # Cross-reference with CSV
    csv_path = "/Users/kvallie2/Desktop/esc_stage8/witnesses_1000000.csv"
    try:
        csv_primes = set()
        with open(csv_path) as f:
            reader = csv.DictReader(f)
            for row in reader:
                csv_primes.add(int(row["p"]))
        sorry_set = set(sorry_primes)
        in_csv_not_sorry = csv_primes - sorry_set
        in_sorry_not_csv = sorry_set - csv_primes
        print(f"\n  CSV primes: {len(csv_primes)}")
        print(f"  In CSV but not sorry-region: {len(in_csv_not_sorry)}")
        if in_csv_not_sorry:
            examples = sorted(in_csv_not_sorry)[:5]
            for p in examples:
                print(f"    p={p}: mod24={p%24}, mod7={p%7}, mod5={p%5}, "
                      f"mod11={p%11}, mod19={p%19}, mod23={p%23}")
        print(f"  In sorry-region but not CSV: {len(in_sorry_not_csv)}")
        if in_sorry_not_csv:
            for p in sorted(in_sorry_not_csv)[:5]:
                print(f"    p={p}")
    except FileNotFoundError:
        print("  (CSV file not found, skipping cross-reference)")

    # ============================================================
    # Step 2: Compute coverage for each candidate M
    # ============================================================
    print()
    print("=" * 70)
    print("STEP 2: COVERAGE ANALYSIS FOR CANDIDATE M VALUES")
    print("=" * 70)

    # Candidate M values: M ≡ 3 mod 4, M > 23
    candidate_Ms = [M for M in range(27, 200) if M % 4 == 3]

    coverage_data = {}  # M -> {res -> case_data}
    coverage_primes = {}  # M -> set of covered sorry-region primes

    for M in candidate_Ms:
        b_param = (M + 1) // 4
        facts = ordered_factorizations_3(b_param)

        # For each factorization, compute the covered class
        res_to_case = {}
        for alpha, r, s in facts:
            case = compute_case_data(M, alpha, r, s)
            if case is None:
                continue
            res = case["res"]
            # Pick the factorization with smallest num_a (simplest Lean code)
            if res not in res_to_case or case["num_a"] < res_to_case[res]["num_a"]:
                res_to_case[res] = case

        # Count covered sorry-region primes
        covered = set()
        for p in sorry_primes:
            if p % M in res_to_case:
                covered.add(p)

        coverage_data[M] = res_to_case
        coverage_primes[M] = covered

    # Print per-M coverage
    print(f"\n  {'M':>4s}  {'b_param':>7s}  {'#facts':>6s}  {'#classes':>8s}  {'#covered':>8s}  {'%covered':>8s}")
    print(f"  {'-'*4}  {'-'*7}  {'-'*6}  {'-'*8}  {'-'*8}  {'-'*8}")
    for M in candidate_Ms:
        b_param = (M + 1) // 4
        n_facts = len(ordered_factorizations_3(b_param))
        n_classes = len(coverage_data[M])
        n_covered = len(coverage_primes[M])
        pct = n_covered / len(sorry_primes) * 100 if sorry_primes else 0
        if n_covered > 0:
            print(f"  {M:>4d}  {b_param:>7d}  {n_facts:>6d}  {n_classes:>8d}  {n_covered:>8d}  {pct:>7.1f}%")

    # ============================================================
    # Step 3: Greedy M selection
    # ============================================================
    print()
    print("=" * 70)
    print("STEP 3: GREEDY M SELECTION FOR MAXIMUM COVERAGE")
    print("=" * 70)

    uncovered = set(sorry_primes)
    selected_Ms = []
    cumulative = []

    while uncovered:
        best_M = None
        best_count = 0
        for M in candidate_Ms:
            if M in [m for m, _, _ in selected_Ms]:
                continue
            new_cov = len(coverage_primes[M] & uncovered)
            if new_cov > best_count:
                best_count = new_cov
                best_M = M
        if best_count == 0:
            break

        _, covered = coverage_data[best_M], coverage_primes[best_M]
        newly_covered = covered & uncovered
        uncovered -= newly_covered
        total_covered = len(sorry_primes) - len(uncovered)
        pct = total_covered / len(sorry_primes) * 100
        selected_Ms.append((best_M, best_count, total_covered))
        print(f"  M={best_M:>3d}: covers {best_count:>4d} new primes, "
              f"cumulative {total_covered}/{len(sorry_primes)} ({pct:.1f}%)")

    if uncovered:
        print(f"\n  WARNING: {len(uncovered)} primes still uncovered!")
        for p in sorted(uncovered)[:20]:
            print(f"    p={p}: mod7={p%7}, mod5={p%5}, mod11={p%11}")
    else:
        print(f"\n  ALL {len(sorry_primes)} primes covered!")
        print(f"  Selected M values: {[m for m, _, _ in selected_Ms]}")

    # ============================================================
    # Step 4: Verify all cases on sorry-region primes
    # ============================================================
    print()
    print("=" * 70)
    print("STEP 4: VERIFICATION OF D.6 FORMULAS")
    print("=" * 70)

    verify_errors = 0
    for M, _, _ in selected_Ms:
        res_to_case = coverage_data[M]
        covered = coverage_primes[M]
        verified = 0
        for p in covered:
            res = p % M
            case = res_to_case[res]
            try:
                verify_case(case, p)
                verified += 1
            except AssertionError as e:
                print(f"  VERIFY FAIL: {e}")
                verify_errors += 1
                if verify_errors > 10:
                    print("  (stopping after 10 errors)")
                    break
        print(f"  M={M}: verified {verified}/{len(covered)} primes")

    if verify_errors == 0:
        print("\n  ALL formulas verified correct!")

    # ============================================================
    # Step 5: Generate case tuples for gen_lean_cases.py
    # ============================================================
    print()
    print("=" * 70)
    print("STEP 5: GENERATED CASE TUPLES")
    print("=" * 70)

    for M, _, _ in selected_Ms:
        res_to_case = coverage_data[M]
        b_param = (M + 1) // 4
        print(f"\ncases_m{M} = [")
        for res in sorted(res_to_case.keys()):
            c = res_to_case[res]
            print(f"    ({c['res']}, {c['alpha']}, {c['r']}, {c['s']}, "
                  f"{c['num_a']}, {c['b']}, {c['c_coeff']}, "
                  f'"{c["c_num_expr"]}", "{c["c_num_cast"]}", '
                  f"{c['crt_mod']}, {c['crt_val']}),")
        print("]")

    # ============================================================
    # Step 6: Generate complete Lean code
    # ============================================================
    print()
    print("=" * 70)
    print("STEP 6: LEAN CODE GENERATION")
    print("=" * 70)

    all_cases = []
    for M, _, _ in selected_Ms:
        res_to_case = coverage_data[M]
        # Sort by residue for deterministic output
        for res in sorted(res_to_case.keys()):
            all_cases.append((M, res_to_case[res]))

    print(f"\n  Total cases to generate: {len(all_cases)}")
    print(f"  Estimated Lean lines: ~{len(all_cases) * 15}")

    # Generate the Lean code
    lean_lines = gen_lean_chain(all_cases, bullet_indent=8)
    lean_code = "\n".join(lean_lines)

    output_path = "/Users/kvallie2/Desktop/esc_stage8/lean_new_cases_code.txt"
    with open(output_path, "w") as f:
        f.write(lean_code)
    print(f"  Lean code written to: {output_path}")
    print(f"  Total lines: {len(lean_lines)}")

    # Also generate per-M helper lemma versions
    for M, _, _ in selected_Ms:
        res_to_case = coverage_data[M]
        m_cases = [(M, res_to_case[res]) for res in sorted(res_to_case.keys())]
        m_lines = gen_lean_chain(m_cases, bullet_indent=8, final_sorry=True)
        m_output = f"/Users/kvallie2/Desktop/esc_stage8/lean_m{M}_code.txt"
        with open(m_output, "w") as f:
            f.write("\n".join(m_lines))
        print(f"  M={M} code ({len(m_lines)} lines) written to: lean_m{M}_code.txt")


def sp(n):
    return " " * n


def gen_positive_case(case_data, indent):
    """Generate Lean proof lines for a positive D.6 case."""
    M = case_data["M"]
    res = case_data["res"]
    alpha = case_data["alpha"]
    r = case_data["r"]
    s = case_data["s"]
    num_a = case_data["num_a"]
    b = case_data["b"]
    c_coeff = case_data["c_coeff"]
    c_num_expr = case_data["c_num_expr"]
    c_num_cast = case_data["c_num_cast"]
    crt_mod = case_data["crt_mod"]
    crt_val = case_data["crt_val"]

    lines = []
    I = sp(indent)

    # Comment
    lines.append(f"{I}-- p \u2261 {res} (mod {M}): (\u03b1={alpha}, r={r}, s={s}), "
                 f"M = 4\u00b7{alpha}\u00b7{s}\u00b7{r} - 1 = {M}")
    if c_coeff > 1:
        lines.append(f"{I}-- offset = (p+{num_a})/{M}, b = {b}, "
                     f"c = {c_coeff}\u00b7({c_num_expr})/{M}")
    else:
        lines.append(f"{I}-- offset = (p+{num_a})/{M}, b = {b}, "
                     f"c = ({c_num_expr})/{M}")

    # Divisibility hypotheses
    lines.append(f"{I}have hdiv{M}a : {M} \u2223 (p + {num_a}) := by omega")
    lines.append(f"{I}have hdiv{M}b : {M} \u2223 ({c_num_expr}) := by omega")

    # Refine
    if c_coeff > 1:
        lines.append(f"{I}refine \u27e8(p + {num_a}) / {M}, {b}, "
                     f"{c_coeff} * (({c_num_expr}) / {M}), ?_, by norm_num, ?_, ?_\u27e9")
    else:
        lines.append(f"{I}refine \u27e8(p + {num_a}) / {M}, {b}, "
                     f"({c_num_expr}) / {M}, ?_, by norm_num, ?_, ?_\u27e9")

    # Goal 1: offset % 4 = 3
    lines.append(f"{I}\u00b7 have : p % {crt_mod} = {crt_val} := by omega")
    lines.append(f"{I}  have h{M}div : (p + {num_a}) / {M} * {M} = "
                 f"p + {num_a} := Nat.div_mul_cancel hdiv{M}a")
    lines.append(f"{I}  omega")

    # Goal 2: c > 0
    if c_coeff > 1:
        lines.append(f"{I}\u00b7 exact Nat.mul_pos (by norm_num) "
                     f"(Nat.div_pos (by omega) (by norm_num))")
    else:
        lines.append(f"{I}\u00b7 exact Nat.div_pos (by omega) (by norm_num)")

    # Goal 3: identity
    lines.append(f"{I}\u00b7 set \u03b4 := (p + {num_a}) / {M} with h\u03b4_def")
    lines.append(f"{I}  set c\u2080 := ({c_num_expr}) / {M} with hc\u2080_def")
    lines.append(f"{I}  have h\u03b4_mul : \u03b4 * {M} = p + {num_a} := "
                 f"Nat.div_mul_cancel hdiv{M}a")
    lines.append(f"{I}  have hc\u2080_mul : c\u2080 * {M} = {c_num_expr} := "
                 f"Nat.div_mul_cancel hdiv{M}b")
    lines.append(f"{I}  have h\u03b4_int : (\u2191\u03b4 : \u2124) * {M} = "
                 f"\u2191p + {num_a} := by exact_mod_cast h\u03b4_mul")
    lines.append(f"{I}  have hc\u2080_int : (\u2191c\u2080 : \u2124) * {M} = "
                 f"{c_num_cast} := by exact_mod_cast hc\u2080_mul")
    lines.append(f"{I}  push_cast")
    lines.append(f"{I}  nlinarith [h\u03b4_int, hc\u2080_int]")

    return lines


def gen_lean_chain(all_cases, bullet_indent, final_sorry=True):
    """Generate a chain of by_cases for all cases."""
    lines = []
    n = len(all_cases)

    for i, (M, case_data) in enumerate(all_cases):
        res = case_data["res"]
        ci = bullet_indent + 2 * i

        if i == 0:
            lines.append(f"{sp(ci)}-- M = {M} subcases via Lemma D.6")
            lines.append(f"{sp(ci)}by_cases hp{M}_{res} : p % {M} = {res}")
        # else: the by_cases was emitted by the previous negative branch

        # Positive case
        pos_lines = gen_positive_case(case_data, ci + 2)
        lines.append(f"{sp(ci)}\u00b7 {pos_lines[0].lstrip()}")
        lines.extend(pos_lines[1:])

        # Negative branch
        if i < n - 1:
            next_M, next_case = all_cases[i + 1]
            next_res = next_case["res"]
            if next_M != M:
                lines.append(f"{sp(ci)}\u00b7 -- M = {next_M} subcases via Lemma D.6")
                lines.append(f"{sp(ci + 2)}by_cases hp{next_M}_{next_res} : "
                             f"p % {next_M} = {next_res}")
            else:
                lines.append(f"{sp(ci)}\u00b7 by_cases hp{M}_{next_res} : "
                             f"p % {M} = {next_res}")
        else:
            if final_sorry:
                lines.append(f"{sp(ci)}\u00b7 sorry")
            else:
                lines.append(f"{sp(ci)}\u00b7 -- All sorry-region primes covered "
                             f"by M values above")
                lines.append(f"{sp(ci + 2)}sorry")

    return lines


if __name__ == "__main__":
    main()
