#!/usr/bin/env python3
"""
Generate D.6 helper lemmas in the 'rcases' style for Existence.lean.

Each M value gets one helper lemma with flat case-split using rcases,
avoiding deep nesting. The main proof calls these helpers.
"""

import math


def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def crt_solve(r1, m1, r2, m2):
    g, p, q = extended_gcd(m1, m2)
    if (r2 - r1) % g != 0:
        return None, None
    lcm_val = m1 * m2 // g
    sol = (r1 + m1 * ((r2 - r1) // g) * p) % lcm_val
    return sol, lcm_val


def ordered_factorizations_3(n):
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


def compute_cases_for_M(M):
    """Compute all valid D.6 subcases for a given M."""
    b_param = (M + 1) // 4
    facts = ordered_factorizations_3(b_param)

    res_to_case = {}
    for alpha, r, s in facts:
        res = (-4 * alpha * s * s) % M
        num_a = 4 * alpha * s * s

        # CRT compatibility check
        crt_val, crt_mod = crt_solve(1, 24, res, M)
        if crt_val is None:
            continue

        # Pick smallest num_a for each residue
        if res not in res_to_case or num_a < res_to_case[res]["num_a"]:
            c_coeff = alpha * r
            if r == 1:
                c_num_expr = f"p + {s}"
                c_num_cast = f"\u2191p + {s}"
            else:
                c_num_expr = f"{r} * p + {s}"
                c_num_cast = f"{r} * \u2191p + {s}"

            res_to_case[res] = {
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

    return res_to_case


def gen_helper_lemma(M, cases, heartbeats=400000):
    """Generate a complete helper lemma for one M value."""
    residues = sorted(cases.keys())
    n = len(residues)

    lines = []

    # Disjunction type
    disj = " \u2228 ".join(f"p % {M} = {r}" for r in residues)

    lines.append(f"set_option maxHeartbeats {heartbeats} in")
    lines.append(f"private theorem ed2_via_m{M} (p : \u2115) (hp24 : p % 24 = 1)")
    lines.append(f"    (h : {disj}) :")
    lines.append(f"    \u2203 offset b c : \u2115, offset % 4 = 3 \u2227 b > 0 \u2227 c > 0 \u2227")
    lines.append(f"      (\u2191p + \u2191offset : \u2124) * (\u2191b + \u2191c) = "
                 f"4 * \u2191offset * \u2191b * \u2191c := by")
    lines.append(f"  rcases h with " + " | ".join(["h"] * n))

    for i, res in enumerate(residues):
        c = cases[res]
        alpha = c["alpha"]
        r = c["r"]
        s = c["s"]
        num_a = c["num_a"]
        b = c["b"]
        c_coeff = c["c_coeff"]
        c_num_expr = c["c_num_expr"]
        c_num_cast = c["c_num_cast"]
        crt_mod = c["crt_mod"]
        crt_val = c["crt_val"]

        prefix = "  \u00b7 " if i == 0 else "  \u00b7 "

        lines.append(f"  \u00b7 -- p \u2261 {res} (mod {M}): "
                     f"(\u03b1={alpha}, r={r}, s={s})")
        lines.append(f"    have hdiv{M}a : {M} \u2223 (p + {num_a}) := by omega")
        lines.append(f"    have hdiv{M}b : {M} \u2223 ({c_num_expr}) := by omega")

        if c_coeff > 1:
            lines.append(f"    refine \u27e8(p + {num_a}) / {M}, {b}, "
                         f"{c_coeff} * (({c_num_expr}) / {M}), ?_, by norm_num, ?_, ?_\u27e9")
        else:
            lines.append(f"    refine \u27e8(p + {num_a}) / {M}, {b}, "
                         f"({c_num_expr}) / {M}, ?_, by norm_num, ?_, ?_\u27e9")

        # Goal 1: offset % 4 = 3
        lines.append(f"    \u00b7 have : p % {crt_mod} = {crt_val} := by omega")
        lines.append(f"      have : (p + {num_a}) / {M} * {M} = "
                     f"p + {num_a} := Nat.div_mul_cancel hdiv{M}a")
        lines.append(f"      omega")

        # Goal 2: c > 0
        if c_coeff > 1:
            lines.append(f"    \u00b7 exact Nat.mul_pos (by norm_num) "
                         f"(Nat.div_pos (by omega) (by norm_num))")
        else:
            lines.append(f"    \u00b7 exact Nat.div_pos (by omega) (by norm_num)")

        # Goal 3: identity
        lines.append(f"    \u00b7 set \u03b4 := (p + {num_a}) / {M}")
        lines.append(f"      set c\u2080 := ({c_num_expr}) / {M}")
        lines.append(f"      have h\u03b4_mul : \u03b4 * {M} = p + {num_a} := "
                     f"Nat.div_mul_cancel hdiv{M}a")
        lines.append(f"      have hc\u2080_mul : c\u2080 * {M} = {c_num_expr} := "
                     f"Nat.div_mul_cancel hdiv{M}b")
        lines.append(f"      have h\u03b4_int : (\u2191\u03b4 : \u2124) * {M} = "
                     f"\u2191p + {num_a} := by exact_mod_cast h\u03b4_mul")
        lines.append(f"      have hc\u2080_int : (\u2191c\u2080 : \u2124) * {M} = "
                     f"{c_num_cast} := by exact_mod_cast hc\u2080_mul")
        lines.append(f"      push_cast")
        lines.append(f"      nlinarith [h\u03b4_int, hc\u2080_int]")

    return "\n".join(lines)


def gen_dispatch_code(selected_Ms, indent=32):
    """Generate the dispatch code for the sorry location."""
    I = " " * indent
    lines = []

    for i, M in enumerate(selected_Ms):
        cases = compute_cases_for_M(M)
        residues = sorted(cases.keys())
        disj = " \u2228 ".join(f"p % {M} = {r}" for r in residues)

        if i == 0:
            lines.append(f"{I}by_cases h{M} : {disj}")
        # else: already emitted by previous negative branch

        lines.append(f"{I}\u00b7 exact ed2_via_m{M} p (by omega) h{M}")

        if i < len(selected_Ms) - 1:
            next_M = selected_Ms[i + 1]
            next_cases = compute_cases_for_M(next_M)
            next_residues = sorted(next_cases.keys())
            next_disj = " \u2228 ".join(f"p % {next_M} = {r}" for r in next_residues)
            lines.append(f"{I}\u00b7 by_cases h{next_M} : {next_disj}")
        else:
            lines.append(f"{I}\u00b7 /- Remaining sorry-region primes not covered by D.6 subcases.")
            lines.append(f"{I}     These require the certificate bridge (Phase 2) or the full")
            lines.append(f"{I}     Dyachenko lattice density argument (Phase 3). -/")
            lines.append(f"{I}  sorry")

    return "\n".join(lines)


def main():
    # Selected M values from greedy analysis (top coverage)
    # Start with just M=39 for testing
    test_Ms = [39]

    # Full set from coverage analysis
    all_Ms = [39, 47, 119, 159, 71, 95, 111, 143, 79, 87, 151, 59,
              191, 155, 199, 83, 127, 43, 99, 107, 131, 167]

    print("=" * 70)
    print("GENERATING HELPER LEMMAS")
    print("=" * 70)

    # Generate M=39 test helper
    cases_39 = compute_cases_for_M(39)
    helper_39 = gen_helper_lemma(39, cases_39)
    print("\n--- M=39 Helper Lemma ---")
    print(helper_39)

    # Save M=39 helper
    with open("/Users/kvallie2/Desktop/esc_stage8/lean_helper_m39.txt", "w") as f:
        f.write(helper_39)

    # Generate dispatch code for M=39 only
    dispatch_39 = gen_dispatch_code([39])
    print("\n--- M=39 Dispatch Code (replaces sorry) ---")
    print(dispatch_39)

    with open("/Users/kvallie2/Desktop/esc_stage8/lean_dispatch_m39.txt", "w") as f:
        f.write(dispatch_39)

    # Generate ALL helper lemmas
    print("\n\n" + "=" * 70)
    print("GENERATING ALL HELPER LEMMAS")
    print("=" * 70)

    all_helpers = []
    for M in all_Ms:
        cases = compute_cases_for_M(M)
        n_cases = len(cases)
        # Scale heartbeats with number of cases
        hb = max(400000, n_cases * 100000)
        helper = gen_helper_lemma(M, cases, heartbeats=hb)
        all_helpers.append(helper)
        print(f"  M={M}: {n_cases} cases, {hb} heartbeats")

    all_helpers_text = "\n\n".join(all_helpers)
    with open("/Users/kvallie2/Desktop/esc_stage8/lean_all_helpers.txt", "w") as f:
        f.write(all_helpers_text)
    print(f"\n  All helpers written to lean_all_helpers.txt")
    print(f"  Total lines: {all_helpers_text.count(chr(10)) + 1}")

    # Generate full dispatch
    dispatch_all = gen_dispatch_code(all_Ms)
    with open("/Users/kvallie2/Desktop/esc_stage8/lean_dispatch_all.txt", "w") as f:
        f.write(dispatch_all)
    print(f"  Full dispatch written to lean_dispatch_all.txt")
    print(f"  Dispatch lines: {dispatch_all.count(chr(10)) + 1}")
    print(f"  Dispatch nesting depth: {len(all_Ms)} levels")


if __name__ == "__main__":
    main()
