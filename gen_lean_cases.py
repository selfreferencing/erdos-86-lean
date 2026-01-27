#!/usr/bin/env python3
"""Generate Lean 4 code for M=19 and M=23 D6 subcases.
Uses the pattern: · by_cases on same line for negative branches."""

# Each case: (res, alpha, r, s, num_a, b, c_coeff, c_num_expr, c_num_cast, crt_mod, crt_val)
# c = c_coeff * (c_num_expr / M)  when c_coeff > 1
# c = (c_num_expr / M)            when c_coeff == 1

cases_m19 = [
    (14, 1, 1, 5, 100, 5, 1, "p + 5", "↑p + 5", 456, 337),
    (15, 1, 5, 1, 4, 5, 5, "5 * p + 1", "5 * ↑p + 1", 456, 433),
    (18, 5, 1, 1, 20, 5, 5, "p + 1", "↑p + 1", 456, 265),
]

cases_m23 = [
    (19, 1, 6, 1, 4, 6, 6, "6 * p + 1", "6 * ↑p + 1", 552, 433),
    (7, 1, 3, 2, 16, 6, 3, "3 * p + 2", "3 * ↑p + 2", 552, 145),
    (10, 1, 2, 3, 36, 6, 2, "2 * p + 3", "2 * ↑p + 3", 552, 217),
    (17, 1, 1, 6, 144, 6, 1, "p + 6", "↑p + 6", 552, 385),
    (15, 2, 3, 1, 8, 6, 6, "3 * p + 1", "3 * ↑p + 1", 552, 337),
    (20, 2, 1, 3, 72, 6, 2, "p + 3", "↑p + 3", 552, 457),
    (11, 3, 2, 1, 12, 6, 6, "2 * p + 1", "2 * ↑p + 1", 552, 241),
    (21, 3, 1, 2, 48, 6, 3, "p + 2", "↑p + 2", 552, 481),
    (22, 6, 1, 1, 24, 6, 6, "p + 1", "↑p + 1", 552, 505),
]


def sp(n):
    return " " * n


def gen_positive_case(M, res, alpha, r, s, num_a, b, c_coeff,
                      c_num_expr, c_num_cast, crt_mod, crt_val, indent):
    """Generate lines for a positive case block (content after ·)."""
    lines = []
    I = sp(indent)

    # Comment
    lines.append(f"{I}-- p ≡ {res} (mod {M}): (α={alpha}, r={r}, s={s}), M = 4·{alpha}·{s}·{r} - 1 = {M}")
    if c_coeff > 1:
        lines.append(f"{I}-- offset = (p+{num_a})/{M}, b = {b}, c = {c_coeff}·({c_num_expr})/{M}")
    else:
        lines.append(f"{I}-- offset = (p+{num_a})/{M}, b = {b}, c = ({c_num_expr})/{M}")

    # Divisibility hypotheses
    lines.append(f"{I}have hdiv{M}a : {M} ∣ (p + {num_a}) := by omega")
    lines.append(f"{I}have hdiv{M}b : {M} ∣ ({c_num_expr}) := by omega")

    # Refine
    if c_coeff > 1:
        lines.append(f"{I}refine ⟨(p + {num_a}) / {M}, {b}, {c_coeff} * (({c_num_expr}) / {M}), ?_, by norm_num, ?_, ?_⟩")
    else:
        lines.append(f"{I}refine ⟨(p + {num_a}) / {M}, {b}, ({c_num_expr}) / {M}, ?_, by norm_num, ?_, ?_⟩")

    # Goal 1: offset % 4 = 3
    lines.append(f"{I}· have : p % {crt_mod} = {crt_val} := by omega")
    lines.append(f"{I}  have h{M}div : (p + {num_a}) / {M} * {M} = p + {num_a} := Nat.div_mul_cancel hdiv{M}a")
    lines.append(f"{I}  omega")

    # Goal 2: c > 0
    if c_coeff > 1:
        lines.append(f"{I}· exact Nat.mul_pos (by norm_num) (Nat.div_pos (by omega) (by norm_num))")
    else:
        lines.append(f"{I}· exact Nat.div_pos (by omega) (by norm_num)")

    # Goal 3: identity
    lines.append(f"{I}· set δ := (p + {num_a}) / {M} with hδ_def")
    lines.append(f"{I}  set c₀ := ({c_num_expr}) / {M} with hc₀_def")
    lines.append(f"{I}  have hδ_mul : δ * {M} = p + {num_a} := Nat.div_mul_cancel hdiv{M}a")
    lines.append(f"{I}  have hc₀_mul : c₀ * {M} = {c_num_expr} := Nat.div_mul_cancel hdiv{M}b")
    lines.append(f"{I}  have hδ_int : (↑δ : ℤ) * {M} = ↑p + {num_a} := by exact_mod_cast hδ_mul")
    lines.append(f"{I}  have hc₀_int : (↑c₀ : ℤ) * {M} = {c_num_cast} := by exact_mod_cast hc₀_mul")
    lines.append(f"{I}  push_cast")
    lines.append(f"{I}  nlinarith [hδ_int, hc₀_int]")

    return lines


def gen_chain(all_cases, bullet_indent):
    """Generate a chain of by_cases with properly nested negative branches.

    bullet_indent: indent of the first by_cases statement
    """
    lines = []
    n = len(all_cases)

    for i, (M, case) in enumerate(all_cases):
        res, alpha, r, s, num_a, b, c_coeff, c_num_expr, c_num_cast, crt_mod, crt_val = case
        # The by_cases and · bullets are at `ci` indent
        ci = bullet_indent + 2 * i

        if i == 0:
            # First by_cases is a standalone tactic
            lines.append(f"{sp(ci)}by_cases hp{M}_{res} : p % {M} = {res}")
        # else: handled by the negative branch of previous case

        # Positive case: · at ci, content at ci+2
        pos_lines = gen_positive_case(M, res, alpha, r, s, num_a, b,
                                      c_coeff, c_num_expr, c_num_cast,
                                      crt_mod, crt_val, ci + 2)
        lines.append(f"{sp(ci)}· {pos_lines[0].lstrip()}")
        lines.extend(pos_lines[1:])

        # Negative branch
        if i < n - 1:
            next_M, next_case = all_cases[i + 1]
            next_res = next_case[0]
            # If switching M values, add a comment
            if next_M != M:
                lines.append(f"{sp(ci)}· -- M = {next_M} subcases via Lemma D.6")
                lines.append(f"{sp(ci + 2)}by_cases hp{next_M}_{next_res} : p % {next_M} = {next_res}")
            else:
                lines.append(f"{sp(ci)}· by_cases hp{M}_{next_res} : p % {M} = {next_res}")
        else:
            # Final negative branch: sorry
            lines.append(f"{sp(ci)}· /- Remaining: p % 7 ∈ {{1, 2, 4}}, p % 5 ∈ {{1, 4}},")
            lines.append(f"{sp(ci + 5)}p % 11 ∉ {{7, 8, 10}}, p % 19 ∉ {{14, 15, 18}},")
            lines.append(f"{sp(ci + 5)}p % 23 ∉ {{7, 10, 11, 15, 17, 19, 20, 21, 22}}.")
            lines.append(f"{sp(ci + 5)}Requires the full Dyachenko lattice density argument")
            lines.append(f"{sp(ci + 5)}(arXiv:2511.07465) or additional M values.")
            lines.append(f"{sp(ci + 5)}Computationally verified for all such primes up to 10^7. -/")
            lines.append(f"{sp(ci + 2)}sorry")

    return lines


def main():
    # Build combined case list: [(M, case_tuple), ...]
    all_cases = [(19, c) for c in cases_m19] + [(23, c) for c in cases_m23]

    # The outer · at line 184 is at indent 6, so its content is at indent 8.
    # The first by_cases starts at indent 8.
    bullet_indent = 8

    # Generate header comment + chain
    lines = []
    lines.append(f"{sp(bullet_indent)}-- M = 19 subcases: cover p % 19 ∈ {{14, 15, 18}} via Lemma D.6")
    lines.extend(gen_chain(all_cases, bullet_indent))

    result = "\n".join(lines)
    print(result)

    with open("/Users/kvallie2/Desktop/esc_stage8/lean_m19_m23_code.txt", "w") as f:
        f.write(result)
    print(f"\n\n--- Saved {len(lines)} lines to lean_m19_m23_code.txt ---")


if __name__ == "__main__":
    main()
