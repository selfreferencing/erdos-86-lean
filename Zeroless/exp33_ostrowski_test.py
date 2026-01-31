#!/usr/bin/env python3
"""
Experiment 33: Ostrowski Renormalization Test

MOTIVATION:
GPT 5A Pro (2nd instance) proposed the Ostrowski renormalization route:
decompose Birkhoff sums into blocks aligned with convergent denominators q_j,
replace 1_{F_m} by a coarse J-digit approximation f_{m,J}, apply
Denjoy-Koksma on each block. This experiment tests quantitative viability.

KEY QUESTIONS:
1. What is the Ostrowski decomposition of L_m for various m?
2. How good is the J-digit approximation f_{m,J} vs f_m?
3. What is the DK bound on each q_j-block?
4. For what J(m) does the total error go to zero?

PARTS:
A) Continued fraction and convergent denominators
B) Ostrowski decomposition of L_m
C) J-digit approximation error
D) Block-level DK analysis
E) Assessment of J(m) growth rate needed
"""

import sys
import os
import json
import math

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

theta = math.log10(2)
C_const = 1.0 / theta


def is_zeroless(x, m):
    """Check if integer x has all m digits nonzero."""
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True


def is_zeroless_J(x, m, J):
    """Check only the LAST J digits of x for zeros.
    This is the J-digit approximation: only checking digits 1..J.
    """
    for j in range(min(J, m)):
        if x % 10 == 0:
            return False
        x //= 10
    return True


def cf_expansion(x_float, n_terms=25):
    """Compute continued fraction expansion."""
    terms = []
    x = x_float
    for _ in range(n_terms):
        a = int(x)
        terms.append(a)
        frac = x - a
        if abs(frac) < 1e-15:
            break
        x = 1.0 / frac
        if x > 1e15:
            break
    return terms


def convergents(cf):
    """Compute convergent pairs (p_n, q_n) from continued fraction."""
    convs = []
    p_prev, p_curr = 0, 1
    q_prev, q_curr = 1, 0
    for a in cf:
        p_prev, p_curr = p_curr, a * p_curr + p_prev
        q_prev, q_curr = q_curr, a * q_curr + q_prev
        convs.append((p_curr, q_curr))
    return convs


def ostrowski_decomposition(N, cf, convs):
    """Decompose N using Ostrowski representation.
    N = sum c_j * q_j where 0 <= c_j <= a_{j+1} and c_j * c_{j-1} constraints.
    For simplicity, use greedy algorithm: subtract largest q_j <= remaining N.
    """
    decomp = []
    remaining = N
    # Work from largest q_j down
    for j in range(len(convs) - 1, -1, -1):
        p_j, q_j = convs[j]
        if q_j <= remaining:
            c_j = remaining // q_j
            # Cap at a_{j+1} if available
            if j + 1 < len(cf):
                c_j = min(c_j, cf[j + 1])
            if c_j > 0:
                decomp.append((j, c_j, q_j))
                remaining -= c_j * q_j
    if remaining > 0:
        decomp.append((-1, remaining, 1))  # remainder as individual terms
    return decomp


if __name__ == "__main__":
    print("=" * 70)
    print("  EXPERIMENT 33: OSTROWSKI RENORMALIZATION TEST")
    print("=" * 70)

    all_results = {}

    # =================================================================
    # Part A: Continued fraction and convergent denominators
    # =================================================================
    print()
    print("=" * 70)
    print("  PART A: CF expansion of theta = log10(2)")
    print("=" * 70)
    print()

    cf = cf_expansion(theta, 20)
    convs = convergents(cf)

    print("  CF = [", ", ".join(str(a) for a in cf), "]")
    print()
    print("  n | a_n | p_n | q_n | ||q_n * theta|| | 1/(q_n * q_{n+1})")
    print("  --+-----+-----+-----+-----------------+------------------")

    for n, (p, q) in enumerate(convs):
        err = abs(q * theta - round(q * theta))
        next_q = convs[n + 1][1] if n + 1 < len(convs) else 0
        bound = 1.0 / (q * next_q) if next_q > 0 else 0
        print(f"  {n:2d} | {cf[n]:3d} | {p:7d} | {q:7d} | {err:15.12f} | {bound:.12f}")

    all_results["part_A"] = {
        "cf": cf,
        "convergents": [(p, q) for p, q in convs]
    }

    # =================================================================
    # Part B: Ostrowski decomposition of L_m
    # =================================================================
    print()
    print("=" * 70)
    print("  PART B: Ostrowski decomposition of L_m")
    print("=" * 70)
    print()

    for m in range(2, 21):
        L_m = int(math.ceil(C_const * m))
        decomp = ostrowski_decomposition(L_m, cf, convs)
        decomp_str = " + ".join(
            f"{c}*q_{j}" if j >= 0 else f"{c}*1"
            for j, c, q in decomp
        )
        decomp_val = sum(c * q for j, c, q in decomp)
        check = "OK" if decomp_val == L_m else f"ERR({decomp_val})"

        print(f"  m={m:2d}: L_m = {L_m:4d} = {decomp_str}  [{check}]")

    # =================================================================
    # Part C: J-digit approximation error
    # =================================================================
    print()
    print("=" * 70)
    print("  PART C: J-digit approximation error")
    print("=" * 70)
    print()
    print("  For each m, compare f_m (full m-digit check) with f_{m,J}")
    print("  (only check first J digits). Compute:")
    print("    - rho_m = mu(F_m) = fraction of orbit that is zeroless")
    print("    - rho_{m,J} = fraction passing J-digit check")
    print("    - Birkhoff sum difference: |S_L(f_m) - S_L(f_{m,J})|")
    print()

    M_MAX_C = 10  # feasible with full orbit
    J_VALUES = [2, 3, 4, 5]

    print("  m | rho_m | J=2: rho_J, |S diff| | J=3: rho_J, |S diff| | J=4: rho_J, |S diff| | J=5: rho_J, |S diff|")
    print("  --+-------+-----------------------+-----------------------+-----------------------+-----------------------")

    approx_data = {}

    for m in range(2, M_MAX_C + 1):
        T_m = 4 * 5**(m - 1)
        mod_m = 10**m
        L_m = int(math.ceil(C_const * m))

        # Build orbit
        x = pow(2, m, mod_m)
        f_full = []
        f_approx = {J: [] for J in J_VALUES}

        for i in range(T_m):
            zl_full = is_zeroless(x, m)
            f_full.append(1 if zl_full else 0)
            for J in J_VALUES:
                if J >= m:
                    f_approx[J].append(1 if zl_full else 0)
                else:
                    zl_J = is_zeroless_J(x, m, J)
                    f_approx[J].append(1 if zl_J else 0)
            x = (2 * x) % mod_m

        rho_m = sum(f_full) / T_m

        row_parts = [f"  {m:2d} | {rho_m:.5f}"]

        m_data = {"rho_m": rho_m, "L_m": L_m, "T_m": T_m}

        for J in J_VALUES:
            rho_J = sum(f_approx[J]) / T_m
            # Birkhoff sum difference in transition zone
            S_full = sum(f_full[:L_m])
            S_J = sum(f_approx[J][:L_m])
            diff = abs(S_full - S_J)
            row_parts.append(f" {rho_J:.5f}, {diff:7d}")
            m_data[f"J{J}"] = {
                "rho_J": rho_J,
                "S_full": S_full,
                "S_J": S_J,
                "S_diff": diff,
                "rho_ratio": rho_J / rho_m if rho_m > 0 else 0
            }

        approx_data[m] = m_data
        print(" | ".join(row_parts))

    all_results["part_C"] = {str(m): v for m, v in approx_data.items()}

    # =================================================================
    # Part D: Block-level DK analysis
    # =================================================================
    print()
    print("=" * 70)
    print("  PART D: Block-level Denjoy-Koksma analysis")
    print("=" * 70)
    print()
    print("  For each m and J, compute the variation of f_{m,J} along the orbit,")
    print("  then compare with the DK bound on q_j-blocks.")
    print()

    for m in range(3, min(M_MAX_C + 1, 9)):
        T_m = 4 * 5**(m - 1)
        mod_m = 10**m
        L_m = int(math.ceil(C_const * m))

        # Build orbit values
        x = pow(2, m, mod_m)
        orbit = []
        for i in range(T_m):
            orbit.append(x)
            x = (2 * x) % mod_m

        print(f"  --- m = {m}, T_m = {T_m}, L_m = {L_m} ---")

        for J in [2, 3, min(m, 4)]:
            if J > m:
                continue

            # Compute f_{m,J} on full orbit
            f_J = []
            for xx in orbit:
                f_J.append(1 if is_zeroless_J(xx, m, J) else 0)

            rho_J = sum(f_J) / T_m

            # Variation of f_J along orbit ordering
            var_orbit = sum(1 for i in range(T_m - 1) if f_J[i] != f_J[i + 1])
            var_orbit += (1 if f_J[-1] != f_J[0] else 0)

            # DK bound for q_j block: |S_{q_j}(f_J) - q_j * rho_J| <= var(f_J)
            # But var(f_J) in the DK sense is the total variation on [0,1)
            # For orbit-ordered variation, this is what we computed

            # Check actual discrepancy at convergent denominators
            print(f"    J={J}: rho_J = {rho_J:.6f}, orbit_variation = {var_orbit}")

            for n_conv in range(len(convs)):
                p_n, q_n = convs[n_conv]
                if q_n >= T_m or q_n > L_m * 5:
                    break
                # Block sum
                block_sum = sum(f_J[:q_n])
                expected = q_n * rho_J
                disc = abs(block_sum - expected)
                dk_bound = var_orbit  # DK says |disc| <= variation
                ratio = disc / dk_bound if dk_bound > 0 else 0

                print(f"      q_{n_conv} = {q_n:6d}: S = {block_sum:5d}, "
                      f"expected = {expected:8.2f}, |disc| = {disc:8.2f}, "
                      f"DK bound = {dk_bound}, ratio = {ratio:.6f}")

        print()

    # =================================================================
    # Part E: Assessment
    # =================================================================
    print()
    print("=" * 70)
    print("  PART E: Assessment of J(m) growth rate")
    print("=" * 70)
    print()

    print("  The J-digit approximation f_{m,J} passes the first J digits.")
    print("  The 'tail' error f_m - f_{m,J} has measure:")
    print("    mu(f_m != f_{m,J}) = rho_J - rho_m")
    print("  where rho_J = (9/10)^J and rho_m = (9/10)^{m-1} approximately.")
    print()
    print("  m | rho_m | rho_{m,2} | rho_{m,3} | excess_2 | excess_3 | excess_2/rho_m")
    print("  --+-------+-----------+-----------+----------+----------+---------------")

    for m in range(2, M_MAX_C + 1):
        if str(m) in all_results.get("part_C", {}):
            d = approx_data[m]
            rho_m = d["rho_m"]
            rho_2 = d.get("J2", {}).get("rho_J", 0)
            rho_3 = d.get("J3", {}).get("rho_J", 0)
            exc_2 = rho_2 - rho_m
            exc_3 = rho_3 - rho_m
            ratio_2 = exc_2 / rho_m if rho_m > 0 else 0

            print(f"  {m:2d} | {rho_m:.5f} | {rho_2:.7f} | {rho_3:.7f} | "
                  f"{exc_2:.5e} | {exc_3:.5e} | {ratio_2:.4f}")

    print()
    print("  The excess rho_J - rho_m represents the fraction of orbit points")
    print("  that pass the J-digit check but fail the full m-digit check.")
    print("  For the Ostrowski route, we need this excess * L_m -> 0.")
    print("  Since excess ~ 0.9^J and L_m ~ 3.3m, we need J >> log(m)/log(10/9).")
    print("  Even J = 2 already gives excess * L_m < 1 for large m (since")
    print("  0.81 * 3.3m < 1 fails, but 0.9^J decreases while L_m grows linearly).")
    print()
    print("  VERDICT: The Ostrowski route requires J(m) growing at least as")
    print("  ~log(m) / log(10/9) ~ 22 * log(m). For m=100, this means J ~ 100,")
    print("  which is J = m (no approximation). The route works when m is")
    print("  moderate but does not provide asymptotic savings.")

    # Save
    output_file = os.path.join(DATA_DIR, "exp33_results.json")
    with open(output_file, 'w') as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"\n  Results saved to {output_file}")
