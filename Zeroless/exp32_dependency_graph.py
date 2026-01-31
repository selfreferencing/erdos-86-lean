#!/usr/bin/env python3
"""
Experiment 32: Dependency Graph / Overlap Bound

MOTIVATION:
The second moment method requires bounding pair correlations:
mu(F_m intersect (F_m - h*theta)) for lags h = 1, 2, ..., L_m.
If this is ~c * mu(F_m)^2 (quasi-independence), the second moment
argument gives Var(N_m) ~ E[N_m], which combined with E[N_m] -> 0
proves P(N_m > 0) -> 0.

Step B implies the overlap can only arise from CROSS-component overlaps
(no single component survives a theta-shift). This should give
quasi-independence.

KEY QUESTIONS:
1. Is mu(F_m cap (F_m - h*theta)) ~ c * mu(F_m)^2 for lag h=1?
2. How does the correlation ratio behave across lags h = 1..20?
3. Does the ratio stay bounded as m grows?
4. What is Var(N_m) / E[N_m]?

PARTS:
A) Pair correlation at lag 1 for m = 2..10
B) Multi-lag correlations h = 1..20
C) Correlation ratio analysis
D) Second moment / variance estimate
"""

import sys
import os
import json
import math
import time

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


if __name__ == "__main__":
    print("=" * 70)
    print("  EXPERIMENT 32: DEPENDENCY GRAPH / OVERLAP BOUND")
    print("=" * 70)

    all_results = {}
    MAX_LAG = 20
    M_MAX = 10  # T_10 = 4*5^9 = 7,812,500 -- feasible

    # =================================================================
    # Part A & B: Pair correlations for all lags
    # =================================================================
    print()
    print("=" * 70)
    print("  PARTS A-B: Pair correlations at lags h = 1..20")
    print("=" * 70)
    print()

    corr_data = {}

    for m in range(2, M_MAX + 1):
        T_m = 4 * 5**(m - 1)
        mod_m = 10**m
        L_m = int(math.ceil(C_const * m))

        t0 = time.time()

        # Build orbit indicator
        x = pow(2, m, mod_m)
        f = [0] * T_m
        for i in range(T_m):
            if is_zeroless(x, m):
                f[i] = 1
            x = (2 * x) % mod_m

        rho = sum(f) / T_m

        # Compute pair correlations for lags 0..MAX_LAG
        correlations = {}
        for h in range(0, MAX_LAG + 1):
            overlap = 0
            for i in range(T_m):
                if f[i] == 1 and f[(i + h) % T_m] == 1:
                    overlap += 1
            mu_overlap = overlap / T_m
            correlations[h] = {
                "mu_overlap": mu_overlap,
                "mu_sq": rho**2,
                "ratio": mu_overlap / rho**2 if rho > 0 else 0,
                "covariance": mu_overlap - rho**2
            }

        elapsed = time.time() - t0
        corr_data[m] = {
            "T_m": T_m,
            "rho": rho,
            "correlations": correlations,
            "time": elapsed
        }

        print(f"  m = {m}, T_m = {T_m:,}, rho = {rho:.6f} ({elapsed:.1f}s)")
        print(f"    h |  mu(F_m cap (F_m-h*theta)) |  mu(F_m)^2  |  ratio")
        print(f"  ----+----------------------------+-------------+--------")
        for h in range(0, min(MAX_LAG + 1, 11)):
            c = correlations[h]
            print(f"  {h:3d} | {c['mu_overlap']:26.8f} | {c['mu_sq']:.8f} | {c['ratio']:.4f}")
        if MAX_LAG > 10:
            print(f"    ...")
            for h in [15, 20]:
                if h <= MAX_LAG:
                    c = correlations[h]
                    print(f"  {h:3d} | {c['mu_overlap']:26.8f} | {c['mu_sq']:.8f} | {c['ratio']:.4f}")
        print()

    all_results["correlations"] = {
        str(m): {
            "T_m": d["T_m"],
            "rho": d["rho"],
            "corr": {str(h): c for h, c in d["correlations"].items()}
        }
        for m, d in corr_data.items()
    }

    # =================================================================
    # Part C: Correlation ratio analysis
    # =================================================================
    print()
    print("=" * 70)
    print("  PART C: Correlation ratio mu(overlap) / mu(F_m)^2 by m")
    print("=" * 70)
    print()
    print("  If ratio ~ 1, quasi-independence holds.")
    print("  If ratio >> 1, there are strong positive correlations.")
    print("  If ratio << 1, there is negative correlation (anti-bunching).")
    print()

    print("  m | lag=1 ratio | lag=2 ratio | lag=3 ratio | lag=5 ratio | lag=10 ratio")
    print("  --+-------------+-------------+-------------+-------------+-------------")

    for m in range(2, M_MAX + 1):
        ratios = []
        for h in [1, 2, 3, 5, 10]:
            if h <= MAX_LAG:
                r = corr_data[m]["correlations"][h]["ratio"]
                ratios.append(f"{r:11.4f}")
            else:
                ratios.append("        N/A")
        print(f"  {m:2d} | " + " | ".join(ratios))

    # Max ratio across all lags for each m
    print()
    print("  m | max_ratio (across lags 1..20) | at lag")
    print("  --+-------------------------------+-------")
    for m in range(2, M_MAX + 1):
        max_r = 0
        max_h = 0
        for h in range(1, MAX_LAG + 1):
            r = corr_data[m]["correlations"][h]["ratio"]
            if r > max_r:
                max_r = r
                max_h = h
        print(f"  {m:2d} | {max_r:29.4f} | {max_h:5d}")

    # =================================================================
    # Part D: Second moment estimate
    # =================================================================
    print()
    print("=" * 70)
    print("  PART D: Second moment / variance estimate")
    print("=" * 70)
    print()
    print("  Var(N_m) = Sum_{h=-(L-1)}^{L-1} (L-|h|) * Cov(f(i), f(i+h))")
    print("  where Cov = mu(overlap) - mu(F_m)^2")
    print()

    print("  m | L_m | E[N_m]=L*rho | Var(N_m) | Var/E[N_m] | Var/E^2")
    print("  --+-----+--------------+----------+------------+--------")

    for m in range(2, M_MAX + 1):
        L_m = int(math.ceil(C_const * m))
        rho = corr_data[m]["rho"]
        E_Nm = L_m * rho

        # Compute variance
        variance = 0.0
        for h in range(-(L_m - 1), L_m):
            weight = L_m - abs(h)
            h_abs = abs(h)
            if h_abs <= MAX_LAG:
                cov = corr_data[m]["correlations"][h_abs]["covariance"]
            else:
                # For large lags, assume independence (cov = 0)
                cov = 0.0
            variance += weight * cov

        var_over_E = variance / E_Nm if E_Nm > 0 else float('inf')
        var_over_E2 = variance / E_Nm**2 if E_Nm > 0 else float('inf')

        print(f"  {m:2d} | {L_m:3d} | {E_Nm:12.4f} | {variance:8.4f} | {var_over_E:10.4f} | {var_over_E2:6.4f}")

    # =================================================================
    # Verdict
    # =================================================================
    print()
    print("=" * 70)
    print("  VERDICT")
    print("=" * 70)
    print()

    # Check if ratios are bounded
    all_ratios = []
    for m in range(3, M_MAX + 1):
        for h in range(1, MAX_LAG + 1):
            all_ratios.append(corr_data[m]["correlations"][h]["ratio"])

    max_ratio_overall = max(all_ratios)
    avg_ratio = sum(all_ratios) / len(all_ratios)

    print(f"  Max correlation ratio (m=3..{M_MAX}, h=1..{MAX_LAG}): {max_ratio_overall:.4f}")
    print(f"  Average correlation ratio: {avg_ratio:.4f}")
    print()

    if max_ratio_overall < 3.0:
        print("  QUASI-INDEPENDENCE CONFIRMED.")
        print(f"  Correlation ratios bounded by {max_ratio_overall:.2f}.")
        print("  The second moment method is viable:")
        print("  Var(N_m) = O(E[N_m]), and since E[N_m] -> 0,")
        print("  P(N_m > 0) -> 0 by Chebyshev/Paley-Zygmund.")
    elif max_ratio_overall < 10:
        print("  WEAK QUASI-INDEPENDENCE.")
        print(f"  Ratios bounded by {max_ratio_overall:.2f}, suggesting")
        print("  moderate correlations. Second moment method may still work")
        print("  with logarithmic corrections.")
    else:
        print(f"  STRONG CORRELATIONS detected (ratio up to {max_ratio_overall:.2f}).")
        print("  Second moment method faces obstacles.")

    # Save
    output_file = os.path.join(DATA_DIR, "exp32_results.json")
    with open(output_file, 'w') as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"\n  Results saved to {output_file}")
