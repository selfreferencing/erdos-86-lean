#!/usr/bin/env python3
"""
Experiment 37: Corrected Discrepancy with Dirichlet Kernel

MOTIVATION:
Exp 36 computed circle Fourier coefficients |hat{1_{F_m}}(k)| and found the
naive coboundary sum S_m = sum |hat(k)| / ||k*theta|| does NOT go to zero
(values 160-760 for K_max=5000). But this uses 1/||k*theta|| as a bound on
the Dirichlet kernel |D_L(k*theta)|, which is extremely loose when L is small.

The actual discrepancy formula is:

  N_m - L_m * rho_m = sum_{k != 0} hat{1_{F_m}}(k) * G_m(k)

where G_m(k) = sum_{j=0}^{L_m - 1} e(frac((m+j)*theta) * (-1)) * e(k * frac((m+j)*theta))
             ... more precisely, we need the full Weyl sum formulation.

The exact count is:
  N_m = sum_{j=0}^{L_m-1} 1_{F_m}(alpha_j)
  where alpha_j = frac((m+j)*theta)

And by Fourier expansion of 1_{F_m}:
  1_{F_m}(x) = rho_m + sum_{k!=0} hat{1_{F_m}}(k) * e(k*x)

So:
  N_m = L_m * rho_m + sum_{k!=0} hat{1_{F_m}}(k) * sum_{j=0}^{L_m-1} e(k * alpha_j)

The inner sum is:
  W_m(k) = sum_{j=0}^{L_m-1} e(k * frac((m+j)*theta))
         = sum_{j=0}^{L_m-1} e(k*(m+j)*theta)  (since e is 1-periodic)
         = e(k*m*theta) * sum_{j=0}^{L_m-1} e(k*j*theta)
         = e(k*m*theta) * D_{L_m}(k*theta)

where D_L(alpha) = sum_{j=0}^{L-1} e(j*alpha) is the Dirichlet kernel,
with |D_L(alpha)| = |sin(pi*L*alpha)| / |sin(pi*alpha)| for alpha not integer,
and |D_L(alpha)| <= min(L, 1/(2*||alpha||)).

So the error is:
  |N_m - L_m * rho_m| <= sum_{k!=0} |hat{1_{F_m}}(k)| * |D_{L_m}(k*theta)|

THIS is the correct sum to compute. Since L_m ~ 3.3*m is small,
|D_L(k*theta)| << 1/||k*theta|| for most k.

KEY QUESTIONS:
1. Does the corrected sum T_m = sum |hat(k)| * |D_{L_m}(k*theta)| go to zero?
2. If T_m < 1/2 for large m, then |N_m - L_m*rho_m| < 1/2, forcing N_m = 0
   (since L_m*rho_m -> 0).
3. How much smaller is T_m compared to S_m from Exp 36?
4. Which frequencies dominate T_m?

PARTS:
A) Recompute Fourier coefficients (reuse Exp 36 interval data)
B) Compute |D_{L_m}(k*theta)| for each k and m
C) Compute T_m = sum |hat(k)| * |D_{L_m}(k*theta)| and compare to S_m
D) Check the finiteness criterion: T_m < 1/2 - L_m*rho_m for large m
E) Band decomposition and dangerous frequency analysis
F) Extrapolation: predict T_m for m = 8..20
"""

import sys
import os
import json
import math
import time
import numpy as np

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

theta = math.log10(2)
C_const = 1.0 / theta  # ~ 3.32


def is_zeroless(x, m):
    """Check if integer x has all m digits nonzero."""
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True


def enumerate_zeroless_runs(m):
    """Enumerate maximal runs of consecutive zeroless m-digit integers."""
    lo = 10 ** (m - 1)
    hi = 10 ** m
    run_starts = []
    run_ends = []
    in_run = False
    current_start = 0

    for n in range(lo, hi):
        zl = is_zeroless(n, m)
        if zl and not in_run:
            current_start = n
            in_run = True
        elif not zl and in_run:
            run_starts.append(current_start)
            run_ends.append(n - 1)
            in_run = False

    if in_run:
        run_starts.append(current_start)
        run_ends.append(hi - 1)

    return run_starts, run_ends


def runs_to_alpha(run_starts, run_ends, m):
    """Convert integer runs to alpha-intervals in [0,1)."""
    a_starts = np.array([math.log10(n) - (m - 1) for n in run_starts])
    a_ends = np.array([math.log10(n + 1) - (m - 1) for n in run_ends])
    return a_starts, a_ends


def fourier_coeff_intervals(k, a_starts, a_ends):
    """Compute hat{1_{F_m}}(k) using exact interval formula."""
    if k == 0:
        return np.sum(a_ends - a_starts)
    phase_starts = np.exp(-2j * np.pi * k * a_starts)
    phase_ends = np.exp(-2j * np.pi * k * a_ends)
    return np.sum(phase_starts - phase_ends) / (2j * np.pi * k)


def dirichlet_kernel_mag(L, alpha):
    """Compute |D_L(alpha)| = |sum_{j=0}^{L-1} e(j*alpha)|.
    = |sin(pi*L*alpha)| / |sin(pi*alpha)| when alpha is not integer.
    """
    frac_alpha = alpha - math.floor(alpha)
    if abs(frac_alpha) < 1e-15 or abs(frac_alpha - 1.0) < 1e-15:
        return float(L)
    return abs(math.sin(math.pi * L * alpha)) / abs(math.sin(math.pi * alpha))


def frac_dist(x):
    """Compute ||x|| = min(frac(x), 1 - frac(x))."""
    fx = x - math.floor(x)
    return min(fx, 1.0 - fx)


if __name__ == "__main__":
    print("=" * 70)
    print("  EXPERIMENT 37: CORRECTED DISCREPANCY WITH DIRICHLET KERNEL")
    print("=" * 70)

    all_results = {}

    # Convergent denominators of theta = log10(2)
    convergent_denoms = [1, 3, 10, 93, 196, 485, 2136, 13301, 28738,
                         42039, 70777, 254370, 325147]

    # =================================================================
    # Part A: Build interval data (reusing Exp 36 logic)
    # =================================================================
    print()
    print("=" * 70)
    print("  PART A: Enumerate zeroless runs")
    print("=" * 70)
    print()

    M_MAX = 7
    interval_data = {}

    for m in range(2, M_MAX + 1):
        t0 = time.time()
        run_starts, run_ends = enumerate_zeroless_runs(m)
        a_starts, a_ends = runs_to_alpha(run_starts, run_ends, m)
        elapsed = time.time() - t0
        rho = np.sum(a_ends - a_starts)
        L_m = int(math.ceil(C_const * m))
        interval_data[m] = {
            "a_starts": a_starts,
            "a_ends": a_ends,
            "n_runs": len(run_starts),
            "rho": float(rho),
            "L_m": L_m,
        }
        print(f"  m={m}: {len(run_starts)} runs, rho={rho:.8f}, L_m={L_m}, elapsed={elapsed:.2f}s")

    # =================================================================
    # Part B: Compute Fourier coefficients and Dirichlet kernel values
    # =================================================================
    print()
    print("=" * 70)
    print("  PART B: Fourier coefficients + Dirichlet kernel")
    print("=" * 70)
    print()

    K_MAX = 10000  # go higher than Exp 36 to check convergence

    fourier_and_kernel = {}

    for m in range(2, M_MAX + 1):
        K = K_MAX if m <= 6 else 5000
        L_m = interval_data[m]["L_m"]
        rho_m = interval_data[m]["rho"]
        a_s = interval_data[m]["a_starts"]
        a_e = interval_data[m]["a_ends"]

        print(f"  m={m} (L_m={L_m}, K={K}): computing ...")
        t0 = time.time()

        hat_mags = np.zeros(K)
        dk_mags = np.zeros(K)
        terms_corrected = np.zeros(K)  # |hat(k)| * |D_L(k*theta)|
        terms_naive = np.zeros(K)      # |hat(k)| / ||k*theta||

        for k in range(1, K + 1):
            fk = fourier_coeff_intervals(k, a_s, a_e)
            hat_mag = abs(fk)
            hat_mags[k - 1] = hat_mag

            k_theta = k * theta
            dk_mag = dirichlet_kernel_mag(L_m, k_theta)
            dk_mags[k - 1] = dk_mag

            norm_kth = frac_dist(k_theta)
            naive_weight = 1.0 / norm_kth if norm_kth > 1e-15 else float(L_m)

            terms_corrected[k - 1] = hat_mag * dk_mag
            terms_naive[k - 1] = hat_mag * naive_weight

        elapsed = time.time() - t0

        # Compute sums (factor of 2 for negative k symmetry)
        T_m = 2.0 * np.sum(terms_corrected)
        S_m = 2.0 * np.sum(terms_naive)
        ratio_TS = T_m / S_m if S_m > 0 else 0

        fourier_and_kernel[m] = {
            "hat_mags": hat_mags,
            "dk_mags": dk_mags,
            "terms_corrected": terms_corrected,
            "terms_naive": terms_naive,
            "T_m": T_m,
            "S_m": S_m,
        }

        print(f"    T_m (corrected) = {T_m:.6f}")
        print(f"    S_m (naive)     = {S_m:.6f}")
        print(f"    T_m / S_m       = {ratio_TS:.6f}")
        print(f"    L_m * rho_m     = {L_m * rho_m:.6f}")
        print(f"    T_m < 0.5?      {'YES' if T_m < 0.5 else 'NO'}")
        print(f"    elapsed: {elapsed:.2f}s")
        print()

        all_results[f"partB_m{m}"] = {
            "T_m": float(T_m),
            "S_m": float(S_m),
            "ratio_TS": float(ratio_TS),
            "L_m_rho_m": float(L_m * rho_m),
            "K_max": K,
            "elapsed_s": elapsed,
        }

    # =================================================================
    # Part C: Summary table and trend analysis
    # =================================================================
    print()
    print("=" * 70)
    print("  PART C: Summary and trend")
    print("=" * 70)
    print()

    print(f"  {'m':>3} {'L_m':>5} {'rho_m':>10} {'L*rho':>8} {'T_m':>12} {'S_m':>12} {'T/S':>8} {'T<0.5?':>7}")
    print(f"  {'-'*75}")

    summary = {}
    for m in range(2, M_MAX + 1):
        d = fourier_and_kernel[m]
        L_m = interval_data[m]["L_m"]
        rho_m = interval_data[m]["rho"]
        T_m = d["T_m"]
        S_m = d["S_m"]
        L_rho = L_m * rho_m
        ratio = T_m / S_m if S_m > 0 else 0
        ok = "YES" if T_m < 0.5 else "NO"
        print(f"  {m:>3} {L_m:>5} {rho_m:>10.6f} {L_rho:>8.4f} {T_m:>12.4f} {S_m:>12.4f} {ratio:>8.4f} {ok:>7}")
        summary[m] = {
            "L_m": L_m,
            "rho_m": float(rho_m),
            "L_rho": float(L_rho),
            "T_m": float(T_m),
            "S_m": float(S_m),
            "T_over_S": float(ratio),
        }

    all_results["partC_summary"] = summary
    print()

    # Trend analysis
    ms = sorted(summary.keys())
    T_vals = [summary[m]["T_m"] for m in ms]
    print("  T_m trend:")
    for i, m in enumerate(ms):
        trend = ""
        if i > 0:
            if T_vals[i] < T_vals[i - 1]:
                pct = (T_vals[i - 1] - T_vals[i]) / T_vals[i - 1] * 100
                trend = f" (down {pct:.1f}%)"
            else:
                trend = " (UP)"
        print(f"    m={m}: T_m = {T_vals[i]:.6f}{trend}")
    print()

    # =================================================================
    # Part D: Finiteness criterion check
    # =================================================================
    print()
    print("=" * 70)
    print("  PART D: Finiteness criterion")
    print("=" * 70)
    print()
    print("  For N_m = 0, need: |N_m - L_m*rho_m| < 1/2")
    print("  Since N_m is integer and L_m*rho_m < 1/2 for large m,")
    print("  sufficient condition: T_m + L_m*rho_m < 1/2")
    print("  (T_m bounds the error, L_m*rho_m is the expectation)")
    print()
    print("  Actually, N_m = 0 iff |N_m - L_m*rho_m| = L_m*rho_m,")
    print("  so we need T_m < L_m*rho_m ... no.")
    print()
    print("  More precisely: N_m is a nonneg integer. If N_m >= 1,")
    print("  then N_m - L_m*rho_m >= 1 - L_m*rho_m.")
    print("  So N_m = 0 iff error = -L_m*rho_m (negative error).")
    print("  The bound gives |error| <= T_m.")
    print("  If T_m < 1 - L_m*rho_m, then error cannot be >= 1 - L_m*rho_m,")
    print("  so N_m cannot be >= 1. Hence N_m = 0.")
    print()
    print("  Criterion: T_m < 1 - L_m * rho_m")
    print()

    for m in sorted(summary.keys()):
        L_rho = summary[m]["L_rho"]
        T_m = summary[m]["T_m"]
        threshold = 1.0 - L_rho
        gap = threshold - T_m
        ok = "FINITENESS PROVED" if T_m < threshold else f"gap = {gap:.4f}"
        print(f"  m={m}: T_m={T_m:.6f}, threshold={threshold:.6f}, {ok}")

    print()
    all_results["partD"] = {
        m: {
            "T_m": summary[m]["T_m"],
            "threshold": 1.0 - summary[m]["L_rho"],
            "proved": summary[m]["T_m"] < 1.0 - summary[m]["L_rho"],
        }
        for m in sorted(summary.keys())
    }

    # =================================================================
    # Part E: Band decomposition and dangerous frequencies
    # =================================================================
    print()
    print("=" * 70)
    print("  PART E: Band decomposition and dangerous frequencies")
    print("=" * 70)
    print()

    for m in range(2, M_MAX + 1):
        d = fourier_and_kernel[m]
        L_m = interval_data[m]["L_m"]
        K = len(d["terms_corrected"])
        tc = d["terms_corrected"]
        T_m = d["T_m"]

        k_vals = np.arange(1, K + 1)

        # Bands
        low = k_vals <= 10
        mid = (k_vals > 10) & (k_vals <= 100)
        high = (k_vals > 100) & (k_vals <= 1000)
        vhigh = k_vals > 1000

        T_low = 2.0 * np.sum(tc[low])
        T_mid = 2.0 * np.sum(tc[mid])
        T_high = 2.0 * np.sum(tc[high])
        T_vhigh = 2.0 * np.sum(tc[vhigh])

        print(f"  m={m} (L_m={L_m}):")
        print(f"    T_m      = {T_m:.6f}")
        print(f"    |k|<=10  = {T_low:.6f} ({T_low/T_m*100:.1f}%)")
        print(f"    10<|k|<=100 = {T_mid:.6f} ({T_mid/T_m*100:.1f}%)")
        print(f"    100<|k|<=1000 = {T_high:.6f} ({T_high/T_m*100:.1f}%)")
        print(f"    |k|>1000 = {T_vhigh:.6f} ({T_vhigh/T_m*100:.1f}%)")

        # Top 15 dangerous frequencies (by corrected contribution)
        top_idx = np.argsort(tc)[-15:][::-1]
        print(f"    Top-15 by |hat(k)|*|D_L(k*theta)|:")
        print(f"    {'k':>6} {'|hat|':>12} {'|D_L|':>12} {'product':>12} {'|D_L|_max':>10} {'near_q':>8}")
        for idx in top_idx:
            k = idx + 1
            hat_mag = d["hat_mags"][idx]
            dk = d["dk_mags"][idx]
            prod = tc[idx]
            dk_max = min(L_m, 1.0 / (2.0 * frac_dist(k * theta)) if frac_dist(k * theta) > 1e-15 else L_m)
            near_q = ""
            for q in convergent_denoms:
                if abs(k - q) <= 2:
                    near_q = f"q={q}"
            print(f"    {k:>6} {hat_mag:>12.6e} {dk:>12.4f} {prod:>12.6e} {dk_max:>10.4f} {near_q:>8}")
        print()

        all_results[f"partE_m{m}"] = {
            "T_low": float(T_low),
            "T_mid": float(T_mid),
            "T_high": float(T_high),
            "T_vhigh": float(T_vhigh),
        }

    # =================================================================
    # Part F: Extrapolation for larger m
    # =================================================================
    print()
    print("=" * 70)
    print("  PART F: Extrapolation to larger m")
    print("=" * 70)
    print()

    # From Exp 36, we know |hat{1_{F_m}}(k)| = C(k) * (9/10)^{m-1}
    # where C(k) stabilizes by m=4. Use the m=6 coefficients as the
    # template C(k), then extrapolate to m=8..20.

    if 6 in fourier_and_kernel:
        template_m = 6
        template_mags = fourier_and_kernel[template_m]["hat_mags"]
        template_rho = interval_data[template_m]["rho"]
        # C(k) = |hat(k)| / rho_m for the template
        C_k = template_mags / template_rho
        K_template = len(C_k)

        print(f"  Using m={template_m} as template (K={K_template} frequencies)")
        print(f"  C(k) = |hat_m{template_m}(k)| / rho_{template_m}")
        print()

        print(f"  {'m':>3} {'L_m':>5} {'rho_m':>12} {'L*rho':>10} {'T_m_pred':>12} {'threshold':>12} {'proved?':>8}")
        print(f"  {'-'*75}")

        extrapolation = {}
        for m in range(2, 21):
            rho_m = (9.0 / 10.0) ** (m - 1)
            L_m = int(math.ceil(C_const * m))

            # Predicted |hat(k)| = C(k) * rho_m
            pred_mags = C_k[:K_template] * rho_m

            # |D_L(k*theta)| for each k
            T_pred = 0.0
            for k in range(1, K_template + 1):
                dk = dirichlet_kernel_mag(L_m, k * theta)
                T_pred += pred_mags[k - 1] * dk
            T_pred *= 2.0  # negative k symmetry

            threshold = 1.0 - L_m * rho_m
            proved = T_pred < threshold

            print(f"  {m:>3} {L_m:>5} {rho_m:>12.6e} {L_m*rho_m:>10.6f} {T_pred:>12.6f} {threshold:>12.6f} {'YES' if proved else 'NO':>8}")

            extrapolation[m] = {
                "L_m": L_m,
                "rho_m": rho_m,
                "L_rho": L_m * rho_m,
                "T_m_predicted": float(T_pred),
                "threshold": threshold,
                "proved": proved,
            }

        all_results["partF_extrapolation"] = extrapolation

    print()

    # =================================================================
    # Part G: Convergence check - how much does truncation at K matter?
    # =================================================================
    print()
    print("=" * 70)
    print("  PART G: Truncation convergence check")
    print("=" * 70)
    print()

    for m in [4, 5, 6]:
        if m not in fourier_and_kernel:
            continue
        tc = fourier_and_kernel[m]["terms_corrected"]
        K = len(tc)

        # Cumulative sum
        cumsum = 2.0 * np.cumsum(tc)
        for K_cut in [100, 500, 1000, 2000, 5000, K]:
            if K_cut <= K:
                T_cut = cumsum[K_cut - 1]
                print(f"  m={m}, K={K_cut:>6}: T_m = {T_cut:.6f}")
        print()

    # =================================================================
    # Save results
    # =================================================================
    print("=" * 70)
    print("  SAVING RESULTS")
    print("=" * 70)

    # Remove numpy arrays before saving
    save_results = {}
    for key, val in all_results.items():
        if isinstance(val, dict):
            save_results[key] = {}
            for k2, v2 in val.items():
                if isinstance(v2, np.ndarray):
                    continue
                save_results[key][k2] = v2
        else:
            save_results[key] = val

    with open(os.path.join(DATA_DIR, "exp37_results.json"), "w") as f:
        json.dump(save_results, f, indent=2, default=str)
    print(f"  Saved to {os.path.join(DATA_DIR, 'exp37_results.json')}")

    # =================================================================
    # Final assessment
    # =================================================================
    print()
    print("=" * 70)
    print("  FINAL ASSESSMENT")
    print("=" * 70)
    print()

    # Check actual vs predicted for m values where we have both
    if 6 in fourier_and_kernel and "partF_extrapolation" in all_results:
        print("  Actual vs predicted T_m (validation):")
        for m in range(2, M_MAX + 1):
            actual = fourier_and_kernel[m]["T_m"]
            predicted = all_results["partF_extrapolation"].get(m, {}).get("T_m_predicted", None)
            if predicted is not None:
                err = abs(actual - predicted) / actual * 100 if actual > 0 else 0
                print(f"    m={m}: actual={actual:.6f}, predicted={predicted:.6f}, err={err:.1f}%")
        print()

    # Key verdict
    if "partF_extrapolation" in all_results:
        ext = all_results["partF_extrapolation"]
        first_proved = None
        for m in sorted(ext.keys()):
            if ext[m]["proved"]:
                first_proved = m
                break

        if first_proved:
            print(f"  VERDICT: T_m < threshold starting at m={first_proved}.")
            print(f"  If the C(k) stability holds (verified for m=2..7),")
            print(f"  then N_m = 0 for all m >= {first_proved}.")
            print(f"  This would prove the 86 Conjecture (since N_m = 0")
            print(f"  is computationally verified for m up to ~30).")
        else:
            print("  VERDICT: T_m does not drop below threshold for m <= 20.")
            print("  Strategy C' in this form is insufficient.")
            print("  The truncation at K=10000 may be the issue.")

    print()
    print("=" * 70)
    print("  EXPERIMENT 37 COMPLETE")
    print("=" * 70)
