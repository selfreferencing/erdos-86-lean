#!/usr/bin/env python3
"""
Experiment 17: Fourier Analysis of Survivor Counts in Short Intervals

THE MATHEMATICAL FRAMEWORK
==========================

Goal: Estimate |S_m ∩ [0, L]| where S_m is the set of level-m survivors
and L = C*m for C ~ 3.32 (the critical constant 1/log10(2)).

The orbit at level m has period T_m = 4 * 5^{m-1}. Define the survivor
indicator function on Z/T_m Z:

    f_m(i) = 1 if orbit element i is a level-m survivor, else 0

Then: |S_m ∩ [0, L-1]| = sum_{i=0}^{L-1} f_m(i)

FOURIER EXPANSION: Write f_m using DFT on Z/T_m Z:

    f_m(i) = sum_{j=0}^{T_m - 1} F_m(j) * e^{2*pi*i*j*i/T_m}

where F_m(j) = (1/T_m) * sum_{i=0}^{T_m-1} f_m(i) * e^{-2*pi*i*j*i/T_m}

Note: F_m(0) = Z_m / T_m = rho_m (the survivor density).

Summing over [0, L-1]:

    |S_m ∩ [0, L-1]| = L * rho_m + sum_{j=1}^{T_m-1} F_m(j) * D_L(j)

where D_L(j) = sum_{i=0}^{L-1} e^{2*pi*i*j*i/T_m} is a geometric sum:

    D_L(j) = (1 - e^{2*pi*i*j*L/T_m}) / (1 - e^{2*pi*i*j/T_m})

    |D_L(j)| <= min(L, 1/|sin(pi*j/T_m)|) <= min(L, T_m/(2j)) for 1 <= j <= T_m/2

So: |S_m ∩ [0, L-1]| = L * rho_m + E_m

where the error E_m satisfies:

    |E_m| <= sum_{j=1}^{T_m-1} |F_m(j)| * |D_L(j)|

KEY QUESTION: Is |E_m| < 1 for large m? If so, then:

    |S_m ∩ [0, L-1]| = round(L * rho_m) = 0 for large m

since L * rho_m = C*m * (9/10)^m * correction -> 0 exponentially.

PARTS OF THIS EXPERIMENT
========================

Part A: Compute F_m(j) for m = 1..12 via DFT
Part B: Compute the error sum E_m for L = ceil(3.32 * m) explicitly
Part C: Decompose error by frequency bands (low/mid/high j)
Part D: Track |F_m(j)| decay rate as function of j and m
Part E: The critical ratio: |E_m| / (L * rho_m) -- does error dominate?
Part F: Direct verification: compare Fourier prediction to exact count
"""

import sys
import os
import json
import time
import math

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

M_MAX = 9  # T_9 = 1,562,500; T_10 = 7.8M (may be slow)
C_CRIT = 1.0 / math.log10(2)  # 3.32192...
C_VALUES = [2.5, C_CRIT, 5.0, 10.0]

LOG10_2 = math.log10(2)


def enumerate_survivors(m):
    """Return the survivor indicator array f_m[0..T_m-1] and count Z_m."""
    mod = 10 ** m
    T = 4 * 5 ** (m - 1)
    min_val = mod // 10  # 10^{m-1}

    f = [0] * T
    x = pow(2, m, mod)
    Z = 0

    for i in range(T):
        if x >= min_val and '0' not in str(x):
            f[i] = 1
            Z += 1
        x = (x * 2) % mod

    return f, Z, T


import numpy as np


def compute_error_vectorized(F_np, L, T, rho):
    """Vectorized computation of Fourier error terms.

    Returns dict with error bound, actual error, and band decomposition.
    Uses numpy throughout for speed.
    """
    j = np.arange(1, T)  # skip DC term j=0

    # Fourier magnitudes (non-DC)
    Fj = F_np[1:]
    Fj_mag = np.abs(Fj)

    # |D_L(j)| = |sin(pi*j*L/T)| / |sin(pi*j/T)|
    theta = np.pi * j / T
    sin_denom = np.abs(np.sin(theta))
    sin_numer = np.abs(np.sin(theta * L))
    # Handle near-zero denominator
    safe = sin_denom > 1e-15
    DLj_mag = np.where(safe, sin_numer / sin_denom, float(L))
    # Cap at L (the geometric sum can't exceed L)
    DLj_mag = np.minimum(DLj_mag, float(L))

    # D_L(j) = (1 - e^{2*pi*i*j*L/T}) / (1 - e^{2*pi*i*j/T})
    omega = np.exp(2j * np.pi * j / T)
    omega_L = np.exp(2j * np.pi * j * L / T)
    denom_complex = 1.0 - omega
    # Avoid division by zero
    safe_c = np.abs(denom_complex) > 1e-15
    DLj = np.where(safe_c, (1.0 - omega_L) / np.where(safe_c, denom_complex, 1.0), L)

    # Error bound: sum |F(j)| * |D_L(j)|
    contributions = Fj_mag * DLj_mag
    fourier_error_bound = float(np.sum(contributions))

    # Actual error: Re(sum F(j) * D_L(j))
    fourier_error_actual = float(np.real(np.sum(Fj * DLj)))

    # Band decomposition
    j_cutoff_low = max(1, T // L) if L > 0 else T
    j_cutoff_mid = T // 10

    # j array is 0-indexed but represents j=1..T-1
    band_low = float(np.sum(contributions[j <= j_cutoff_low - 1]))  # j <= cutoff_low
    band_high = float(np.sum(contributions[j > j_cutoff_mid - 1]))  # j > cutoff_mid
    band_mid = fourier_error_bound - band_low - band_high

    return {
        "fourier_error_bound": fourier_error_bound,
        "fourier_error_actual": fourier_error_actual,
        "band_low": band_low,
        "band_mid": band_mid,
        "band_high": band_high,
    }


def analyze_level(m):
    """Complete Fourier analysis for level m."""
    t0 = time.time()

    # Step 1: Enumerate survivors
    print(f"  Enumerating level m={m}...", end=" ", flush=True)
    f_list, Z, T = enumerate_survivors(m)
    rho = Z / T
    print(f"T={T:,}, Z={Z:,}, rho={rho:.8f}", flush=True)

    # Step 2: DFT via numpy
    print(f"  Computing FFT (T={T:,})...", end=" ", flush=True)
    t_dft = time.time()
    f_arr = np.array(f_list, dtype=np.float64)
    F_np = np.fft.fft(f_arr) / T
    print(f"done ({time.time()-t_dft:.1f}s)", flush=True)

    # Step 3: For each C value, compute the error (vectorized)
    print(f"  Computing error terms...", end=" ", flush=True)
    t_err = time.time()
    results_by_C = {}
    for C in C_VALUES:
        L = min(int(math.ceil(C * m)), T)
        if L == 0:
            L = 1

        main_term = L * rho
        exact_count = int(np.sum(f_arr[:L]))
        exact_error = exact_count - main_term

        err = compute_error_vectorized(F_np, L, T, rho)

        results_by_C[str(C)] = {
            "L": L,
            "main_term": round(main_term, 6),
            "exact_count": exact_count,
            "exact_error": round(exact_error, 6),
            "fourier_error_bound": round(err["fourier_error_bound"], 6),
            "fourier_error_actual": round(err["fourier_error_actual"], 6),
            "error_bound_over_main": round(err["fourier_error_bound"] / main_term, 4)
                if main_term > 0.001 else None,
            "band_low": round(err["band_low"], 6),
            "band_mid": round(err["band_mid"], 6),
            "band_high": round(err["band_high"], 6),
        }
    print(f"done ({time.time()-t_err:.1f}s)", flush=True)

    # Step 4: Fourier coefficient analysis (vectorized)
    mags = np.abs(F_np)
    mags_noDC = mags.copy()
    mags_noDC[0] = 0

    # Top 10 non-DC
    top_idx = np.argsort(mags_noDC)[::-1][:10]
    top10 = []
    for j in top_idx:
        j = int(j)
        v5 = 0
        jj = j
        while jj > 0 and jj % 5 == 0:
            v5 += 1
            jj //= 5
        top10.append({
            "j": j, "v5": v5,
            "magnitude": round(float(mags[j]), 10),
            "relative_to_DC": round(float(mags[j] / rho), 6) if rho > 0 else None
        })

    # L^1, L^2 of non-DC
    l1_norm = float(np.sum(mags[1:]))
    l2_norm_sq = float(np.sum(mags[1:]**2))

    # Spectral concentration
    sorted_sq = np.sort(mags[1:]**2)[::-1]
    cumsum_sq = np.cumsum(sorted_sq)
    concentration = {}
    for k_idx in [1, 5, 10, 50, 100]:
        if k_idx <= len(sorted_sq) and l2_norm_sq > 0:
            concentration[k_idx] = round(float(cumsum_sq[k_idx - 1] / l2_norm_sq), 6)

    elapsed = time.time() - t0

    result = {
        "m": m,
        "T": T,
        "Z": Z,
        "rho": round(rho, 10),
        "rho_expected": round(0.9 ** m, 10),
        "intervals": results_by_C,
        "top10_coefficients": top10,
        "l1_norm_nonDC": round(l1_norm, 8),
        "l2_norm_sq_nonDC": round(l2_norm_sq, 10),
        "spectral_concentration": concentration,
        "elapsed": round(elapsed, 2),
    }

    return result


def print_summary(results):
    """Print comprehensive summary tables."""
    print("\n" + "=" * 100)
    print("PART A: MAIN TERM vs EXACT COUNT")
    print("=" * 100)

    C = C_CRIT
    print(f"\nC = 1/log10(2) = {C:.5f} (critical constant)")
    print(f"{'m':>3}  {'L':>6}  {'T_m':>14}  {'Z_m':>10}  {'L*rho':>12}  "
          f"{'exact':>6}  {'error':>10}  {'bound':>10}  {'bnd/main':>10}")
    print("-" * 100)
    for r in results:
        m = r['m']
        iv = r['intervals'][str(C)]
        print(f"{m:>3}  {iv['L']:>6}  {r['T']:>14,}  {r['Z']:>10,}  "
              f"{iv['main_term']:>12.6f}  {iv['exact_count']:>6}  "
              f"{iv['exact_error']:>10.4f}  {iv['fourier_error_bound']:>10.4f}  "
              f"{str(iv['error_bound_over_main']) if iv['error_bound_over_main'] is not None else 'N/A':>10}")

    print("\n" + "=" * 100)
    print("PART B: ERROR BOUND TREND")
    print("  If |E_m| < 1 and L*rho < 1, then |S_m ∩ [0,L)| = 0")
    print("=" * 100)

    for C_val in C_VALUES:
        print(f"\nC = {C_val:.5f}:")
        print(f"  {'m':>3}  {'L*rho':>12}  {'|E_m| bound':>12}  "
              f"{'|E_m| actual':>12}  {'bound<1?':>8}  {'count=0?':>8}")
        print("  " + "-" * 70)
        for r in results:
            m = r['m']
            iv = r['intervals'][str(C_val)]
            bound_ok = "YES" if iv['fourier_error_bound'] < 1.0 else "no"
            count_zero = "YES" if iv['exact_count'] == 0 else "no"
            print(f"  {m:>3}  {iv['main_term']:>12.6f}  "
                  f"{iv['fourier_error_bound']:>12.4f}  "
                  f"{iv['fourier_error_actual']:>12.4f}  "
                  f"{bound_ok:>8}  {count_zero:>8}")

    print("\n" + "=" * 100)
    print("PART C: FREQUENCY BAND DECOMPOSITION (C = C_crit)")
    print("=" * 100)

    C = C_CRIT
    print(f"\n{'m':>3}  {'band_low':>12}  {'band_mid':>12}  {'band_high':>12}  "
          f"{'total_bound':>12}  {'low%':>6}  {'mid%':>6}  {'high%':>6}")
    print("-" * 90)
    for r in results:
        iv = r['intervals'][str(C)]
        total = iv['fourier_error_bound']
        if total > 0:
            lp = 100 * iv['band_low'] / total
            mp = 100 * iv['band_mid'] / total
            hp = 100 * iv['band_high'] / total
        else:
            lp = mp = hp = 0
        print(f"{r['m']:>3}  {iv['band_low']:>12.4f}  {iv['band_mid']:>12.4f}  "
              f"{iv['band_high']:>12.4f}  {total:>12.4f}  "
              f"{lp:>5.1f}%  {mp:>5.1f}%  {hp:>5.1f}%")

    print("\n" + "=" * 100)
    print("PART D: FOURIER COEFFICIENT DECAY (Top 10)")
    print("=" * 100)
    for r in results:
        m = r['m']
        print(f"\nm={m}: rho={r['rho']:.8f}, L1_nonDC={r['l1_norm_nonDC']:.6f}")
        print(f"  {'rank':>4}  {'j':>10}  {'v5(j)':>5}  {'|F(j)|':>14}  {'rel_to_DC':>10}")
        print("  " + "-" * 55)
        for rank, tc in enumerate(r['top10_coefficients']):
            print(f"  {rank+1:>4}  {tc['j']:>10}  {tc['v5']:>5}  "
                  f"{tc['magnitude']:>14.10f}  "
                  f"{tc['relative_to_DC'] if tc['relative_to_DC'] is not None else 'N/A':>10}")

    print("\n" + "=" * 100)
    print("PART E: SPECTRAL CONCENTRATION")
    print("=" * 100)
    print(f"\n{'m':>3}  {'top1':>8}  {'top5':>8}  {'top10':>8}  {'top50':>8}  {'top100':>8}")
    print("-" * 50)
    for r in results:
        sc = r['spectral_concentration']
        vals = [sc.get(k, '') for k in [1, 5, 10, 50, 100]]
        vstr = [f"{v:>8.4f}" if v != '' else f"{'---':>8}" for v in vals]
        print(f"{r['m']:>3}  {'  '.join(vstr)}")

    print("\n" + "=" * 100)
    print("PART F: CRITICAL ASSESSMENT")
    print("=" * 100)

    print("\nThe key question: does |E_m| < 1 for large m?")
    print("If YES: finiteness follows (L*rho -> 0, error < 1 => count = 0)")
    print("If NO: we need sharper bounds or a different approach\n")

    C = C_CRIT
    for r in results:
        m = r['m']
        iv = r['intervals'][str(C)]
        main = iv['main_term']
        bound = iv['fourier_error_bound']
        actual = abs(iv['fourier_error_actual'])
        exact = iv['exact_count']

        status = ""
        if bound < 1.0:
            status = "BOUND < 1 ==> count must be 0!"
        elif actual < 1.0 and exact == 0:
            status = f"bound={bound:.1f} too loose, but actual error < 1 and count=0"
        elif exact == 0:
            status = f"count=0 but bound={bound:.1f}, actual={actual:.4f}"
        else:
            status = f"count={exact}, main={main:.4f}, need sharper bound"

        print(f"  m={m:>2}: {status}")


def main():
    print("=" * 100)
    print("EXPERIMENT 17: FOURIER ANALYSIS OF SURVIVOR COUNTS IN SHORT INTERVALS")
    print("=" * 100)
    print(f"C_crit = 1/log10(2) = {C_CRIT:.6f}")
    print(f"Testing m = 1 to {M_MAX}")
    print()

    t_start = time.time()
    results = []

    for m in range(1, M_MAX + 1):
        print(f"\n--- Level m={m} ---")
        r = analyze_level(m)
        results.append(r)

    total_elapsed = time.time() - t_start
    print(f"\nAll levels complete. Total: {total_elapsed:.1f}s\n")

    print_summary(results)

    # Save results
    save_data = {
        "_meta": {
            "M_MAX": M_MAX,
            "C_VALUES": C_VALUES,
            "C_CRIT": C_CRIT,
            "total_elapsed": round(total_elapsed, 1),
        },
        "levels": [r for r in results],
    }

    path = os.path.join(DATA_DIR, "exp17_results.json")
    with open(path, 'w') as fp:
        json.dump(save_data, fp, indent=2, default=str)
    print(f"\nResults saved to {path}")


if __name__ == '__main__':
    main()
