#!/usr/bin/env python3
"""
Experiment 15: Small-Survivor Census

Tests whether survivors at level m are equidistributed in the orbit [0, T_m),
and specifically whether "small" survivors (orbit index i < C*m) vanish for
large m.

Connection to finiteness: A zeroless 2^n has D(n) ~ 0.301n digits. At level
m = D(n), orbit index i = n - m ~ 2.32m. If no survivors cluster in [0, C*m]
for large m, no zeroless 2^n can exist beyond a finite threshold.

Parts:
  A - Small-survivor counts for various C thresholds
  B - Chi-squared equidistribution test across bins
  C - Local vs global density ratios
  D - Known zeroless powers: survival and drop-off tracking
"""

import sys
import os
import json
import time
import math

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

M_MAX = 12
C_VALUES = [2.5, 3.32, 5.0, 10.0, 50.0, 100.0]
NUM_BINS_TARGET = 100

# All 35 known zeroless powers of 2 (n where 2^n has no digit 0)
KNOWN_ZEROLESS = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19,
    24, 25, 27, 28, 31, 32, 33, 34, 35, 36, 37, 39, 49,
    51, 67, 72, 76, 77, 81, 86
]

LOG10_2 = math.log10(2)  # 0.30102999566...


def digit_count(n):
    """Number of digits of 2^n in base 10."""
    return int(n * LOG10_2) + 1


def chi2_critical(df, alpha=0.05):
    """Wilson-Hilferty approximation for chi-squared critical value."""
    z = 1.6449  # z_{0.05} for one-sided
    term = 1.0 - 2.0 / (9.0 * df) + z * math.sqrt(2.0 / (9.0 * df))
    return df * term ** 3


def enumerate_level(m):
    """Single-pass orbit enumeration collecting data for Parts A-D."""
    mod = 10 ** m
    T = 4 * 5 ** (m - 1)
    min_val = mod // 10

    # Part A: small-survivor thresholds
    thresholds = {}
    for c in C_VALUES:
        thresholds[c] = min(int(c * m), T)
    max_threshold = max(thresholds.values())
    small_counts = {c: 0 for c in C_VALUES}

    # Store actual small survivors for m <= 8, C <= 3.32
    small_lists = {}
    if m <= 8:
        for c in C_VALUES:
            if c <= 3.32:
                small_lists[c] = []

    # Part B: bins
    num_bins = min(NUM_BINS_TARGET, T)
    bin_size = T / num_bins
    bin_counts = [0] * num_bins

    # Part D: known zeroless orbit indices at this level
    known_set = set()
    known_survivors = []
    for n in KNOWN_ZEROLESS:
        if n >= m and digit_count(n) >= m:
            idx = n - m
            if idx < T:
                known_set.add(idx)

    known_found = set()

    # Orbit scan
    Z_m = 0
    x = pow(2, m, mod)
    t0 = time.time()

    for i in range(T):
        if x >= min_val and '0' not in str(x):
            Z_m += 1

            # Part A: check small thresholds
            if i < max_threshold:
                for c in C_VALUES:
                    if i < thresholds[c]:
                        small_counts[c] += 1
                        if m <= 8 and c in small_lists:
                            small_lists[c].append(i)

            # Part B: bin assignment
            b = min(int(i / bin_size), num_bins - 1)
            bin_counts[b] += 1

            # Part D: known zeroless check
            if i in known_set:
                known_found.add(i)

        x = (x * 2) % mod

        # Progress reporting
        if m >= 10 and i > 0 and i % (T // 5) == 0:
            el = time.time() - t0
            print(f"  [m={m}: {100*i//T}%, {el:.1f}s]",
                  file=sys.stderr, flush=True)

    elapsed = time.time() - t0

    # Part A: expected counts under equidistribution
    density = Z_m / T
    small_expected = {}
    for c in C_VALUES:
        interval_len = min(c * m, T)
        small_expected[c] = Z_m * interval_len / T

    # Part B: chi-squared
    E_per_bin = Z_m / num_bins
    if E_per_bin > 0:
        chi2 = sum((obs - E_per_bin) ** 2 / E_per_bin for obs in bin_counts)
    else:
        chi2 = 0.0
    df = num_bins - 1
    crit = chi2_critical(df) if df > 0 else 0.0
    equidist_pass = chi2 <= crit

    # Part C: density ratios
    density_ratios = {}
    for c in C_VALUES:
        interval_len = min(c * m, T)
        if interval_len > 0 and density > 0:
            local_density = small_counts[c] / interval_len
            density_ratios[c] = local_density / density
        else:
            density_ratios[c] = float('nan')

    # Part D: collect known survivors
    known_surviving_n = []
    known_orbit_indices = []
    for n in KNOWN_ZEROLESS:
        if n >= m and digit_count(n) >= m:
            idx = n - m
            if idx < T and idx in known_found:
                known_surviving_n.append(n)
                known_orbit_indices.append(idx)

    result = {
        "T_m": T,
        "Z_m": Z_m,
        "density": density,
        "small_counts": {str(c): small_counts[c] for c in C_VALUES},
        "small_expected": {str(c): round(small_expected[c], 2) for c in C_VALUES},
        "density_ratios": {str(c): round(density_ratios[c], 4)
                          if not math.isnan(density_ratios[c]) else None
                          for c in C_VALUES},
        "num_bins": num_bins,
        "chi2": round(chi2, 2),
        "df": df,
        "chi2_crit": round(crit, 2),
        "equidist_pass": equidist_pass,
        "bin_max": max(bin_counts) if bin_counts else 0,
        "bin_min": min(bin_counts) if bin_counts else 0,
        "E_per_bin": round(E_per_bin, 2),
        "known_zeroless_count": len(known_surviving_n),
        "known_zeroless_n": known_surviving_n,
        "known_zeroless_orbit_indices": known_orbit_indices,
        "elapsed": round(elapsed, 3),
    }

    if small_lists:
        result["small_lists"] = {str(c): lst for c, lst in small_lists.items()}

    return result


def part_A_summary(results):
    """Print small-survivor census table."""
    print("=" * 100)
    print("PART A: Small-Survivor Census")
    print("=" * 100)
    print()

    # Header
    hdr = f"{'m':>3}  {'T_m':>14}  {'Z_m':>12}  {'density':>8}"
    for c in [2.5, 3.32, 5.0, 10.0, 100.0]:
        hdr += f"  C={c:<5} (exp)"
    print(hdr)
    print("-" * len(hdr))

    for m in range(1, M_MAX + 1):
        r = results[m]
        line = f"{m:>3}  {r['T_m']:>14,}  {r['Z_m']:>12,}  {r['density']:>8.4f}"
        for c in [2.5, 3.32, 5.0, 10.0, 100.0]:
            sc = r['small_counts'][str(c)]
            se = r['small_expected'][str(c)]
            line += f"  {sc:>5} ({se:>6.1f})"
        print(line)

    print()


def part_B_summary(results):
    """Print equidistribution chi-squared test table."""
    print("=" * 100)
    print("PART B: Equidistribution Test (chi-squared, alpha=0.05)")
    print("=" * 100)
    print()

    hdr = f"{'m':>3}  {'bins':>5}  {'E/bin':>10}  {'chi2':>10}  {'crit':>10}  {'pass?':>6}"
    print(hdr)
    print("-" * len(hdr))

    for m in range(1, M_MAX + 1):
        r = results[m]
        p = "YES" if r['equidist_pass'] else "NO"
        line = (f"{m:>3}  {r['num_bins']:>5}  {r['E_per_bin']:>10.2f}  "
                f"{r['chi2']:>10.2f}  {r['chi2_crit']:>10.2f}  {p:>6}")
        print(line)

    print()


def part_C_summary(results):
    """Print density ratio table."""
    print("=" * 100)
    print("PART C: Density Ratios (local/global) in [0, C*m)")
    print("       ratio = 1 means equidistributed; < 1 means under-represented")
    print("=" * 100)
    print()

    hdr = f"{'m':>3}  {'rho_m':>8}"
    for c in C_VALUES:
        hdr += f"  {'C='+str(c):>8}"
    print(hdr)
    print("-" * len(hdr))

    for m in range(1, M_MAX + 1):
        r = results[m]
        line = f"{m:>3}  {r['density']:>8.4f}"
        for c in C_VALUES:
            dr = r['density_ratios'][str(c)]
            if dr is not None:
                line += f"  {dr:>8.4f}"
            else:
                line += f"  {'N/A':>8}"
        print(line)

    print()


def part_D_summary(results):
    """Print known zeroless powers tracking."""
    print("=" * 100)
    print("PART D: Known Zeroless Powers at Each Level")
    print("=" * 100)
    print()

    hdr = f"{'m':>3}  {'#alive':>7}  {'max_idx':>9}  {'max(i/m)':>9}  surviving_n"
    print(hdr)
    print("-" * 90)

    for m in range(1, M_MAX + 1):
        r = results[m]
        cnt = r['known_zeroless_count']
        indices = r['known_zeroless_orbit_indices']
        surviving = r['known_zeroless_n']

        if indices:
            max_idx = max(indices)
            max_ratio = max_idx / m
        else:
            max_idx = None
            max_ratio = None

        if max_idx is not None:
            if cnt <= 15:
                nlist = str(surviving)
            else:
                nlist = f"[{surviving[0]},...,{surviving[-1]}]"
            line = f"{m:>3}  {cnt:>7}  {max_idx:>9}  {max_ratio:>9.3f}  {nlist}"
        else:
            line = f"{m:>3}  {cnt:>7}  {'---':>9}  {'---':>9}  (none)"
        print(line)

    # Drop-off table
    print()
    print("Drop-off: D(n) for each known zeroless n")
    print("-" * 60)
    for n in KNOWN_ZEROLESS:
        d = digit_count(n)
        print(f"  n={n:>3}  D(n)={d:>3}  orbit_idx_at_D(n)={n-d:>3}  "
              f"i/D(n)={((n-d)/d):>6.3f}")

    print()


def main():
    print(f"Experiment 15: Small-Survivor Census (m=1..{M_MAX})")
    print(f"Testing equidistribution and small-survivor counts")
    print(f"C thresholds: {C_VALUES}")
    print()

    t_start = time.time()

    results = {}
    for m in range(1, M_MAX + 1):
        print(f"Level m={m}: T={4 * 5**(m-1):,} ...", end=" ", flush=True)
        results[m] = enumerate_level(m)
        print(f"Z={results[m]['Z_m']:,}  "
              f"chi2={'PASS' if results[m]['equidist_pass'] else 'FAIL'}  "
              f"[{results[m]['elapsed']:.1f}s]")

    elapsed_total = time.time() - t_start
    print(f"\nAll levels complete. Total: {elapsed_total:.1f}s\n")

    part_A_summary(results)
    part_B_summary(results)
    part_C_summary(results)
    part_D_summary(results)

    # Final summary
    print("=" * 100)
    print("KEY FINDINGS")
    print("=" * 100)

    # Check if small survivors vanish
    for c in [2.5, 3.32]:
        counts = [results[m]['small_counts'][str(c)] for m in range(1, M_MAX + 1)]
        expected = [results[m]['small_expected'][str(c)] for m in range(1, M_MAX + 1)]
        print(f"\nC={c}: actual counts = {counts}")
        print(f"       expected     = {[round(e, 1) for e in expected]}")
        ratios = [results[m]['density_ratios'][str(c)] for m in range(1, M_MAX + 1)]
        ratios_clean = [r if r is not None else 0 for r in ratios]
        print(f"       density ratios = {[round(r, 3) for r in ratios_clean]}")

    # Equidistribution summary
    passes = sum(1 for m in range(1, M_MAX + 1) if results[m]['equidist_pass'])
    print(f"\nEquidistribution: {passes}/{M_MAX} levels pass chi2 test")

    print()

    # Save JSON
    save_data = {
        "_meta": {
            "M_MAX": M_MAX,
            "C_VALUES": C_VALUES,
            "KNOWN_ZEROLESS": KNOWN_ZEROLESS,
            "elapsed_total": round(elapsed_total, 1),
        },
        "per_level": {str(m): results[m] for m in range(1, M_MAX + 1)},
    }

    # Remove small_lists from JSON for large m (already excluded by m<=8 check)
    path = os.path.join(DATA_DIR, "exp15_results.json")
    with open(path, 'w') as f:
        json.dump(save_data, f, indent=2, default=str)
    print(f"Results saved to {path}")


if __name__ == '__main__':
    main()
