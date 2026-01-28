#!/usr/bin/env python3
"""
Experiment 8: Exponential Sum and Orbit-Restricted Analysis

Guided by the A-series (equidistribution/Fourier) and B-series (transfer matrix)
syntheses. Five sub-experiments:

A. Verify large-k examples from B-series GPT responses
B. Triple lifting analysis (extend B4's pair lifting lemma to triples)
C. Orbit-restricted survivor counting with decay rates
D. Fourier analysis of zeroless indicator on the orbit
E. Dominant character contribution and pointwise decomposition
"""

import sys
import os
import json
import time
import numpy as np
from collections import Counter

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)


# ============================================================
# Helpers
# ============================================================

def is_kdigit_zeroless(x, k):
    """Check if the last k digits of x (with leading zeros) are all nonzero."""
    for _ in range(k):
        if x % 10 == 0:
            return False
        x //= 10
    return True


# ============================================================
# Sub-experiment A: Verify large-k examples from B-series
# ============================================================

def verify_examples():
    print("=" * 70)
    print("SUB-EXPERIMENT A: Verify large-k examples from B-series")
    print("=" * 70)

    examples = [
        # (n, k, type, source)
        (849227, 10, "triple", "B1-A"),
        (38811471, 11, "triple", "B1-A"),
        (610351888025, 20, "pair", "B4-A"),
    ]

    results = []

    for n, k, etype, source in examples:
        mod = 10 ** k
        x = pow(2, n, mod)
        y = pow(2, n + 1, mod)
        x_zl = is_kdigit_zeroless(x, k)
        y_zl = is_kdigit_zeroless(y, k)

        x_str = str(x).zfill(k)
        y_str = str(y).zfill(k)

        if etype == "triple":
            z = pow(2, n + 2, mod)
            z_zl = is_kdigit_zeroless(z, k)
            z_str = str(z).zfill(k)
            ok = x_zl and y_zl and z_zl
            print(f"\n{source}: n={n}, k={k} ({etype})")
            print(f"  2^n     mod 10^{k} = {x_str}  zeroless: {x_zl}")
            print(f"  2^(n+1) mod 10^{k} = {y_str}  zeroless: {y_zl}")
            print(f"  2^(n+2) mod 10^{k} = {z_str}  zeroless: {z_zl}")
            print(f"  VERDICT: {'CONFIRMED' if ok else 'FAILED'}")
            results.append({'n': n, 'k': k, 'type': etype, 'confirmed': ok,
                            'x': x_str, 'y': y_str, 'z': z_str})
        else:
            ok = x_zl and y_zl
            print(f"\n{source}: n={n}, k={k} ({etype})")
            print(f"  2^n     mod 10^{k} = {x_str}  zeroless: {x_zl}")
            print(f"  2^(n+1) mod 10^{k} = {y_str}  zeroless: {y_zl}")
            print(f"  VERDICT: {'CONFIRMED' if ok else 'FAILED'}")
            results.append({'n': n, 'k': k, 'type': etype, 'confirmed': ok,
                            'x': x_str, 'y': y_str})

    return results


# ============================================================
# Sub-experiment B: Triple (and pair) lifting analysis
# ============================================================

def lifting_analysis(max_k=8):
    print("\n" + "=" * 70)
    print("SUB-EXPERIMENT B: Lifting analysis (pairs and triples)")
    print("=" * 70)

    results = []
    prev_pair_survivors = None
    prev_triple_survivors = None

    for k in range(1, max_k + 1):
        T_k = 4 * 5 ** (k - 1)
        mod = 10 ** k

        t0 = time.time()

        # Iterate through one period of the orbit
        # Start at n = k (so 2^n is divisible by 2^k)
        x = pow(2, k, mod)
        y = (2 * x) % mod
        z = (2 * y) % mod

        pair_survivors = set()
        triple_survivors = set()

        for n_offset in range(T_k):
            x_zl = is_kdigit_zeroless(x, k)
            if x_zl:
                y_zl = is_kdigit_zeroless(y, k)
                if y_zl:
                    pair_survivors.add(n_offset)
                    z_zl = is_kdigit_zeroless(z, k)
                    if z_zl:
                        triple_survivors.add(n_offset)

            # Advance
            x = y
            y = z
            z = (2 * z) % mod

        elapsed = time.time() - t0

        n_pairs = len(pair_survivors)
        n_triples = len(triple_survivors)
        pair_density = n_pairs / T_k
        triple_density = n_triples / T_k

        print(f"\nk={k}: T_k={T_k:,}")
        print(f"  Pair survivors: {n_pairs:,} (density {pair_density:.6f})")
        print(f"  Triple survivors: {n_triples:,} (density {triple_density:.6f})")
        print(f"  Time: {elapsed:.1f}s")

        # Lifting analysis from k-1 to k
        level_result = {
            'k': k, 'T_k': T_k,
            'pair_survivors': n_pairs, 'triple_survivors': n_triples,
            'pair_density': pair_density, 'triple_density': triple_density
        }

        if prev_pair_survivors is not None and k >= 2:
            T_prev = 4 * 5 ** (k - 2)

            # Pair lifts
            pair_lift_counts = []
            for n_off in prev_pair_survivors:
                count = 0
                for j in range(5):
                    lifted = (n_off + j * T_prev) % T_k
                    if lifted in pair_survivors:
                        count += 1
                pair_lift_counts.append(count)

            pair_lift_dist = Counter(pair_lift_counts)
            pair_avg = sum(pair_lift_counts) / len(pair_lift_counts) if pair_lift_counts else 0
            pair_branch = n_pairs / len(prev_pair_survivors) if prev_pair_survivors else 0

            print(f"  Pair lifts (k={k-1} -> k={k}):")
            print(f"    Distribution: {dict(sorted(pair_lift_dist.items()))}")
            print(f"    Average: {pair_avg:.4f}, Branching: {pair_branch:.4f}")

            level_result['pair_lift_dist'] = dict(sorted(pair_lift_dist.items()))
            level_result['pair_avg_lifts'] = pair_avg
            level_result['pair_branching'] = pair_branch

            # Triple lifts
            if prev_triple_survivors:
                triple_lift_counts = []
                for n_off in prev_triple_survivors:
                    count = 0
                    for j in range(5):
                        lifted = (n_off + j * T_prev) % T_k
                        if lifted in triple_survivors:
                            count += 1
                    triple_lift_counts.append(count)

                triple_lift_dist = Counter(triple_lift_counts)
                triple_avg = sum(triple_lift_counts) / len(triple_lift_counts) if triple_lift_counts else 0
                triple_branch = n_triples / len(prev_triple_survivors) if prev_triple_survivors else 0

                print(f"  Triple lifts (k={k-1} -> k={k}):")
                print(f"    Distribution: {dict(sorted(triple_lift_dist.items()))}")
                print(f"    Average: {triple_avg:.4f}, Branching: {triple_branch:.4f}")

                level_result['triple_lift_dist'] = dict(sorted(triple_lift_dist.items()))
                level_result['triple_avg_lifts'] = triple_avg
                level_result['triple_branching'] = triple_branch

        results.append(level_result)
        prev_pair_survivors = pair_survivors
        prev_triple_survivors = triple_survivors

    # Summary table
    print("\n\nLIFTING SUMMARY:")
    print(f"{'k':>3} {'T_k':>10} {'pairs':>8} {'triples':>8} "
          f"{'p_branch':>10} {'t_branch':>10} {'p_avg_lift':>10} {'t_avg_lift':>10}")
    print("-" * 80)
    for r in results:
        pb = r.get('pair_branching', '-')
        tb = r.get('triple_branching', '-')
        pa = r.get('pair_avg_lifts', '-')
        ta = r.get('triple_avg_lifts', '-')
        pb_s = f"{pb:.4f}" if isinstance(pb, float) else pb
        tb_s = f"{tb:.4f}" if isinstance(tb, float) else tb
        pa_s = f"{pa:.4f}" if isinstance(pa, float) else pa
        ta_s = f"{ta:.4f}" if isinstance(ta, float) else ta
        print(f"{r['k']:3d} {r['T_k']:10,} {r['pair_survivors']:8,} {r['triple_survivors']:8,} "
              f"{pb_s:>10} {tb_s:>10} {pa_s:>10} {ta_s:>10}")

    return results


# ============================================================
# Sub-experiment C: Orbit-restricted counting with decay rates
# ============================================================

def orbit_counting(max_k=10):
    print("\n" + "=" * 70)
    print("SUB-EXPERIMENT C: Orbit-restricted survivor counting")
    print("=" * 70)

    results = []

    for k in range(1, max_k + 1):
        T_k = 4 * 5 ** (k - 1)
        mod = 10 ** k

        t0 = time.time()

        x = pow(2, k, mod)
        y = (2 * x) % mod
        z = (2 * y) % mod

        singles = 0
        pairs = 0
        triples = 0

        for _ in range(T_k):
            x_zl = is_kdigit_zeroless(x, k)
            if x_zl:
                singles += 1
                y_zl = is_kdigit_zeroless(y, k)
                if y_zl:
                    pairs += 1
                    z_zl = is_kdigit_zeroless(z, k)
                    if z_zl:
                        triples += 1

            x = y
            y = z
            z = (2 * z) % mod

        elapsed = time.time() - t0

        s_frac = singles / T_k
        p_frac = pairs / T_k
        t_frac = triples / T_k

        results.append({
            'k': k, 'T_k': T_k,
            'singles': singles, 'pairs': pairs, 'triples': triples,
            's_frac': s_frac, 'p_frac': p_frac, 't_frac': t_frac,
            'time': elapsed
        })

    # Print main table
    print(f"\n{'k':>3} {'T_k':>12} {'singles':>10} {'pairs':>10} {'triples':>10} "
          f"{'s_frac':>10} {'p_frac':>10} {'t_frac':>10}")
    print("-" * 90)
    for r in results:
        print(f"{r['k']:3d} {r['T_k']:12,} {r['singles']:10,} {r['pairs']:10,} {r['triples']:10,} "
              f"{r['s_frac']:10.6f} {r['p_frac']:10.6f} {r['t_frac']:10.6f}")

    # Decay rates
    print(f"\nPer-step decay ratios:")
    print(f"{'k':>3} {'s_ratio':>10} {'p_ratio':>10} {'t_ratio':>10} "
          f"{'s_pred':>10} {'p_pred':>10} {'t_pred':>10}")
    print("-" * 70)
    for i in range(1, len(results)):
        r = results[i]
        rp = results[i - 1]
        s_ratio = r['s_frac'] / rp['s_frac'] if rp['s_frac'] > 0 else 0
        p_ratio = r['p_frac'] / rp['p_frac'] if rp['p_frac'] > 0 else 0
        t_ratio = r['t_frac'] / rp['t_frac'] if rp['t_frac'] > 0 else 0
        print(f"{r['k']:3d} {s_ratio:10.6f} {p_ratio:10.6f} {t_ratio:10.6f} "
              f"{'0.900000':>10} {8.531/9:10.6f} {8.035/9:10.6f}")

    # Correlation analysis
    print(f"\nCorrelation ratios:")
    print(f"{'k':>3} {'p/s^2':>12} {'t/s^3':>12} {'t/(s*p)':>12}")
    print("-" * 45)
    for r in results:
        s = r['s_frac']
        p = r['p_frac']
        t = r['t_frac']
        ps2 = p / s**2 if s > 0 else 0
        ts3 = t / s**3 if s > 0 else 0
        tsp = t / (s * p) if s > 0 and p > 0 else 0
        print(f"{r['k']:3d} {ps2:12.6f} {ts3:12.6f} {tsp:12.6f}")

    return results


# ============================================================
# Sub-experiment D: Fourier analysis of zeroless indicator
# ============================================================

def fourier_analysis(max_k=7):
    print("\n" + "=" * 70)
    print("SUB-EXPERIMENT D: Fourier analysis of zeroless indicator")
    print("=" * 70)

    results = []

    for k in range(1, max_k + 1):
        T_k = 4 * 5 ** (k - 1)
        mod = 10 ** k

        t0 = time.time()

        # Build f(n) = 1_{zeroless}(2^n mod 10^k) for one period
        f = np.zeros(T_k, dtype=np.float64)
        x = pow(2, k, mod)
        for n_offset in range(T_k):
            if is_kdigit_zeroless(x, k):
                f[n_offset] = 1.0
            x = (2 * x) % mod

        # DFT (normalized)
        F = np.fft.fft(f) / T_k
        density = np.real(F[0])

        # Magnitudes of non-DC terms
        mags = np.abs(F)
        mags_noDC = mags.copy()
        mags_noDC[0] = 0

        # Top 5 non-trivial coefficients
        top_idx = np.argsort(mags_noDC)[::-1][:5]

        elapsed = time.time() - t0

        print(f"\nk={k}: T_k={T_k:,}, density={density:.8f}, "
              f"expected (0.9^k)={0.9**k:.8f}, time={elapsed:.1f}s")

        # Relative Fourier coefficients
        print(f"  Top 5 non-trivial |hat(f)(j)| / hat(f)(0):")
        top_data = []
        for rank, j in enumerate(top_idx):
            rel = mags[j] / density if density > 0 else 0
            # 5-adic valuation of j
            v5 = 0
            jj = int(j)
            while jj > 0 and jj % 5 == 0:
                v5 += 1
                jj //= 5
            print(f"    #{rank+1}: j={j:8d} (v5={v5}), |hat(f)|={mags[j]:.8f}, "
                  f"relative={rel:.6f}")
            top_data.append({'j': int(j), 'v5': v5,
                             'magnitude': float(mags[j]), 'relative': float(rel)})

        # Check A3-A's prediction: dominant at j = 5^{k-2}
        if k >= 2:
            j_pred = 5 ** (k - 2)
            j_conj = T_k - j_pred
            rel_pred = mags[j_pred] / density if density > 0 else 0
            print(f"  A3-A prediction check: j=5^(k-2)={j_pred}")
            print(f"    |hat(f)({j_pred})|={mags[j_pred]:.8f}, relative={rel_pred:.6f}")
            if j_conj != j_pred and j_conj < T_k:
                rel_conj = mags[j_conj] / density if density > 0 else 0
                print(f"    Conjugate j={j_conj}: |hat(f)|={mags[j_conj]:.8f}, "
                      f"relative={rel_conj:.6f}")

        results.append({
            'k': k, 'T_k': T_k,
            'density': float(density),
            'expected_density': 0.9 ** k,
            'top_coefficients': top_data
        })

    # Density ratio analysis
    print("\n\nDensity ratio analysis (observed density / expected (0.9)^k):")
    for r in results:
        ratio = r['density'] / r['expected_density']
        print(f"  k={r['k']}: observed={r['density']:.8f}, "
              f"expected={r['expected_density']:.8f}, ratio={ratio:.6f}")

    # Cross-level relative bias growth
    print("\nRelative bias of dominant character (j=5^{k-2}) vs k:")
    for r in results:
        if r['k'] >= 2 and r['top_coefficients']:
            j_pred = 5 ** (r['k'] - 2)
            for tc in r['top_coefficients']:
                if tc['j'] == j_pred:
                    print(f"  k={r['k']}: relative = {tc['relative']:.6f}")
                    break

    return results


# ============================================================
# Sub-experiment E: Dominant character decomposition
# ============================================================

def dominant_character_analysis(max_k=6):
    print("\n" + "=" * 70)
    print("SUB-EXPERIMENT E: Dominant character contribution")
    print("=" * 70)

    for k in range(2, max_k + 1):
        T_k = 4 * 5 ** (k - 1)
        mod = 10 ** k

        # Build f(n)
        f = np.zeros(T_k, dtype=np.float64)
        x = pow(2, k, mod)
        for n_offset in range(T_k):
            if is_kdigit_zeroless(x, k):
                f[n_offset] = 1.0
            x = (2 * x) % mod

        # DFT
        F = np.fft.fft(f) / T_k
        density = np.real(F[0])

        # Variance decomposition (Parseval)
        total_var = np.sum(np.abs(F[1:]) ** 2)

        # Dominant character at j = 5^{k-2} and its conjugate
        j_dom = 5 ** (k - 2)
        j_conj = T_k - j_dom
        dom_var = np.abs(F[j_dom]) ** 2
        if j_conj != j_dom:
            dom_var += np.abs(F[j_conj]) ** 2

        # Low-conductor characters: those with 5^{k-2} | j
        divisor = 5 ** max(0, k - 2)
        low_var = 0.0
        low_count = 0
        for j in range(1, T_k):
            if j % divisor == 0:
                low_var += np.abs(F[j]) ** 2
                low_count += 1

        # Characters at each conductor level
        print(f"\nk={k}: T_k={T_k:,}")
        print(f"  Density: {density:.8f}")
        print(f"  Total non-DC variance: {total_var:.10f}")
        print(f"  Dominant pair (j={j_dom},j={j_conj}): "
              f"var={dom_var:.10f}, share={dom_var/total_var*100:.2f}%")
        print(f"  Low-conductor chars (5^{max(0,k-2)} | j): "
              f"{low_count} chars, var={low_var:.10f}, share={low_var/total_var*100:.2f}%")

        # Variance by 5-adic valuation of j
        print(f"  Variance by v_5(j):")
        for v in range(k + 1):
            v_var = 0.0
            v_count = 0
            for j in range(1, T_k):
                jj = j
                vj = 0
                while jj % 5 == 0:
                    vj += 1
                    jj //= 5
                if vj == v:
                    v_var += np.abs(F[j]) ** 2
                    v_count += 1
            if v_count > 0:
                print(f"    v_5={v}: {v_count:6d} chars, var={v_var:.10f}, "
                      f"share={v_var/total_var*100:.2f}%")

        # Pointwise decomposition near n=86-87 (for small k)
        if k <= 4:
            print(f"  Pointwise decomposition (n near 86):")
            for n_test in [83, 84, 85, 86, 87, 88]:
                n_mod = n_test % T_k
                # Actual value
                x_test = pow(2, n_test, mod)
                actual = 1.0 if is_kdigit_zeroless(x_test, k) else 0.0
                # DC contribution
                dc = density
                # Dominant character contribution
                phase_dom = 2 * np.pi * j_dom * n_mod / T_k
                phase_conj = 2 * np.pi * j_conj * n_mod / T_k
                dom_contrib = np.real(F[j_dom] * np.exp(1j * phase_dom))
                if j_conj != j_dom:
                    dom_contrib += np.real(F[j_conj] * np.exp(1j * phase_conj))
                # Full reconstruction
                phases = 2 * np.pi * np.arange(T_k) * n_mod / T_k
                full_recon = np.real(np.sum(F * np.exp(1j * phases)))

                print(f"    n={n_test}: actual={actual:.0f}, DC={dc:.4f}, "
                      f"dom_char={dom_contrib:+.4f}, "
                      f"full={full_recon:.4f}")


# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    print("EXPERIMENT 8: EXPONENTIAL SUM AND ORBIT-RESTRICTED ANALYSIS")
    print("Guided by A-series + B-series syntheses")
    print("=" * 70)
    print()

    all_results = {}

    # A: Verify examples
    all_results['verify'] = verify_examples()

    # B: Lifting analysis (pairs and triples), k up to 8
    all_results['lifting'] = lifting_analysis(max_k=8)

    # C: Orbit-restricted counting, k up to 10
    all_results['orbit'] = orbit_counting(max_k=10)

    # D: Fourier analysis, k up to 7
    all_results['fourier'] = fourier_analysis(max_k=7)

    # E: Dominant character analysis, k up to 6
    dominant_character_analysis(max_k=6)

    # Save
    with open(os.path.join(DATA_DIR, "exp8_results.json"), "w") as fp:
        json.dump(all_results, fp, indent=2, default=str)

    print("\n" + "=" * 70)
    print("Results saved to data/exp8_results.json")
    print("=" * 70)
