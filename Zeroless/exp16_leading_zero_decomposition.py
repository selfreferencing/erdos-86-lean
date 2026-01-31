#!/usr/bin/env python3
"""
Experiment 16: Leading-Zero Decomposition of Small-Index Depletion

Explains WHY small orbit indices are depleted of survivors (found in Exp 15).

The mechanism: when orbit index i is small, exponent n = m+i gives 2^n < 10^m,
so x_i = 2^n (no modular reduction). Written as m digits, this has leading zeros.
The survivor test x >= 10^{m-1} kills it automatically.

Three zones:
  i < i_low:                2^n has < m digits. Category 1 (leading-zero kill).
  i_low <= i <= i_high:     2^n has exactly m digits. Survivor iff zeroless power.
  i > i_high:               2^n > 10^m. Modular reduction. "Random" survivor rate.

Parts:
  A - Category decomposition (Cat 1/2/3) for small indices
  B - Position-resolved survivor density (sliding windows)
  C - First-survivor index at each level
  D - Transition sharpness near i_low
  E - Depletion budget: how much is explained by leading zeros
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
I_SCAN = 500  # detailed per-index scan up to this many indices
LOG10_2 = math.log10(2)

KNOWN_ZEROLESS = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19,
    24, 25, 27, 28, 31, 32, 33, 34, 35, 36, 37, 39, 49,
    51, 67, 72, 76, 77, 81, 86
]


def digit_count(n):
    """Number of digits of 2^n in base 10."""
    if n == 0:
        return 1
    return int(n * LOG10_2) + 1


def compute_critical_indices(m):
    """Compute i_low and i_high for level m."""
    # i_low: first orbit index where D(m+i) >= m, i.e., 2^{m+i} >= 10^{m-1}
    # n_low = ceil((m-1)/log10(2)), so i_low = n_low - m
    if m == 1:
        i_low = 0  # D(1) = 1 = m, so index 0 already has enough digits
    else:
        n_low = math.ceil((m - 1) / LOG10_2)
        i_low = n_low - m

    # i_high: last orbit index where D(m+i) = m, i.e., 2^{m+i} < 10^m
    # n_high = ceil(m/log10(2)) - 1, so i_high = n_high - m
    n_high = math.ceil(m / LOG10_2) - 1
    i_high = n_high - m

    return max(i_low, 0), max(i_high, 0)


def enumerate_level(m):
    """Single-pass enumeration collecting data for Parts A-E."""
    mod = 10 ** m
    T = 4 * 5 ** (m - 1)
    min_val = mod // 10

    i_low, i_high = compute_critical_indices(m)
    i_scan = min(I_SCAN, T)

    # Part A: category counts in zones
    cat_pre = [0, 0, 0]   # Cat 1,2,3 for i in [0, i_low)
    cat_mid = [0, 0, 0]   # Cat 1,2,3 for i in [i_low, i_high]
    cat_post = [0, 0, 0]  # Cat 1,2,3 for i in (i_high, i_scan)

    # Per-index categories for m <= 8
    categories = [] if m <= 8 else None

    # Part B: windowed density
    W_B = max(m, 10)
    num_windows = min(i_scan // W_B, 50)
    window_counts = [0] * max(num_windows, 1)

    # Part C: first survivor
    i_first = None

    # Part D: narrow windows around i_low
    W_D = max(3, m // 2)
    # Cover i_low - 5*W_D to i_low + 10*W_D
    d_start = max(0, i_low - 5 * W_D)
    d_end = min(i_scan, i_low + 10 * W_D)
    d_num = max(1, (d_end - d_start) // W_D)
    d_window_counts = [0] * d_num
    d_window_totals = [0] * d_num

    # Full orbit scan
    Z_m = 0
    x = pow(2, m, mod)
    t0 = time.time()

    for i in range(T):
        is_surv = x >= min_val and '0' not in str(x)
        if is_surv:
            Z_m += 1

        if i < i_scan:
            # Classify
            if x < min_val:
                cat_val = 1
            elif '0' in str(x):
                cat_val = 2
            else:
                cat_val = 3

            # Zone assignment
            if i < i_low:
                cat_pre[cat_val - 1] += 1
            elif i <= i_high:
                cat_mid[cat_val - 1] += 1
            else:
                cat_post[cat_val - 1] += 1

            if categories is not None:
                categories.append(cat_val)

            # Part B: window
            w_idx = i // W_B
            if w_idx < num_windows and cat_val == 3:
                window_counts[w_idx] += 1

            # Part C: first survivor
            if i_first is None and cat_val == 3:
                i_first = i

            # Part D: narrow window
            if d_start <= i < d_end:
                d_idx = (i - d_start) // W_D
                if d_idx < d_num:
                    d_window_totals[d_idx] += 1
                    if cat_val == 3:
                        d_window_counts[d_idx] += 1

        x = (x * 2) % mod

        if m >= 10 and i > 0 and i % (T // 5) == 0:
            el = time.time() - t0
            print(f"  [m={m}: {100*i//T}%, {el:.1f}s]",
                  file=sys.stderr, flush=True)

    elapsed = time.time() - t0
    density_global = Z_m / T

    # Part B: compute densities
    windows_B = []
    pre_crit_densities = []
    post_crit_densities = []
    for w in range(num_windows):
        w_start = w * W_B
        w_end = (w + 1) * W_B
        d = window_counts[w] / W_B
        windows_B.append((w_start, w_end, round(d, 4)))
        if w_end <= i_low:
            pre_crit_densities.append(d)
        elif w_start > i_high + W_B:
            post_crit_densities.append(d)

    mean_pre = sum(pre_crit_densities) / len(pre_crit_densities) if pre_crit_densities else 0.0
    mean_post = sum(post_crit_densities) / len(post_crit_densities) if post_crit_densities else 0.0
    expected_post = 0.9 ** m

    # Part C
    if i_first is not None:
        n_first = m + i_first
        D_first = digit_count(n_first)
    else:
        n_first = None
        D_first = None

    # Part D: transition windows
    transition_windows = []
    for d_idx in range(d_num):
        w_start = d_start + d_idx * W_D
        w_end = w_start + W_D
        total = d_window_totals[d_idx]
        surv = d_window_counts[d_idx]
        d_val = surv / total if total > 0 else 0.0
        transition_windows.append({
            "start": w_start,
            "end": w_end,
            "survivors": surv,
            "total": total,
            "density": round(d_val, 4)
        })

    # Part E: depletion budget
    # Pre-critical zone: [0, i_low)
    total_pre = sum(cat_pre)
    non_surv_pre = cat_pre[0] + cat_pre[1]
    frac_cat1_pre = cat_pre[0] / non_surv_pre if non_surv_pre > 0 else 0.0
    frac_cat2_pre = cat_pre[1] / non_surv_pre if non_surv_pre > 0 else 0.0

    equidist_pred = density_global * i_low if i_low > 0 else 0.0
    actual_surv_pre = cat_pre[2]
    excess = equidist_pred - actual_surv_pre

    # How much depletion is explained by leading zeros?
    # Under equidistribution, Cat 1 rate would be ~1/10 (random m-digit numbers
    # have ~10% chance of being < 10^{m-1} after mod reduction).
    # Actual Cat 1 rate in pre-critical: cat_pre[0] / i_low
    # Baseline Cat 1 rate: ~1/10
    # Excess Cat 1 kills: cat_pre[0] - i_low/10
    baseline_cat1 = i_low / 10.0 if i_low > 0 else 0.0
    excess_cat1_kills = cat_pre[0] - baseline_cat1
    lz_explanation_pct = (excess_cat1_kills / excess * 100) if excess > 0 else 0.0

    result = {
        "T_m": T,
        "Z_m": Z_m,
        "density_global": round(density_global, 6),
        "i_low": i_low,
        "i_high": i_high,
        "i_scanned": i_scan,

        "part_A": {
            "cat_pre_crit": cat_pre,
            "cat_mid": cat_mid,
            "cat_post": cat_post,
            "total_pre": total_pre,
            "total_mid": sum(cat_mid),
            "total_post": sum(cat_post),
            "fraction_cat1_pre": round(frac_cat1_pre, 4),
            "fraction_cat2_pre": round(frac_cat2_pre, 4),
        },

        "part_B": {
            "window_width": W_B,
            "num_windows": num_windows,
            "mean_pre_crit": round(mean_pre, 6),
            "mean_post_crit": round(mean_post, 6),
            "expected_post": round(expected_post, 6),
            "windows": windows_B[:30],  # store first 30
        },

        "part_C": {
            "i_first": i_first,
            "n_first": n_first,
            "D_n_first": D_first,
        },

        "part_D": {
            "narrow_width": W_D,
            "d_start": d_start,
            "d_end": d_end,
            "transition_windows": transition_windows,
        },

        "part_E": {
            "equidist_predicted": round(equidist_pred, 2),
            "actual_survivors_pre": actual_surv_pre,
            "excess_depletion": round(excess, 2),
            "fraction_cat1": round(frac_cat1_pre, 4),
            "fraction_cat2": round(frac_cat2_pre, 4),
            "baseline_cat1": round(baseline_cat1, 2),
            "excess_cat1_kills": round(excess_cat1_kills, 2),
            "leading_zero_explanation_pct": round(lz_explanation_pct, 1),
        },

        "elapsed": round(elapsed, 3),
    }

    if categories is not None:
        result["categories_detail"] = categories

    return result


def part_A_summary(results):
    print("=" * 100)
    print("PART A: Leading-Zero Category Decomposition")
    print("  Cat 1 = too small (x < 10^{m-1}), Cat 2 = right size but has zero, Cat 3 = survivor")
    print("=" * 100)
    print()

    print("Pre-critical zone [0, i_low):")
    hdr = f"{'m':>3}  {'i_low':>6}  {'total':>6}  {'Cat1':>6}  {'Cat2':>6}  {'Cat3':>6}  {'%Cat1':>7}"
    print(hdr)
    print("-" * len(hdr))
    for m in range(1, M_MAX + 1):
        r = results[m]
        a = r["part_A"]
        line = (f"{m:>3}  {r['i_low']:>6}  {a['total_pre']:>6}  "
                f"{a['cat_pre_crit'][0]:>6}  {a['cat_pre_crit'][1]:>6}  "
                f"{a['cat_pre_crit'][2]:>6}  {a['fraction_cat1_pre']*100:>6.1f}%")
        print(line)

    print()
    print("Transition zone [i_low, i_high]:")
    hdr2 = f"{'m':>3}  {'i_low':>6}  {'i_high':>6}  {'width':>6}  {'Cat1':>6}  {'Cat2':>6}  {'Cat3':>6}"
    print(hdr2)
    print("-" * len(hdr2))
    for m in range(1, M_MAX + 1):
        r = results[m]
        a = r["part_A"]
        width = r["i_high"] - r["i_low"] + 1
        line = (f"{m:>3}  {r['i_low']:>6}  {r['i_high']:>6}  {width:>6}  "
                f"{a['cat_mid'][0]:>6}  {a['cat_mid'][1]:>6}  {a['cat_mid'][2]:>6}")
        print(line)

    print()
    print("Post-critical zone (i_high, 500]:")
    hdr3 = f"{'m':>3}  {'i_high':>6}  {'total':>6}  {'Cat1':>6}  {'Cat2':>6}  {'Cat3':>6}  {'surv%':>7}  {'(9/10)^m':>8}"
    print(hdr3)
    print("-" * len(hdr3))
    for m in range(1, M_MAX + 1):
        r = results[m]
        a = r["part_A"]
        total = a["total_post"]
        surv_pct = a["cat_post"][2] / total * 100 if total > 0 else 0.0
        exp_pct = 0.9 ** m * 100
        line = (f"{m:>3}  {r['i_high']:>6}  {total:>6}  "
                f"{a['cat_post'][0]:>6}  {a['cat_post'][1]:>6}  {a['cat_post'][2]:>6}  "
                f"{surv_pct:>6.1f}%  {exp_pct:>7.1f}%")
        print(line)

    print()


def part_B_summary(results):
    print("=" * 100)
    print("PART B: Position-Resolved Survivor Density (sliding windows)")
    print("=" * 100)
    print()

    hdr = f"{'m':>3}  {'W':>4}  {'pre-crit':>10}  {'post-crit':>10}  {'(9/10)^m':>10}  {'ratio':>7}"
    print(hdr)
    print("-" * len(hdr))
    for m in range(1, M_MAX + 1):
        r = results[m]
        b = r["part_B"]
        ratio = b["mean_post_crit"] / b["expected_post"] if b["expected_post"] > 0 else 0.0
        line = (f"{m:>3}  {b['window_width']:>4}  {b['mean_pre_crit']:>10.6f}  "
                f"{b['mean_post_crit']:>10.6f}  {b['expected_post']:>10.6f}  "
                f"{ratio:>7.3f}")
        print(line)

    # Show first few windows for selected levels
    for m in [4, 8, 12]:
        if m > M_MAX:
            continue
        r = results[m]
        b = r["part_B"]
        print(f"\n  m={m} windows (W={b['window_width']}, i_low={r['i_low']}, i_high={r['i_high']}):")
        for w_start, w_end, d in b["windows"][:20]:
            marker = ""
            if w_end <= r["i_low"]:
                marker = " <-- pre-crit"
            elif w_start <= r["i_high"] <= w_end:
                marker = " <-- TRANSITION"
            print(f"    [{w_start:>4}, {w_end:>4}): density={d:.4f}{marker}")

    print()


def part_C_summary(results):
    print("=" * 100)
    print("PART C: First-Survivor Index")
    print("=" * 100)
    print()

    hdr = f"{'m':>3}  {'i_low':>6}  {'i_first':>7}  {'n_first':>7}  {'D(n)':>5}  {'at_boundary?':>13}"
    print(hdr)
    print("-" * len(hdr))
    for m in range(1, M_MAX + 1):
        r = results[m]
        c = r["part_C"]
        if c["i_first"] is not None:
            at_bound = "YES" if c["i_first"] >= r["i_low"] else "BEFORE"
            line = (f"{m:>3}  {r['i_low']:>6}  {c['i_first']:>7}  "
                    f"{c['n_first']:>7}  {c['D_n_first']:>5}  {at_bound:>13}")
        else:
            line = f"{m:>3}  {r['i_low']:>6}  {'none':>7}  {'---':>7}  {'---':>5}  {'N/A':>13}"
        print(line)

    print()


def part_D_summary(results):
    print("=" * 100)
    print("PART D: Transition Sharpness Near i_low")
    print("=" * 100)
    print()

    for m in [3, 5, 8, 10, 12]:
        if m > M_MAX:
            continue
        r = results[m]
        d = r["part_D"]
        print(f"  m={m} (i_low={r['i_low']}, i_high={r['i_high']}, "
              f"narrow_W={d['narrow_width']}):")
        for tw in d["transition_windows"]:
            marker = ""
            if tw["end"] <= r["i_low"]:
                marker = "  pre"
            elif tw["start"] >= r["i_low"] and tw["end"] <= r["i_high"] + 1:
                marker = "  MID"
            elif tw["start"] > r["i_high"]:
                marker = "  post"
            print(f"    [{tw['start']:>4}, {tw['end']:>4}): "
                  f"{tw['survivors']:>2}/{tw['total']:>2} = {tw['density']:.4f}{marker}")
        print()


def part_E_summary(results):
    print("=" * 100)
    print("PART E: Depletion Budget")
    print("=" * 100)
    print()

    hdr = (f"{'m':>3}  {'i_low':>5}  {'equidist':>8}  {'actual':>6}  "
           f"{'excess':>7}  {'%Cat1':>6}  {'LZ_expl%':>8}")
    print(hdr)
    print("-" * len(hdr))
    for m in range(1, M_MAX + 1):
        r = results[m]
        e = r["part_E"]
        line = (f"{m:>3}  {r['i_low']:>5}  {e['equidist_predicted']:>8.1f}  "
                f"{e['actual_survivors_pre']:>6}  {e['excess_depletion']:>7.1f}  "
                f"{e['fraction_cat1']*100:>5.1f}%  {e['leading_zero_explanation_pct']:>7.1f}%")
        print(line)

    print()


def main():
    print(f"Experiment 16: Leading-Zero Decomposition (m=1..{M_MAX})")
    print(f"Testing: why are small orbit indices depleted of survivors?")
    print()

    t_start = time.time()

    results = {}
    for m in range(1, M_MAX + 1):
        i_low, i_high = compute_critical_indices(m)
        print(f"Level m={m}: T={4*5**(m-1):,}  i_low={i_low}  i_high={i_high} ...",
              end=" ", flush=True)
        results[m] = enumerate_level(m)
        r = results[m]
        print(f"Z={r['Z_m']:,}  first_surv={r['part_C']['i_first']}  "
              f"LZ%={r['part_E']['fraction_cat1']*100:.0f}%  [{r['elapsed']:.1f}s]")

    elapsed_total = time.time() - t_start
    print(f"\nAll levels complete. Total: {elapsed_total:.1f}s\n")

    part_A_summary(results)
    part_B_summary(results)
    part_C_summary(results)
    part_D_summary(results)
    part_E_summary(results)

    # Key finding
    print("=" * 100)
    print("KEY FINDING")
    print("=" * 100)
    print()
    print("The leading-zero mechanism:")
    print("  For orbit index i < i_low(m), exponent n = m+i gives 2^n < 10^{m-1},")
    print("  so x_i has fewer than m digits. Written as m digits, leading zeros appear.")
    print("  The survivor test x >= 10^{m-1} kills these automatically.")
    print()
    print("Fraction of pre-critical non-survivors that are Category 1 (leading-zero kill):")
    for m in range(1, M_MAX + 1):
        r = results[m]
        pct = r["part_E"]["fraction_cat1"] * 100
        print(f"  m={m:>2}: {pct:>6.1f}%")
    print()

    # Save
    save_data = {
        "_meta": {
            "M_MAX": M_MAX,
            "I_SCAN": I_SCAN,
            "LOG10_2": LOG10_2,
            "elapsed_total": round(elapsed_total, 1),
        },
        "per_level": {str(m): results[m] for m in range(1, M_MAX + 1)},
    }

    path = os.path.join(DATA_DIR, "exp16_results.json")
    with open(path, 'w') as f:
        json.dump(save_data, f, indent=2, default=str)
    print(f"Results saved to {path}")


if __name__ == '__main__':
    main()
