#!/usr/bin/env python3
"""
Experiment 20b: Lacunary Bound on the Error Term

KEY INSIGHT FROM EXP 20:
The digit indicators g_j have perfectly lacunary Fourier support:
- g_j has nonzero Fourier coefficients only at multiples of stride_j = 5^{m-1-j}
- So the Fourier support of g_j consists of T_j = 4*5^j frequencies

Since f_m = g_1 * ... * g_m and hat(f_m) = conv(hat(g_1), ..., hat(g_m)),
the Fourier support of hat(f_m) is the "sumset" of the individual supports.

For classical Riesz products with truly lacunary frequencies (ratio >= 3),
the support sets DON'T overlap: each product of terms contributes to a
unique frequency, giving an explicit formula for each hat(f_m)(r).

OUR SITUATION: The supports ARE nested (stride_j | stride_{j-1}), not lacunary.
So the classical Riesz product formula doesn't apply directly.

BUT: the key observation is that the ERROR TERM involves D_L(j), the
geometric sum. For the Riesz product bound, we need:

error = sum_r hat(f_m)(r) * D_L(r)

The hat(f_m)(r) comes from the convolution. For frequencies r with
high 5-adic valuation v_5(r), fewer digit conditions contribute
(digits 1 through m - v_5(r) "see" frequency r, but digits m-v_5(r)+1
through m don't). So the coefficient hat(f_m)(r) for high v_5(r) comes
from fewer digit conditions and is larger.

THIS EXPERIMENT:
1. Decompose the error by 5-adic valuation of the frequency
2. For each v_5 band, compute the partial error sum
3. Test whether the partial sums cancel across bands
4. Compute the "effective number of digits" contributing to each band
5. Test the KEY QUESTION: does the error at each v_5 level decay
   as more digit conditions are imposed?
"""

import sys
import os
import time
import math
import numpy as np

sys.set_int_max_str_digits(100000)

M_MAX = 9
C_CRIT = 1.0 / math.log10(2)


def build_orbit_and_digits(m):
    """Build orbit elements and per-digit indicators for level m."""
    T = 4 * 5 ** (m - 1)
    mod = 10 ** m

    g = [np.zeros(T, dtype=np.float64) for _ in range(m)]
    x = pow(2, m, mod)
    for i in range(T):
        val = x
        for j in range(m):
            if val % 10 != 0:
                g[j][i] = 1.0
            val //= 10
        x = (x * 2) % mod

    f = np.ones(T, dtype=np.float64)
    for j in range(m):
        f *= g[j]

    return g, f, T


def part_A_error_by_v5_band(max_m=9):
    """Decompose the Fourier error by 5-adic valuation of frequency."""
    print("=" * 100)
    print("PART A: Error Decomposition by 5-adic Valuation of Frequency")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)
        Z = int(np.sum(f))
        rho = Z / T

        L = min(int(math.ceil(C_CRIT * m)), T)

        # Exact count and error
        exact = int(np.sum(f[:L]))
        main = L * rho
        actual_error = exact - main

        # DFT
        F = np.fft.fft(f) / T

        # Geometric sums D_L(j) for j = 1, ..., T-1
        j_arr = np.arange(1, T)
        theta = 2 * np.pi * j_arr / T
        omega = np.exp(1j * theta)
        omega_L = np.exp(1j * theta * L)
        denom = 1.0 - omega
        safe = np.abs(denom) > 1e-15
        DL = np.where(safe, (1.0 - omega_L) / np.where(safe, denom, 1.0), L)

        # Products F(j) * D_L(j)
        products = F[1:] * DL

        # Classify by v_5
        max_v5 = m - 1
        band_error_signed = {v: 0.0 for v in range(max_v5 + 1)}
        band_error_unsigned = {v: 0.0 for v in range(max_v5 + 1)}
        band_count = {v: 0 for v in range(max_v5 + 1)}

        for idx in range(len(j_arr)):
            j = j_arr[idx]
            v5 = 0
            jj = int(j)
            while jj > 0 and jj % 5 == 0:
                v5 += 1
                jj //= 5
            v5 = min(v5, max_v5)

            band_error_signed[v5] += float(np.real(products[idx]))
            band_error_unsigned[v5] += float(np.abs(products[idx]))
            band_count[v5] += 1

        # Print
        print(f"\nm={m}: L={L}, T={T:,}, exact={exact}, main={main:.4f}, "
              f"actual_error={actual_error:.4f}")
        print(f"  {'v_5':>4}  {'count':>8}  {'signed_error':>14}  "
              f"{'unsigned_err':>14}  {'cancellation':>12}  {'#digits_see':>12}")
        print("  " + "-" * 75)

        total_signed = 0.0
        total_unsigned = 0.0
        for v in range(max_v5 + 1):
            # Number of digit conditions that "see" this frequency band:
            # Digit j has stride 5^{m-1-j}. Frequency r has v_5(r) = v.
            # Digit j sees frequency r iff stride_j | r, i.e., 5^{m-1-j} | r.
            # This requires m-1-j <= v, i.e., j >= m-1-v.
            # But digit indices are j=0,...,m-1. So digits j=m-1-v,...,m-1 see it.
            # That's v+1 digits. Wait, let me recheck.
            # g_j has stride 5^{m-1-j}. hat(g_j)(r) is nonzero only if
            # stride_j | r. stride_j = 5^{m-1-j}. If v_5(r) = v, then
            # 5^{m-1-j} | r iff m-1-j <= v, i.e., j >= m-1-v.
            # Digits j = 0, ..., m-1. So j >= m-1-v means digits m-1-v through m-1.
            # Count: v+1 digits.
            # BUT: digit j=0 (ones digit) has stride 5^{m-1}, which is very large.
            # So only frequencies with v_5(r) >= m-1 are seen by digit 1.
            n_digits_see = v + 1

            cancel_ratio = (abs(band_error_signed[v]) / band_error_unsigned[v]
                           if band_error_unsigned[v] > 0 else 0)
            total_signed += band_error_signed[v]
            total_unsigned += band_error_unsigned[v]

            print(f"  {v:>4}  {band_count[v]:>8}  {band_error_signed[v]:>14.6f}  "
                  f"{band_error_unsigned[v]:>14.6f}  {cancel_ratio:>12.6f}  "
                  f"{n_digits_see:>12}")

        cancel_total = abs(total_signed) / total_unsigned if total_unsigned > 0 else 0
        print(f"  {'ALL':>4}  {sum(band_count.values()):>8}  {total_signed:>14.6f}  "
              f"{total_unsigned:>14.6f}  {cancel_total:>12.6f}")
        print(f"  Check: Fourier error = {total_signed:.6f} vs actual = {actual_error:.6f}")


def part_B_sequential_error_by_digit(max_m=9):
    """How does the error change as each digit condition is imposed?

    Start with h_0 = 1 (all indices). Impose conditions one by one:
    h_k = h_{k-1} * g_k.

    For each k, compute |{i in [0,L) : h_k(i) = 1}| - L * mean(h_k).
    This is the error at the k-th stage of sieving.

    KEY QUESTION: does the error SHRINK as more conditions are imposed?
    If so, the "sieving effect" produces equidistribution.
    """
    print("\n" + "=" * 100)
    print("PART B: Error Evolution During Sequential Sieving")
    print("  How does |S_k ∩ [0,L)| - L*rho_k change as k = 1,2,...,m?")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        L = min(int(math.ceil(C_CRIT * m)), T)

        print(f"\nm={m}: L={L}, T={T:,}")
        print(f"  {'k':>3}  {'count_L':>8}  {'count_T':>10}  {'rho_k':>10}  "
              f"{'main':>8}  {'error':>8}  {'error/main':>10}  {'error/sqrt':>10}")
        print("  " + "-" * 80)

        h = np.ones(T, dtype=np.float64)

        for k in range(m):
            h = h * g[k]
            count_L = int(np.sum(h[:L]))
            count_T = int(np.sum(h))
            rho_k = count_T / T
            main = L * rho_k
            error = count_L - main
            error_ratio = error / main if main > 0 else float('inf')
            error_sqrt = error / math.sqrt(main) if main > 0 else 0

            print(f"  {k+1:>3}  {count_L:>8}  {count_T:>10,}  {rho_k:>10.6f}  "
                  f"{main:>8.4f}  {error:>8.4f}  {error_ratio:>10.6f}  {error_sqrt:>10.4f}")


def part_C_which_digit_kills(max_m=9):
    """For elements in [0, L), which digit condition eliminates them?

    Track: at each step k, how many elements in [0,L) are killed
    (were alive after k-1 conditions but die at condition k)?

    Compare to the expected kill rate: 1/10 of survivors.
    This tells us whether any digit condition is disproportionately
    effective or ineffective for small indices.
    """
    print("\n" + "=" * 100)
    print("PART C: Which Digit Kills Small Indices?")
    print("  For [0, L) elements, track kills at each digit level")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        L = min(int(math.ceil(C_CRIT * m)), T)

        print(f"\nm={m}: L={L}, T={T:,}")
        print(f"  {'digit':>5}  {'alive_before':>12}  {'killed':>8}  "
              f"{'kill_rate':>10}  {'expected':>10}  {'ratio':>8}  "
              f"{'alive_after':>12}  {'global_rate':>12}")
        print("  " + "-" * 95)

        alive = np.ones(L, dtype=np.float64)  # just [0, L)

        # Need the digit values for indices [0, L)
        mod = 10 ** m
        x = pow(2, m, mod)
        orbit_digits = []
        for i in range(L):
            val = x
            digits = []
            for j in range(m):
                digits.append(val % 10)
                val //= 10
            orbit_digits.append(digits)
            x = (x * 2) % mod

        for k in range(m):
            alive_before = int(np.sum(alive))
            if alive_before == 0:
                print(f"  {k+1:>5}  {0:>12}  {0:>8}  {'N/A':>10}  {'N/A':>10}  {'N/A':>8}  {0:>12}")
                continue

            # Kill elements where digit k+1 is zero
            killed = 0
            for i in range(L):
                if alive[i] > 0 and orbit_digits[i][k] == 0:
                    alive[i] = 0
                    killed += 1

            alive_after = int(np.sum(alive))
            kill_rate = killed / alive_before if alive_before > 0 else 0
            expected_rate = 1/10
            ratio = kill_rate / expected_rate if expected_rate > 0 else 0

            # Global kill rate for comparison
            global_alive = int(np.sum(g[k]))
            global_rate = 1 - global_alive / T

            print(f"  {k+1:>5}  {alive_before:>12}  {killed:>8}  "
                  f"{kill_rate:>10.6f}  {expected_rate:>10.6f}  {ratio:>8.4f}  "
                  f"{alive_after:>12}  {global_rate:>12.6f}")


def part_D_small_index_correlation(max_m=9):
    """Test whether small indices have systematically different digit distributions.

    The finiteness question reduces to: are small orbit indices
    (i < C*m) "typical" in their digit behavior, or are they special?

    Compute: for each digit j, P(digit j = 0 | i < L) vs P(digit j = 0 | i >= L).
    If these are equal, small indices are typical and the main term
    L * rho_m gives the correct count.
    """
    print("\n" + "=" * 100)
    print("PART D: Small vs Large Index Digit Distributions")
    print("  P(digit j = 0 | i < L) vs P(digit j = 0 | i >= L)")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        L = min(int(math.ceil(C_CRIT * m)), T)

        print(f"\nm={m}: L={L}, T={T:,}")
        print(f"  {'digit':>5}  {'P(0|small)':>12}  {'P(0|large)':>12}  "
              f"{'P(0|all)':>10}  {'bias':>10}  {'bias_frac':>10}")
        print("  " + "-" * 70)

        for j in range(m):
            # P(digit j = 0) for small (i < L) and large (i >= L) indices
            small_zeros = L - int(np.sum(g[j][:L]))
            large_zeros = (T - L) - int(np.sum(g[j][L:]))
            all_zeros = T - int(np.sum(g[j]))

            p_small = small_zeros / L if L > 0 else 0
            p_large = large_zeros / (T - L) if T - L > 0 else 0
            p_all = all_zeros / T
            bias = p_small - p_large
            bias_frac = bias / p_all if p_all > 0 else 0

            print(f"  {j+1:>5}  {p_small:>12.6f}  {p_large:>12.6f}  "
                  f"{p_all:>10.6f}  {bias:>10.6f}  {bias_frac:>10.4f}")


def part_E_max_F_nonDC_formula(max_m=9):
    """The max non-DC coefficient appears to stabilize at ~0.1234 * rho.

    Test: is this value exactly related to known constants?

    Candidates:
    - 1/(2*pi) = 0.15915...  No
    - 3/(10*pi) = 0.09549... No
    - sin(pi/10) = 0.30902... No
    - 1/(2*sqrt(pi)) = 0.28209... No

    Better approach: find WHERE the maximum occurs and what determines it.
    """
    print("\n" + "=" * 100)
    print("PART E: Location and Structure of max |hat(f_m)| nonDC")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)
        Z = int(np.sum(f))
        rho = Z / T

        F = np.fft.fft(f) / T
        mags = np.abs(F)
        mags[0] = 0

        # Top 5 frequencies
        top_indices = np.argsort(mags)[::-1][:10]

        print(f"\nm={m}: T={T:,}, rho={rho:.8f}")
        print(f"  Top 10 non-DC Fourier coefficients:")
        print(f"  {'rank':>4}  {'j':>10}  {'|F(j)|':>14}  {'|F(j)|/rho':>12}  "
              f"{'v_5(j)':>6}  {'j/5^v':>8}  {'j/T':>12}  {'phase':>8}")
        print("  " + "-" * 85)

        for rank, j in enumerate(top_indices):
            if j == 0:
                continue
            mag = mags[j]
            ratio = mag / rho

            v5 = 0
            jj = int(j)
            while jj > 0 and jj % 5 == 0:
                v5 += 1
                jj //= 5

            phase = float(np.angle(F[j]))

            print(f"  {rank+1:>4}  {j:>10}  {mag:>14.10f}  {ratio:>12.8f}  "
                  f"{v5:>6}  {jj:>8}  {j/T:>12.8f}  {phase:>8.4f}")


def main():
    print("=" * 100)
    print("EXPERIMENT 20b: LACUNARY BOUND AND ERROR DECOMPOSITION")
    print("=" * 100)
    print()

    t_start = time.time()

    part_A_error_by_v5_band()
    part_B_sequential_error_by_digit()
    part_C_which_digit_kills()
    part_D_small_index_correlation()
    part_E_max_F_nonDC_formula()

    total = time.time() - t_start
    print(f"\nTotal elapsed: {total:.1f}s")


if __name__ == '__main__':
    main()
