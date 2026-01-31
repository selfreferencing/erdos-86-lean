#!/usr/bin/env python3
"""
Experiment 18: Fourier Structure of the Survivor Indicator

Key findings from Exp17:
- The naive error bound grows as ~2.1^m (useless for finiteness)
- But the ACTUAL error is O(1) (between -4 and -9 across m=2..9)
- The dominant Fourier coefficients cluster at j = 5^{m-2} * h
  (the 5-adic structure dominates)
- Spectral concentration is diffuse (top 10 is only 8% of L^2)

This experiment digs deeper:

Part A: Factor the survivor indicator across digit positions
  f_m(i) = product of single-digit conditions. The Fourier transform
  of a product is the convolution of the individual transforms.
  This should reveal WHY the L1 norm grows and WHERE cancellation occurs.

Part B: Conditional Fourier analysis
  Instead of bounding |sum F(j)*D_L(j)| by sum |F(j)|*|D_L(j)|,
  use the PHASE structure of F(j) and D_L(j) to get cancellation.

Part C: Level-to-level transfer of Fourier coefficients
  How do the Fourier coefficients at level m relate to those at level m+1?
  The 5-fold lift (T_{m+1} = 5*T_m) means F_{m+1}(j) should relate to
  F_m(j mod T_m) via a transfer formula.

Part D: The signed error as a function of L
  Plot E(L) = |S_m ∩ [0,L)| - L*rho for L = 0..T_m.
  If E(L) is bounded (Erdos-Turan style), we can use discrepancy theory.

Part E: Discrepancy bound
  D_m = max_L |E(L)| / T_m. If D_m -> 0, then for L = O(m),
  |E(L)| <= D_m * T_m, and we need D_m * T_m < 1 for L = Cm.
  Equivalently, D_m < 1/(C*m). Since D_m involves the L^inf norm of
  the partial sums, this is sharper than the L1 bound.
"""

import sys
import os
import json
import time
import math
import numpy as np

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

M_MAX = 9
C_CRIT = 1.0 / math.log10(2)


def enumerate_survivors(m):
    """Return survivor indicator array and count."""
    mod = 10 ** m
    T = 4 * 5 ** (m - 1)
    min_val = mod // 10

    f = np.zeros(T, dtype=np.float64)
    x = pow(2, m, mod)
    Z = 0

    for i in range(T):
        if x >= min_val and '0' not in str(x):
            f[i] = 1.0
            Z += 1
        x = (x * 2) % mod

    return f, Z, T


def part_A_digit_factorization(max_m=8):
    """Analyze the multiplicative structure of f_m across digit positions.

    The survivor condition is: digit_j(2^n mod 10^m) != 0 for j=1..m.
    Define g_j(i) = 1 if the j-th digit of the orbit element at index i is nonzero.
    Then f_m(i) = product_{j=1}^{m} g_j(i).

    Each g_j is a function on Z/T_m Z. Its Fourier transform hat(g_j) has
    specific structure because digit j depends on n mod T_j but not on n mod T_{j-1}.
    """
    print("=" * 100)
    print("PART A: Digit Factorization and Individual Fourier Analysis")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        mod = 10 ** m

        # Build per-digit indicators g_j
        g = [np.zeros(T, dtype=np.float64) for _ in range(m)]

        x = pow(2, m, mod)
        for i in range(T):
            digits = []
            val = x
            for d_idx in range(m):
                digits.append(val % 10)
                val //= 10
            # digits[0] = ones digit, digits[m-1] = leading digit
            for j in range(m):
                if digits[j] != 0:
                    g[j][i] = 1.0
            x = (x * 2) % mod

        # Compute DFT of each g_j
        G = [np.fft.fft(gj) / T for gj in g]

        # Mean and L1 norm of each digit's indicator
        print(f"\nm={m}: T={T:,}")
        print(f"  {'digit':>5}  {'mean':>8}  {'L1_nonDC':>12}  {'Linf_nonDC':>12}  "
              f"{'top_j':>8}  {'top_v5':>6}  {'top_rel':>8}")
        print("  " + "-" * 70)

        for j in range(m):
            mean_j = np.real(G[j][0])
            mags_j = np.abs(G[j])
            mags_noDC = mags_j.copy()
            mags_noDC[0] = 0
            l1_j = float(np.sum(mags_noDC))
            linf_j = float(np.max(mags_noDC))
            top_idx = int(np.argmax(mags_noDC))
            v5 = 0
            jj = top_idx
            while jj > 0 and jj % 5 == 0:
                v5 += 1
                jj //= 5
            top_rel = linf_j / mean_j if mean_j > 0 else 0
            print(f"  {j+1:>5}  {mean_j:>8.4f}  {l1_j:>12.4f}  {linf_j:>12.6f}  "
                  f"{top_idx:>8}  {v5:>6}  {top_rel:>8.4f}")

        # Product Fourier norm: L1(hat(f_m)) vs product of L1(hat(g_j))
        f_full = np.ones(T, dtype=np.float64)
        for j in range(m):
            f_full *= g[j]
        F_full = np.fft.fft(f_full) / T
        l1_product = float(np.sum(np.abs(F_full[1:])))
        l1_product_of_individuals = 1.0
        for j in range(m):
            l1_product_of_individuals *= (np.real(G[j][0]) + float(np.sum(np.abs(G[j][1:]))))

        print(f"\n  L1(hat(f_m)) [non-DC] = {l1_product:.4f}")
        print(f"  Product of individual (mean + L1_nonDC) = {l1_product_of_individuals:.4f}")
        print(f"  Ratio (compression) = {l1_product / l1_product_of_individuals:.6f}")


def part_B_signed_error(max_m=9):
    """Compute the signed error E(L) and analyze phase cancellation."""
    print("\n" + "=" * 100)
    print("PART B: Signed Error Analysis and Phase Cancellation")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        f, Z, T = enumerate_survivors(m)
        rho = Z / T

        L = min(int(math.ceil(C_CRIT * m)), T)

        # Compute exact cumulative sum
        cumsum = np.cumsum(f)

        # Exact count in [0, L)
        exact = int(cumsum[L - 1]) if L > 0 else 0
        main = L * rho
        signed_error = exact - main

        # Phase cancellation analysis via DFT
        F = np.fft.fft(f) / T
        j = np.arange(1, T)
        Fj = F[1:]

        # D_L(j) phase and magnitude
        theta = 2 * np.pi * j / T
        omega_L = np.exp(1j * theta * L)
        omega = np.exp(1j * theta)
        denom = 1.0 - omega
        safe = np.abs(denom) > 1e-15
        DLj = np.where(safe, (1.0 - omega_L) / np.where(safe, denom, 1.0), L)

        # Product F(j) * D_L(j): these are the individual error contributions
        products = Fj * DLj
        products_mag = np.abs(products)
        products_real = np.real(products)
        products_imag = np.imag(products)

        # The signed error is sum of products_real
        fourier_signed = float(np.sum(products_real))

        # Cancellation ratio: |sum| / sum |.|
        total_mag = float(np.sum(products_mag))
        cancellation = abs(fourier_signed) / total_mag if total_mag > 0 else 0

        print(f"\nm={m}: L={L}, T={T:,}, Z={Z:,}, rho={rho:.8f}")
        print(f"  Exact count in [0,L): {exact}")
        print(f"  Main term L*rho: {main:.4f}")
        print(f"  Signed error: {signed_error:.4f}")
        print(f"  Fourier signed error: {fourier_signed:.4f}")
        print(f"  Total |F(j)*D_L(j)|: {total_mag:.4f}")
        print(f"  Cancellation ratio: {cancellation:.6f} (lower = more cancellation)")
        print(f"  Cancellation factor: {total_mag / max(abs(fourier_signed), 0.001):.1f}x")


def part_C_transfer_structure(max_m=8):
    """How Fourier coefficients transfer between levels m and m+1.

    Since T_{m+1} = 5*T_m, the DFT at level m+1 has 5x more frequencies.
    The "folded" coefficients F_{m+1}(j) for j that are multiples of 5
    should relate to F_m(j/5).
    """
    print("\n" + "=" * 100)
    print("PART C: Level-to-Level Fourier Transfer")
    print("=" * 100)

    prev_F = None
    prev_T = None

    for m in range(1, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        f, Z, T = enumerate_survivors(m)
        F = np.fft.fft(f) / T

        if prev_F is not None and prev_T is not None:
            # Compare F_m(5j) with F_{m-1}(j)
            T_prev = prev_T
            ratios = []
            for j in range(1, min(T_prev, 20)):
                j5 = 5 * j
                if j5 < T:
                    ratio = F[j5] / prev_F[j] if abs(prev_F[j]) > 1e-15 else 0
                    ratios.append((j, j5, abs(prev_F[j]), abs(F[j5]),
                                   abs(ratio), float(np.angle(ratio))))

            if ratios:
                print(f"\nm={m}: Comparing F_m(5j) to F_{m-1}(j)")
                print(f"  {'j':>6} {'5j':>8} {'|F_{m-1}(j)|':>14} {'|F_m(5j)|':>14} "
                      f"{'|ratio|':>10} {'angle':>8}")
                print("  " + "-" * 65)
                for j, j5, mag_prev, mag_curr, r, angle in ratios[:10]:
                    print(f"  {j:>6} {j5:>8} {mag_prev:>14.8f} {mag_curr:>14.8f} "
                          f"{r:>10.6f} {angle:>8.4f}")

        prev_F = F
        prev_T = T


def part_D_discrepancy(max_m=9):
    """Compute the discrepancy of the survivor set.

    D_m = max_{0 <= L <= T} |S_m ∩ [0,L)| / Z_m - L/T_m|

    This is the classical discrepancy of the survivor set viewed as a
    subset of Z/T_m Z. By Erdos-Turan inequality:

    D_m <= C * (1/K + sum_{j=1}^{K} |hat(f)(j)| / (j * rho))

    for any K.
    """
    print("\n" + "=" * 100)
    print("PART D: Discrepancy of Survivor Set")
    print("=" * 100)

    print(f"\n{'m':>3}  {'T_m':>12}  {'Z_m':>10}  {'D_m':>12}  {'D_m*T_m':>12}  "
          f"{'D_m*Cm':>10}  {'max_dev':>10}  {'at_L':>8}")
    print("-" * 90)

    for m in range(1, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        f, Z, T = enumerate_survivors(m)
        rho = Z / T

        # Cumulative distribution
        cumsum = np.cumsum(f)

        # Expected cumulative
        expected = rho * np.arange(1, T + 1)

        # Discrepancy: max |cumsum(L)/Z - L/T|
        if Z > 0:
            deviations = np.abs(cumsum / Z - np.arange(1, T + 1) / T)
            D_m = float(np.max(deviations))
            max_dev_idx = int(np.argmax(deviations)) + 1

            # Also compute max |cumsum(L) - L*rho| (absolute deviation)
            abs_dev = np.abs(cumsum - expected)
            max_abs_dev = float(np.max(abs_dev))
            max_abs_idx = int(np.argmax(abs_dev)) + 1
        else:
            D_m = 1.0
            max_dev_idx = 0
            max_abs_dev = 0
            max_abs_idx = 0

        L_crit = min(int(math.ceil(C_CRIT * m)), T)
        D_times_T = D_m * T
        D_times_Cm = D_m * L_crit

        print(f"{m:>3}  {T:>12,}  {Z:>10,}  {D_m:>12.8f}  {D_times_T:>12.2f}  "
              f"{D_times_Cm:>10.4f}  {max_abs_dev:>10.2f}  {max_abs_idx:>8}")


def part_E_erdos_turan(max_m=9):
    """Apply the Erdos-Turan inequality to bound discrepancy.

    D_N <= C * (1/K + sum_{j=1}^{K} |hat(1_S)(j)| / j)

    where hat(1_S)(j) = (1/T) sum_{s in S} e^{-2*pi*i*j*s/T}
    """
    print("\n" + "=" * 100)
    print("PART E: Erdos-Turan Bound on Discrepancy")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        f, Z, T = enumerate_survivors(m)
        rho = Z / T

        # DFT of f
        F = np.fft.fft(f) / T

        # Erdos-Turan: for the normalized indicator (1/Z)*1_S,
        # the character sums are F(j)/rho
        # D_N <= (6/pi) * (1/K + sum_{j=1}^{K} |F(j)/rho| / j) for any K

        # Try various K values
        best_K = 1
        best_bound = float('inf')

        j_arr = np.arange(1, T)
        F_mags = np.abs(F[1:]) / rho if rho > 0 else np.zeros(T - 1)

        for K in [10, 50, 100, 500, T // 10, T // 2, T - 1]:
            K = min(K, T - 1)
            if K < 1:
                continue
            et_sum = np.sum(F_mags[:K] / j_arr[:K])
            bound = (6.0 / math.pi) * (1.0 / K + et_sum)
            if bound < best_bound:
                best_bound = bound
                best_K = K

        # The critical question: is D_m * C_crit * m < 1?
        L_crit = min(int(math.ceil(C_CRIT * m)), T)
        dev_bound = best_bound * Z  # max |S ∩ [0,L)| - L * rho| <= D_m * Z

        print(f"\nm={m}: T={T:,}, Z={Z:,}, rho={rho:.6f}")
        print(f"  Best Erdos-Turan bound: D_m <= {best_bound:.8f} (K={best_K})")
        print(f"  D_m * Z = {dev_bound:.4f}")
        print(f"  L_crit = {L_crit}, L_crit * rho = {L_crit * rho:.4f}")
        print(f"  Need: D_m * Z < 1 + L_crit * rho for count=0 guarantee")
        print(f"  Have: D_m * Z = {dev_bound:.4f} vs threshold {1 + L_crit * rho:.4f}")
        print(f"  {'SUFFICIENT' if dev_bound < 1 + L_crit * rho else 'INSUFFICIENT'}")


def main():
    print("=" * 100)
    print("EXPERIMENT 18: FOURIER STRUCTURE OF THE SURVIVOR INDICATOR")
    print("=" * 100)
    print()

    t_start = time.time()

    part_A_digit_factorization()
    part_B_signed_error()
    part_C_transfer_structure()
    part_D_discrepancy()
    part_E_erdos_turan()

    total = time.time() - t_start
    print(f"\nTotal elapsed: {total:.1f}s")


if __name__ == '__main__':
    main()
