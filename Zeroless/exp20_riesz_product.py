#!/usr/bin/env python3
"""
Experiment 20: Riesz Product Structure of the Survivor Indicator

MOTIVATION:
Both GPT analyses identified the Riesz product structure as the most
promising path to finiteness. The survivor indicator factors as:

    f_m(i) = g_1(i) * g_2(i) * ... * g_m(i)

where g_j(i) = 1 if digit j of the orbit element at index i is nonzero.

In Fourier space, hat(f_m) = hat(g_1) * hat(g_2) * ... * hat(g_m) (convolution).
For classical Riesz products where the g_j have "lacunary" frequencies
(frequencies that don't interact), the convolution simplifies and gives
explicit multiplicative bounds on individual Fourier coefficients.

KEY QUESTIONS:
1. Are the digit indicators "approximately lacunary" in frequency?
   g_j depends on i mod T_j where T_j = 4*5^{j-1}. So hat(g_j) is
   supported on frequencies that are multiples of T_m / T_j = 5^{m-j}.
   This IS lacunary (the support sets are nested, not overlapping).

2. Does the convolution structure give |hat(f_m)(r)| <= A * rho^m?
   If the individual g_j are "almost constant" (mean 9/10, small variation),
   then the convolution product should decay exponentially.

3. What is the "effective dimension" of each g_j in Fourier space?
   Each g_j has T_j effective Fourier coefficients (the rest are zero
   by periodicity). How concentrated is the non-DC part?

PARTS:
A. Verify lacunary structure of individual digit Fourier transforms
B. Track the convolution product explicitly: how |hat(f_m)(j)| grows/decays
   as we multiply in successive digit conditions
C. Test the pointwise bound: does max_{j!=0} |hat(f_m)(j)| / hat(f_m)(0) decay?
D. The "defect spectrum": for each j, compute hat(f_m)(j) / hat(f_m)(0)
   and map its magnitude vs the 5-adic structure of j
E. Test Riesz product prediction: if digits were truly independent,
   hat(f_m)(j) = Product_{k where v_5(j) < m-k} hat(g_k)(j mod T_k)
   Compare this prediction to actual values
"""

import sys
import os
import time
import math
import numpy as np

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

M_MAX = 9
C_CRIT = 1.0 / math.log10(2)


def build_orbit_and_digits(m):
    """Build orbit elements and per-digit indicators for level m."""
    T = 4 * 5 ** (m - 1)
    mod = 10 ** m

    # Per-digit indicators: g[j][i] = 1 if digit j+1 of orbit[i] is nonzero
    g = [np.zeros(T, dtype=np.float64) for _ in range(m)]

    x = pow(2, m, mod)
    for i in range(T):
        val = x
        for j in range(m):
            if val % 10 != 0:
                g[j][i] = 1.0
            val //= 10
        x = (x * 2) % mod

    # Full survivor indicator
    f = np.ones(T, dtype=np.float64)
    for j in range(m):
        f *= g[j]

    return g, f, T


def part_A_lacunary_structure(max_m=7):
    """Verify that digit Fourier transforms have lacunary support.

    g_j is periodic with period T_j = 4 * 5^{j-1}.
    So hat(g_j)(r) = 0 unless r is a multiple of T_m / T_j = 5^{m-j}.

    Verify this and measure the effective support size.
    """
    print("=" * 100)
    print("PART A: Lacunary Structure of Digit Fourier Transforms")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        print(f"\nm={m}: T={T:,}")
        print(f"  {'digit':>5}  {'period':>8}  {'stride':>8}  {'#nonzero':>10}  "
              f"{'expected':>10}  {'max_off':>12}  {'DC':>8}  {'L2_nonDC':>12}")
        print("  " + "-" * 90)

        for j in range(m):
            T_j = 4 * 5 ** j  # period of digit j+1
            stride = T // T_j if T_j > 0 else 1  # 5^{m-1-j}

            G_j = np.fft.fft(g[j]) / T

            # Check: hat(g_j)(r) should be zero unless stride | r
            mags = np.abs(G_j)
            max_off_stride = 0.0
            n_nonzero = 0
            threshold = 1e-12

            for r in range(T):
                if r % stride != 0:
                    if mags[r] > max_off_stride:
                        max_off_stride = mags[r]
                else:
                    if mags[r] > threshold:
                        n_nonzero += 1

            expected_support = T_j  # T_j frequencies at stride positions
            dc = float(np.real(G_j[0]))
            l2_nondc = float(np.sqrt(np.sum(mags[1:] ** 2)))

            print(f"  {j+1:>5}  {T_j:>8}  {stride:>8}  {n_nonzero:>10}  "
                  f"{expected_support:>10}  {max_off_stride:>12.2e}  "
                  f"{dc:>8.4f}  {l2_nondc:>12.8f}")


def part_B_sequential_convolution(max_m=8):
    """Track hat(f_m) as we multiply in digit conditions one by one.

    Start with h_0 = 1 (all 1s). Then h_k = h_{k-1} * g_k (pointwise).
    In Fourier: hat(h_k) = hat(h_{k-1}) * hat(g_k) (circular convolution).

    Track max_{r!=0} |hat(h_k)(r)| and the ratio to hat(h_k)(0) = mean(h_k).
    """
    print("\n" + "=" * 100)
    print("PART B: Sequential Convolution -- Pointwise Fourier Decay")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        print(f"\nm={m}: T={T:,}")
        print(f"  {'k':>3}  {'mean(h_k)':>12}  {'max|F_nonDC|':>14}  "
              f"{'ratio':>10}  {'L1_nonDC':>12}  {'L2_nonDC':>12}  {'decay':>8}")
        print("  " + "-" * 85)

        h = np.ones(T, dtype=np.float64)
        prev_max = None

        for k in range(m):
            h = h * g[k]
            H = np.fft.fft(h) / T

            dc = float(np.real(H[0]))
            mags = np.abs(H)
            mags_nodc = mags.copy()
            mags_nodc[0] = 0

            max_nodc = float(np.max(mags_nodc))
            l1_nodc = float(np.sum(mags_nodc))
            l2_nodc = float(np.sqrt(np.sum(mags_nodc ** 2)))

            ratio = max_nodc / dc if dc > 0 else float('inf')
            decay = max_nodc / prev_max if prev_max and prev_max > 0 else 0

            print(f"  {k+1:>3}  {dc:>12.8f}  {max_nodc:>14.8f}  "
                  f"{ratio:>10.6f}  {l1_nodc:>12.4f}  {l2_nodc:>12.8f}  "
                  f"{decay:>8.4f}")

            prev_max = max_nodc


def part_C_pointwise_decay_trend(max_m=9):
    """Track max_{r!=0} |hat(f_m)(r)| / |hat(f_m)(0)| across levels m.

    If this ratio decays exponentially in m, we get pointwise Fourier
    decay and finiteness follows.
    """
    print("\n" + "=" * 100)
    print("PART C: Pointwise Fourier Decay Trend Across Levels")
    print("=" * 100)

    print(f"\n{'m':>3}  {'T':>12}  {'Z':>10}  {'rho':>10}  "
          f"{'max|F|_nonDC':>14}  {'ratio':>10}  {'L1_nonDC':>12}  "
          f"{'ratio_decay':>12}  {'L1_decay':>10}")
    print("-" * 110)

    prev_ratio = None
    prev_l1 = None

    for m in range(1, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)
        Z = int(np.sum(f))
        rho = Z / T

        F = np.fft.fft(f) / T
        dc = float(np.real(F[0]))
        mags = np.abs(F)
        mags_nodc = mags.copy()
        mags_nodc[0] = 0

        max_nodc = float(np.max(mags_nodc))
        l1_nodc = float(np.sum(mags_nodc))

        ratio = max_nodc / dc if dc > 0 else float('inf')

        ratio_decay = ratio / prev_ratio if prev_ratio and prev_ratio > 0 else 0
        l1_decay = l1_nodc / prev_l1 if prev_l1 and prev_l1 > 0 else 0

        print(f"{m:>3}  {T:>12,}  {Z:>10,}  {rho:>10.6f}  "
              f"{max_nodc:>14.8f}  {ratio:>10.6f}  {l1_nodc:>12.4f}  "
              f"{ratio_decay:>12.6f}  {l1_decay:>10.4f}")

        prev_ratio = ratio
        prev_l1 = l1_nodc


def part_D_defect_spectrum(max_m=7):
    """Map |hat(f_m)(j)| / |hat(f_m)(0)| vs the 5-adic valuation of j.

    The 5-adic valuation v_5(j) controls which digit levels contribute
    to the Fourier coefficient at frequency j. Higher v_5 means more
    digit conditions are "invisible" at that frequency.
    """
    print("\n" + "=" * 100)
    print("PART D: Defect Spectrum -- Fourier Magnitude by 5-adic Valuation")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        F = np.fft.fft(f) / T
        dc = float(np.real(F[0]))
        mags = np.abs(F[1:])  # exclude DC

        # Classify by v_5
        max_v5 = m - 1
        by_v5 = {v: [] for v in range(max_v5 + 1)}

        for j_idx in range(len(mags)):
            j = j_idx + 1  # frequency
            v5 = 0
            jj = j
            while jj > 0 and jj % 5 == 0:
                v5 += 1
                jj //= 5
            v5 = min(v5, max_v5)
            by_v5[v5].append(mags[j_idx])

        print(f"\nm={m}: T={T:,}, DC={dc:.8f}")
        print(f"  {'v_5':>4}  {'count':>8}  {'max|F|':>12}  {'mean|F|':>12}  "
              f"{'max/DC':>10}  {'mean/DC':>10}  {'L1_frac':>10}")
        print("  " + "-" * 75)

        total_l1 = float(np.sum(mags))
        for v in range(max_v5 + 1):
            vals = by_v5[v]
            if vals:
                arr = np.array(vals)
                mx = float(np.max(arr))
                mn = float(np.mean(arr))
                l1_frac = float(np.sum(arr)) / total_l1 if total_l1 > 0 else 0
                print(f"  {v:>4}  {len(vals):>8}  {mx:>12.8f}  {mn:>12.10f}  "
                      f"{mx/dc:>10.6f}  {mn/dc:>10.8f}  {l1_frac:>10.4f}")


def part_E_riesz_prediction(max_m=7):
    """Test the Riesz product prediction against actual Fourier coefficients.

    If digit conditions were perfectly independent across digit positions,
    the Fourier coefficient at frequency j would factor as:

    hat(f_m)(j) = Product_{k=1}^{m} hat(g_k)(j)

    But this is WRONG -- hat(f_m) = convolution of hat(g_k), not product.
    The product formula holds for POINTWISE multiplication of functions,
    and the Fourier transform of a pointwise product is a convolution.

    However, because the g_k have lacunary support (g_k is periodic
    with period T_k, so hat(g_k) is supported on multiples of 5^{m-k}),
    the convolution might simplify.

    Specifically, for the Riesz product P(x) = Product(1 + a_k cos(n_k x))
    where n_k are lacunary (n_{k+1}/n_k >= 3), the Fourier coefficients
    can be computed explicitly.

    Here, g_k(i) = (9/10) + delta_k(i) where delta_k is mean-zero and
    periodic with period T_k. The product f_m = Product(9/10 + delta_k)
    expands into a sum over subsets S of {1,...,m}:

    f_m = sum_{S subset {1,...,m}} (9/10)^{m-|S|} * Product_{k in S} delta_k

    The Fourier transform of Product_{k in S} delta_k is the convolution
    of {hat(delta_k)}_{k in S}. Since the supports are nested (not truly
    lacunary), the convolution is nontrivial.

    BUT: if |S| is small, each delta_k has small L_inf norm (~1/10),
    so the product is small. If |S| is large, the (9/10)^{m-|S|} factor
    is close to 1 but the convolution involves many terms with potentially
    cancelling phases.

    This part computes the "subset expansion" terms for small |S| and
    checks how much of the total Fourier coefficient they explain.
    """
    print("\n" + "=" * 100)
    print("PART E: Riesz Product Subset Expansion")
    print("=" * 100)

    for m in range(2, min(max_m + 1, 7)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        # Decompose g_k = mean_k + delta_k
        means = []
        deltas = []
        Delta_fft = []

        for k in range(m):
            mean_k = float(np.mean(g[k]))
            delta_k = g[k] - mean_k
            means.append(mean_k)
            deltas.append(delta_k)
            Delta_fft.append(np.fft.fft(delta_k) / T)

        # Full product
        F_full = np.fft.fft(f) / T

        # Subset expansion: compute contribution from subsets of size 0, 1, 2, ...
        # Size 0: constant term = product of means = (9/10)^m
        dc_pred = 1.0
        for k in range(m):
            dc_pred *= means[k]

        print(f"\nm={m}: T={T:,}")
        print(f"  DC actual: {float(np.real(F_full[0])):.10f}")
        print(f"  DC predicted (product of means): {dc_pred:.10f}")

        # For size 1: sum over k of (prod of means except k) * hat(delta_k)
        size1_contribution = np.zeros(T, dtype=np.complex128)
        for k in range(m):
            coeff = dc_pred / means[k] if means[k] != 0 else 0
            size1_contribution += coeff * Delta_fft[k]

        # Compare size-1 prediction to actual non-DC
        actual_nodc = F_full.copy()
        actual_nodc[0] = 0
        pred_nodc = size1_contribution.copy()
        pred_nodc[0] = 0

        # Error: how much does size-1 explain?
        residual = actual_nodc - pred_nodc
        l1_actual = float(np.sum(np.abs(actual_nodc)))
        l1_pred = float(np.sum(np.abs(pred_nodc)))
        l1_residual = float(np.sum(np.abs(residual)))
        l2_actual = float(np.sqrt(np.sum(np.abs(actual_nodc) ** 2)))
        l2_residual = float(np.sqrt(np.sum(np.abs(residual) ** 2)))

        print(f"\n  Size-1 subset approximation:")
        print(f"    L1(actual non-DC): {l1_actual:.6f}")
        print(f"    L1(size-1 pred):   {l1_pred:.6f}")
        print(f"    L1(residual):      {l1_residual:.6f}")
        print(f"    L1 explained:      {1 - l1_residual/l1_actual:.4f}")
        print(f"    L2 explained:      {1 - l2_residual/l2_actual:.4f}")

        # Size 2: sum over pairs (j,k) of ... * conv(hat(delta_j), hat(delta_k))
        if m <= 6:  # Only compute for small m (O(m^2 * T log T) cost)
            size2_contribution = np.zeros(T, dtype=np.complex128)
            for j in range(m):
                for k in range(j + 1, m):
                    coeff = dc_pred / (means[j] * means[k]) if means[j] * means[k] != 0 else 0
                    # Convolution of Delta_fft[j] and Delta_fft[k]
                    # Conv in freq domain = pointwise product in time domain
                    # But we have the FFTs already, and conv(A,B) in freq = T * A * B in time... no.
                    # hat(delta_j * delta_k) = ifft(fft(delta_j) * fft(delta_k)) / T... careful with normalization
                    # Actually: fft(a*b) != fft(a)*fft(b) in general
                    # fft(a * b)[r] = sum_s fft(a)[s] * fft(b)[r-s] (circular convolution)
                    # So hat(a*b) = conv(hat(a), hat(b)) where hat = fft/T
                    # But fft gives unnormalized. We have Delta_fft = fft/T.
                    # (fft/T)(a*b) = conv of (fft/T)(a) and ... no, need to be more careful.

                    # Easier: just compute the product in time domain and FFT
                    prod_jk = deltas[j] * deltas[k]
                    hat_prod_jk = np.fft.fft(prod_jk) / T
                    size2_contribution += coeff * hat_prod_jk

            total_pred = pred_nodc + size2_contribution
            total_pred[0] = 0
            residual2 = actual_nodc - total_pred
            l1_residual2 = float(np.sum(np.abs(residual2)))
            l2_residual2 = float(np.sqrt(np.sum(np.abs(residual2) ** 2)))

            print(f"\n  Size-1 + Size-2 approximation:")
            print(f"    L1(residual):      {l1_residual2:.6f}")
            print(f"    L1 explained:      {1 - l1_residual2/l1_actual:.4f}")
            print(f"    L2 explained:      {1 - l2_residual2/l2_actual:.4f}")


def part_F_critical_test(max_m=9):
    """THE critical test: does the Fourier error in [0, Cm] go to zero?

    Compute E_m = |S_m cap [0, L)| - L * rho_m for L = ceil(C * m).
    Then compute the Fourier error bound restricted to different
    frequency bands and see which band dominates.

    Also: compute the "effective Riesz product bound" by taking
    max_{r!=0} |hat(f_m)(r)| and multiplying by L (trivial bound
    for the geometric sum). If max|hat(f_m)(r)| * L < rho_m * L,
    the Fourier bound works.
    """
    print("\n" + "=" * 100)
    print("PART F: Critical Finiteness Test -- Riesz Bound vs Main Term")
    print("=" * 100)

    print(f"\n{'m':>3}  {'L':>5}  {'exact':>6}  {'main':>8}  {'error':>8}  "
          f"{'max|F|':>12}  {'L*max|F|':>10}  {'main_term':>10}  "
          f"{'bound_ratio':>12}  {'verdict':>12}")
    print("-" * 115)

    for m in range(1, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)
        Z = int(np.sum(f))
        rho = Z / T

        L = min(int(math.ceil(C_CRIT * m)), T)

        # Exact count
        exact = int(np.sum(f[:L]))
        main = L * rho
        error = exact - main

        # Fourier bound: max |hat(f_m)(r)| for r != 0
        F = np.fft.fft(f) / T
        mags = np.abs(F)
        mags[0] = 0
        max_F = float(np.max(mags))

        # Trivial bound: |error| <= (T-1) * max|F| (from sum of geometric sums)
        # Better bound: |error| <= L * max|F| * (T-1) ... no, need the DFT theory
        # Actually: error = sum_{j!=0} F(j) * D_L(j)
        # |error| <= max|F(j)| * sum_{j!=0} |D_L(j)|
        # But sum |D_L(j)| can be bounded. For L << T:
        # sum |D_L(j)| ~ T * log(T) / pi (approximately)

        # Better: use the specific bound
        # |error| <= sum_{j!=0} |F(j)| * min(L, 1/|2 sin(pi j/T)|)
        j_arr = np.arange(1, T)
        sin_vals = np.abs(np.sin(np.pi * j_arr / T))
        geom_bound = np.minimum(L, 1.0 / (2 * np.maximum(sin_vals, 1e-15)))
        fourier_bound = float(np.sum(np.abs(F[1:]) * geom_bound))

        # The simple Riesz-type bound: L * max|F|_nonDC
        riesz_bound = L * max_F
        bound_ratio = riesz_bound / main if main > 0 else float('inf')

        verdict = "SUFFICIENT" if riesz_bound < main else "INSUFFICIENT"

        print(f"{m:>3}  {L:>5}  {exact:>6}  {main:>8.2f}  {error:>8.2f}  "
              f"{max_F:>12.8f}  {riesz_bound:>10.4f}  {main:>10.4f}  "
              f"{bound_ratio:>12.6f}  {verdict:>12}")


def part_G_individual_digit_spectra(max_m=8):
    """Detailed analysis of each digit's Fourier spectrum.

    For the Riesz product bound to work, we need each digit indicator
    g_j to have Fourier coefficients that are "small" relative to DC.

    Specifically, if hat(g_j)(0) = 9/10 and max_{r!=0} |hat(g_j)(r)| = alpha,
    then the Riesz product bound gives |hat(f_m)(r)| <= product of
    something involving alpha. We need alpha << 1.

    Key structural fact: g_j(i) depends on i mod T_j, so hat(g_j)
    has only T_j nonzero Fourier coefficients (at multiples of stride = T/T_j).
    The L2 norm constraint gives: sum |hat(g_j)(r)|^2 = ||g_j||_2^2 / T.
    Since g_j is 0-1 valued with mean 9/10, ||g_j||_2^2 = T * 9/10.
    So sum |hat(g_j)(r)|^2 = 9/10 / T. Wait, need to be more careful.

    Actually hat(g_j)(r) = (1/T) * sum_{i} g_j(i) * exp(-2pi i r i / T)
    Parseval: sum_r |hat(g_j)(r)|^2 = (1/T) * sum_i |g_j(i)|^2 = 9/10 * 1/T? No.

    Parseval for DFT: sum_r |hat(g_j)(r)|^2 = (1/T) * sum_i |g_j(i)|^2 = mean(g_j^2)
    Since g_j is 0-1, g_j^2 = g_j, so sum |hat(g_j)(r)|^2 = 9/10.
    The DC term is |hat(g_j)(0)|^2 = (9/10)^2 = 81/100.
    So sum_{r!=0} |hat(g_j)(r)|^2 = 9/10 - 81/100 = 9/100.
    And the number of nonzero non-DC terms is T_j - 1.
    So the RMS non-DC coefficient is sqrt(9/100 / (T_j - 1)) = 3/(10*sqrt(T_j-1)).

    For T_j = 4*5^j: RMS ~ 3/(10 * 2 * 5^{j/2}) = 3/(20 * 5^{j/2}).
    This decays as 5^{-j/2}. Good -- individual digit Fourier coefficients
    get small. But we need the MAX, not the RMS.
    """
    print("\n" + "=" * 100)
    print("PART G: Individual Digit Fourier Spectra -- RMS vs Max")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        print(f"\nm={m}: T={T:,}")
        print(f"  {'digit':>5}  {'T_j':>8}  {'DC':>8}  {'RMS_pred':>10}  "
              f"{'RMS_actual':>10}  {'max|F|':>10}  {'max/DC':>8}  "
              f"{'max/RMS':>8}  {'L1_nonDC':>10}")
        print("  " + "-" * 95)

        for j in range(m):
            T_j = 4 * 5 ** j
            G_j = np.fft.fft(g[j]) / T

            dc = float(np.real(G_j[0]))
            mags = np.abs(G_j)
            mags_nodc = mags.copy()
            mags_nodc[0] = 0

            max_nodc = float(np.max(mags_nodc))
            l1_nodc = float(np.sum(mags_nodc))

            # Parseval check
            sum_sq_nodc = float(np.sum(mags_nodc ** 2))
            rms_actual = math.sqrt(sum_sq_nodc / max(T_j - 1, 1))
            rms_pred = 3.0 / (10.0 * math.sqrt(max(T_j - 1, 1)))

            print(f"  {j+1:>5}  {T_j:>8}  {dc:>8.4f}  {rms_pred:>10.6f}  "
                  f"{rms_actual:>10.6f}  {max_nodc:>10.6f}  "
                  f"{max_nodc/dc:>8.4f}  "
                  f"{max_nodc/rms_actual if rms_actual > 0 else 0:>8.2f}  "
                  f"{l1_nodc:>10.4f}")


def part_H_convolution_product_bound(max_m=7):
    """Test: does the convolution product give a multiplicative bound?

    Key idea: f_m = g_1 * g_2 * ... * g_m (pointwise product).
    In Fourier: hat(f_m)(r) = sum over r_1+...+r_m = r (mod T) of
    product hat(g_k)(r_k). This is the convolution.

    For r != 0, at least one r_k != 0. The key question:
    how much "mixing" does each convolution step create?

    A simple bound: for the first k digits,
    max_{r!=0} |hat(h_k)(r)| <= max_{r!=0} |hat(h_{k-1})(r)| * ||hat(g_k)||_1
    + ||hat(h_{k-1})||_1 * max_{r!=0} |hat(g_k)(r)|

    But this uses L1 norms which grow. The RIGHT bound should use the
    Riesz product structure:

    |hat(f_m)(r)| <= Product_{k : r_k != 0} |hat(g_k)(r_k)|

    where the minimum is over all decompositions r = r_1 + ... + r_m.

    Since the g_k have lacunary support (stride 5^{m-1-k} for digit k+1),
    the decomposition is highly constrained.

    This part directly computes the sequential convolution and tests
    whether the max non-DC coefficient decays or grows.
    """
    print("\n" + "=" * 100)
    print("PART H: Convolution Product Decay Test")
    print("  Does max_{r!=0} |hat(h_k)(r)| decay as k increases?")
    print("  h_k = g_1 * ... * g_k (first k digit conditions)")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        g, f, T = build_orbit_and_digits(m)

        print(f"\nm={m}: T={T:,}")
        print(f"  {'k':>3}  {'DC(h_k)':>10}  {'max_nonDC':>12}  "
              f"{'ratio(max/DC)':>14}  {'decay_factor':>14}  {'num_survivors':>14}")
        print("  " + "-" * 80)

        h = np.ones(T, dtype=np.float64)
        prev_ratio = None

        for k in range(m):
            h = h * g[k]
            H = np.fft.fft(h) / T
            dc = float(np.real(H[0]))
            mags = np.abs(H)
            mags[0] = 0
            max_nodc = float(np.max(mags))
            ratio = max_nodc / dc if dc > 0 else float('inf')
            decay = ratio / prev_ratio if prev_ratio and prev_ratio > 0 else 0
            n_surv = int(np.sum(h))

            print(f"  {k+1:>3}  {dc:>10.6f}  {max_nodc:>12.8f}  "
                  f"{ratio:>14.8f}  {decay:>14.8f}  {n_surv:>14,}")

            prev_ratio = ratio


def main():
    print("=" * 100)
    print("EXPERIMENT 20: RIESZ PRODUCT STRUCTURE OF SURVIVOR INDICATOR")
    print("=" * 100)
    print()

    t_start = time.time()

    part_A_lacunary_structure()
    part_B_sequential_convolution()
    part_C_pointwise_decay_trend()
    part_D_defect_spectrum()
    part_E_riesz_prediction()
    part_F_critical_test()
    part_G_individual_digit_spectra()
    part_H_convolution_product_bound()

    total = time.time() - t_start
    print(f"\nTotal elapsed: {total:.1f}s")


if __name__ == '__main__':
    main()
