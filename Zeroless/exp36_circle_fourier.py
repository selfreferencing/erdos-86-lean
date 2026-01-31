#!/usr/bin/env python3
"""
Experiment 36: Circle Fourier Coefficients of the Zeroless Set F_m

MOTIVATION:
Strategy C' (o(1) coboundary) requires verifying that
  S_m := sum_{k != 0} |hat{1_{F_m}}(k)| / ||k*theta|| = o(1)
where F_m is the zeroless set in [0,1), theta = log10(2), and the
Fourier basis is the standard circle basis e^{2*pi*i*k*x}.

All prior Fourier experiments (20-25) used the 5-adic orbit basis.
This experiment computes circle Fourier coefficients using TWO methods:
  (1) Analytic interval formula (exact, no discretization error)
  (2) Product formula over digit positions (Maynard's factorization)

KEY QUESTIONS:
1. Does |hat{1_{F_m}}(k)| ~ rho_m for low |k|?
2. Does S_m decrease with m?
3. Which frequencies dominate S_m?
4. Does the product formula match the interval formula?

PARTS:
A) Enumerate zeroless runs, build interval endpoints
B) Analytic Fourier coefficients via interval formula
C) Product formula Fourier coefficients (Maynard factorization)
D) FFT cross-check for small m
E) Compute S_m and band decomposition
F) Test heuristic |hat(k)| / rho_m ~ 1
G) Identify dangerous frequencies
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
    """Enumerate maximal runs of consecutive zeroless m-digit integers.
    Returns (run_starts, run_ends) as lists of integers.
    A run [n_start, n_end] means n_start, n_start+1, ..., n_end are all zeroless.
    """
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
    """Convert integer runs to alpha-intervals in [0,1).
    Interval for run [n_start, n_end]: [log10(n_start) - (m-1), log10(n_end+1) - (m-1))
    """
    a_starts = np.array([math.log10(n) - (m - 1) for n in run_starts])
    a_ends = np.array([math.log10(n + 1) - (m - 1) for n in run_ends])
    return a_starts, a_ends


def fourier_coeff_intervals(k, a_starts, a_ends):
    """Compute hat{1_{F_m}}(k) using exact interval formula.
    hat(k) = sum_j (e^{-2pi i k a_j} - e^{-2pi i k b_j}) / (2pi i k)
    """
    if k == 0:
        return np.sum(a_ends - a_starts)
    phase_starts = np.exp(-2j * np.pi * k * a_starts)
    phase_ends = np.exp(-2j * np.pi * k * a_ends)
    return np.sum(phase_starts - phase_ends) / (2j * np.pi * k)


def fourier_coeff_product(k, m):
    """Compute hat{1_{F_m}}(k) using Maynard's product formula.

    The indicator of "all m digits nonzero" factors over digit positions.
    For an m-digit number with digits d_1 d_2 ... d_m (d_1 != 0 always for m-digit),
    each digit d_j ranges over {1,...,9} (for j=1,...,m for zeroless).

    On the circle [0,1), alpha = log10(x) - (m-1) where x in [10^{m-1}, 10^m).
    The Fourier transform is:
      hat{1_{F_m}}(k) = integral_0^1 1_{F_m}(alpha) e^{-2pi i k alpha} d alpha

    Using the substitution x = 10^{m-1+alpha}, dx = x * ln(10) * d alpha:
      = integral_{10^{m-1}}^{10^m} 1_{zeroless}(floor(x)) e^{-2pi i k (log10(x) - (m-1))} dx / (x ln 10)
      = integral 1_{zeroless}(floor(x)) * x^{-2pi i k / ln 10} * 10^{(m-1)*2pi i k / ln 10} / (x ln 10) dx

    This does NOT factor as a simple digit product because log10 is nonlinear.

    Instead, use the DISCRETE product formula for the exponential sum:
      S(theta) = sum_{n: m-digit, zeroless} e(n * theta)
             = sum_{d_1=1}^{9} e(d_1 * 10^{m-1} * theta) *
               sum_{d_2=1}^{9} e(d_2 * 10^{m-2} * theta) * ... *
               sum_{d_m=1}^{9} e(d_m * theta)

    This gives the Fourier transform of the INTEGER-weighted measure, not
    the continuous circle measure. The two are related but distinct.

    For the continuous circle, we need the interval formula (Part B).
    This function computes the discrete product sum for comparison.
    """
    # Discrete exponential sum: sum_{n zeroless m-digit} e(n * theta_val)
    # where theta_val is a parameter (not the log10(2) constant)
    # This factors as product over digit positions j=0,...,m-1:
    #   factor_j = sum_{d=1}^{9} e(d * 10^j * theta_val)
    # We use theta_val = k / (10^m) as a normalization... actually let's
    # compute directly.
    #
    # For the circle Fourier coefficient, we need:
    # hat{1_{F_m}}(k) = sum over runs of integral e^{-2pi i k alpha} d alpha
    # The product formula applies to the DISCRETE sum, not the circle integral.
    #
    # So this function computes the discrete analog:
    # D(t) = (1/N_zeroless) * sum_{n zeroless m-digit} e(n * t)
    # where N_zeroless = 9^m (wait, 9^{m-1} * 9 = 9^m if first digit also restricted,
    # but first digit is always 1-9 for m-digit numbers, so only m-1 constraints
    # are non-trivial). Actually for m-digit zeroless:
    # d_1 in {1,...,9}, d_2 in {1,...,9}, ..., d_m in {1,...,9}
    # All 9^m combinations, but as m-digit numbers d_1 >= 1 is automatic.
    # Wait: for m-digit numbers d_1 in {1,...,9} always. So zeroless means
    # d_2,...,d_m in {1,...,9}, which is 9^{m-1} additional constraints beyond
    # the natural m-digit constraint. Total zeroless count = 9^m - but no,
    # 9 choices for each of m digits = 9^m. Wait: d_1 in {1..9} (9 choices),
    # d_2 in {1..9} (9 choices), ..., d_m in {1..9} (9 choices) = 9^m total.
    # But mu(F_m) = 9^m / (9 * 10^{m-1}) = (9/10)^{m-1}. Yes: the m-digit
    # integers range from 10^{m-1} to 10^m-1, total 9*10^{m-1}, of which 9^m
    # are zeroless. So rho = 9^m / (9*10^{m-1}) = (9/10)^{m-1}.

    # Product formula for discrete sum:
    # S(t) = prod_{j=0}^{m-1} sum_{d=1}^{9} e(d * 10^j * t)
    product = 1.0 + 0j
    for j in range(m):
        factor = sum(np.exp(2j * np.pi * d * (10 ** j) * k) for d in range(1, 10))
        # Hmm, but what frequency does k correspond to?
        # For the discrete sum: S(t) = sum_n 1_{zeroless}(n) e(n*t)
        # We want to evaluate at specific t values.
        # But this is NOT the same as the circle Fourier coefficient.
        pass

    # Actually, the cleanest approach: compute the product formula for the
    # discrete exponential sum S(t) = sum_{zeroless n} e(n*t) at t = k/10^m.
    # At these rational points, the product factorizes nicely.
    # But for general k (circle frequency), there's no simple product.
    # Return None to indicate this function is for comparison only.
    return None


def fourier_magnitudes_interval(m, K_max, a_starts, a_ends, verbose=True):
    """Compute |hat{1_{F_m}}(k)| for k = 1..K_max using interval formula."""
    mags = np.zeros(K_max)
    for k in range(1, K_max + 1):
        fk = fourier_coeff_intervals(k, a_starts, a_ends)
        mags[k - 1] = abs(fk)
        if verbose and k <= 5:
            print(f"    k={k}: |hat(k)| = {abs(fk):.6e}, hat(k) = {fk:.6e}")
    return mags


def frac_dist(x):
    """Compute ||x|| = min(frac(x), 1 - frac(x))."""
    fx = x - math.floor(x)
    return min(fx, 1.0 - fx)


if __name__ == "__main__":
    print("=" * 70)
    print("  EXPERIMENT 36: CIRCLE FOURIER COEFFICIENTS OF F_m")
    print("=" * 70)

    all_results = {}

    # =================================================================
    # Part A: Enumerate zeroless runs and build intervals
    # =================================================================
    print()
    print("=" * 70)
    print("  PART A: Enumerate zeroless runs")
    print("=" * 70)
    print()

    interval_data = {}
    M_MAX_ENUM = 7  # enumerate up to m=7 (m=8 takes ~2 min)

    for m in range(2, M_MAX_ENUM + 1):
        t0 = time.time()
        run_starts, run_ends = enumerate_zeroless_runs(m)
        elapsed = time.time() - t0

        a_starts, a_ends = runs_to_alpha(run_starts, run_ends, m)
        total_measure = np.sum(a_ends - a_starts)
        rho_expected = (9.0 / 10.0) ** (m - 1)
        n_runs = len(run_starts)
        n_zeroless = sum(e - s + 1 for s, e in zip(run_starts, run_ends))
        max_width = np.max(a_ends - a_starts) if n_runs > 0 else 0

        interval_data[m] = {
            "a_starts": a_starts,
            "a_ends": a_ends,
            "n_runs": n_runs,
            "n_zeroless": n_zeroless,
        }

        print(f"  m={m}: {n_zeroless} zeroless integers, {n_runs} runs")
        print(f"    mu(F_m) = {total_measure:.10f}, expected (9/10)^{m-1} = {rho_expected:.10f}")
        print(f"    ratio = {total_measure / rho_expected:.10f}")
        print(f"    max component width = {max_width:.6e}")
        print(f"    9^{m-1} = {9**(m-1)}, expected runs ~ 9^{m-1}/avg_run_len")
        print(f"    elapsed: {elapsed:.2f}s")
        print()

        all_results[f"partA_m{m}"] = {
            "n_zeroless": n_zeroless,
            "n_runs": n_runs,
            "total_measure": float(total_measure),
            "rho_expected": rho_expected,
            "measure_ratio": float(total_measure / rho_expected),
            "max_comp_width": float(max_width),
            "elapsed_s": elapsed,
        }

    # =================================================================
    # Part B: Analytic Fourier coefficients via interval formula
    # =================================================================
    print()
    print("=" * 70)
    print("  PART B: Analytic Fourier coefficients (interval formula)")
    print("=" * 70)
    print()

    K_MAX = 5000  # frequencies to compute
    fourier_data = {}

    for m in range(2, min(M_MAX_ENUM + 1, 7)):  # m=2..6 for speed
        print(f"  m={m}: computing |hat(k)| for k=1..{K_MAX} ...")
        t0 = time.time()
        a_s = interval_data[m]["a_starts"]
        a_e = interval_data[m]["a_ends"]
        mags = fourier_magnitudes_interval(m, K_MAX, a_s, a_e, verbose=(m <= 3))
        elapsed = time.time() - t0
        fourier_data[m] = mags
        rho = (9.0 / 10.0) ** (m - 1)
        print(f"    mean |hat(k)| = {np.mean(mags):.6e}, rho_m = {rho:.6e}")
        print(f"    max |hat(k)| = {np.max(mags):.6e} at k={np.argmax(mags)+1}")
        print(f"    elapsed: {elapsed:.2f}s")
        print()

        # Store summary (not full array)
        all_results[f"partB_m{m}"] = {
            "K_max": K_MAX,
            "mean_mag": float(np.mean(mags)),
            "max_mag": float(np.max(mags)),
            "max_mag_k": int(np.argmax(mags) + 1),
            "rho_m": rho,
            "elapsed_s": elapsed,
        }

    # Also do m=7 with reduced K_max
    if 7 in interval_data:
        m = 7
        K_MAX_7 = 1000
        print(f"  m={m}: computing |hat(k)| for k=1..{K_MAX_7} ...")
        t0 = time.time()
        a_s = interval_data[m]["a_starts"]
        a_e = interval_data[m]["a_ends"]
        mags7 = fourier_magnitudes_interval(m, K_MAX_7, a_s, a_e, verbose=False)
        elapsed = time.time() - t0
        fourier_data[m] = mags7
        rho = (9.0 / 10.0) ** (m - 1)
        print(f"    mean |hat(k)| = {np.mean(mags7):.6e}, rho_m = {rho:.6e}")
        print(f"    max |hat(k)| = {np.max(mags7):.6e} at k={np.argmax(mags7)+1}")
        print(f"    elapsed: {elapsed:.2f}s")
        print()
        all_results[f"partB_m{m}"] = {
            "K_max": K_MAX_7,
            "mean_mag": float(np.mean(mags7)),
            "max_mag": float(np.max(mags7)),
            "max_mag_k": int(np.argmax(mags7) + 1),
            "rho_m": rho,
            "elapsed_s": elapsed,
        }

    # =================================================================
    # Part C: Product formula (discrete exponential sum)
    # =================================================================
    print()
    print("=" * 70)
    print("  PART C: Product formula for discrete exponential sum")
    print("=" * 70)
    print()
    print("  The Maynard product formula applies to the DISCRETE sum")
    print("  S(t) = sum_{zeroless n} e(n*t), not the circle integral.")
    print("  Computing S(k/10^m) via product formula and comparing")
    print("  to the interval formula (which gives the circle integral).")
    print()

    for m in range(2, 5):
        rho = (9.0 / 10.0) ** (m - 1)
        N_total = 9 * 10 ** (m - 1)  # total m-digit integers
        N_zeroless = 9 ** m
        print(f"  m={m}: N_zeroless={N_zeroless}, N_total={N_total}")

        for k in [1, 2, 3, 5, 10]:
            # Product formula: S(t) = prod_{j=0}^{m-1} sum_{d=1}^{9} e(d * 10^j * t)
            t_val = k / (10.0 ** m)
            product = 1.0 + 0j
            for j in range(m):
                factor = sum(
                    np.exp(2j * np.pi * d * (10 ** j) * t_val) for d in range(1, 10)
                )
                product *= factor

            # The discrete sum normalized: (1/N_total) * S(t) should relate
            # to the circle Fourier coefficient if intervals are narrow.
            # hat{1_{F_m}}(k) ~ (1/N_total) * sum_n 1_{zeroless}(n) * integral contribution
            # The exact relationship: for narrow intervals,
            # hat{1_{F_m}}(k) ~ (1/(N_total * ln10 * 10^{m-1})) * S(k/(10^m * 2pi))
            # Actually this is subtle. Let's just compare magnitudes.

            # Direct interval formula
            a_s = interval_data[m]["a_starts"]
            a_e = interval_data[m]["a_ends"]
            hat_interval = fourier_coeff_intervals(k, a_s, a_e)

            print(
                f"    k={k}: |S_product| = {abs(product):.6e}, "
                f"|hat_interval| = {abs(hat_interval):.6e}, "
                f"|S|/N_zeroless = {abs(product)/N_zeroless:.6e}, "
                f"rho = {rho:.6e}"
            )
        print()

    # =================================================================
    # Part D: FFT cross-check for small m
    # =================================================================
    print()
    print("=" * 70)
    print("  PART D: FFT cross-check")
    print("=" * 70)
    print()

    for m in range(2, 5):
        N_disc = 10 ** (m + 2)
        print(f"  m={m}: FFT with N_disc={N_disc} ...")

        # Build indicator array
        indicator = np.zeros(N_disc)
        base = 10 ** (m - 1)
        for j in range(N_disc):
            alpha_j = j / N_disc
            x = int(10 ** (m - 1 + alpha_j))
            if x >= 10 ** m:
                x = 10 ** m - 1
            if is_zeroless(x, m):
                indicator[j] = 1.0

        fft_measure = np.mean(indicator)
        rho = (9.0 / 10.0) ** (m - 1)
        print(f"    FFT measure = {fft_measure:.8f}, rho = {rho:.8f}")

        # FFT
        F = np.fft.fft(indicator) / N_disc
        fft_mags = np.abs(F)

        # Compare to analytic for k = 1..50
        a_s = interval_data[m]["a_starts"]
        a_e = interval_data[m]["a_ends"]

        max_rel_err = 0.0
        for k in range(1, min(51, N_disc // 2)):
            analytic = abs(fourier_coeff_intervals(k, a_s, a_e))
            fft_val = fft_mags[k]
            if analytic > 1e-15:
                rel_err = abs(fft_val - analytic) / analytic
                max_rel_err = max(max_rel_err, rel_err)
                if k <= 5:
                    print(
                        f"    k={k}: FFT={fft_val:.8e}, analytic={analytic:.8e}, "
                        f"rel_err={rel_err:.4e}"
                    )

        print(f"    max relative error (k=1..50): {max_rel_err:.4e}")
        print()

        all_results[f"partD_m{m}"] = {
            "N_disc": N_disc,
            "fft_measure": float(fft_measure),
            "max_rel_error_k1_50": float(max_rel_err),
        }

    # =================================================================
    # Part E: Compute S_m and band decomposition
    # =================================================================
    print()
    print("=" * 70)
    print("  PART E: S_m = sum |hat(k)| / ||k*theta||")
    print("=" * 70)
    print()

    # Convergent denominators of theta = log10(2)
    # CF: [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, ...]
    convergent_denoms = [1, 3, 10, 93, 196, 485, 2136, 13301, 28738,
                         42039, 70777, 254370, 325147]

    sm_results = {}

    for m in sorted(fourier_data.keys()):
        mags = fourier_data[m]
        K = len(mags)
        rho = (9.0 / 10.0) ** (m - 1)

        # Compute ||k*theta|| for k=1..K
        k_vals = np.arange(1, K + 1, dtype=float)
        kt = k_vals * theta
        frac_kt = kt - np.floor(kt)
        norm_kt = np.minimum(frac_kt, 1.0 - frac_kt)

        # S_m = 2 * sum |hat(k)| / ||k*theta|| (factor of 2 for negative k)
        terms = mags / norm_kt
        S_m = 2.0 * np.sum(terms)

        # Band decomposition
        low_mask = k_vals <= m
        mid_mask = (k_vals > m) & (k_vals <= m * m)
        high_mask = k_vals > m * m

        S_low = 2.0 * np.sum(terms[low_mask]) if np.any(low_mask) else 0.0
        S_mid = 2.0 * np.sum(terms[mid_mask]) if np.any(mid_mask) else 0.0
        S_high = 2.0 * np.sum(terms[high_mask]) if np.any(high_mask) else 0.0

        # Identify largest terms
        top_idx = np.argsort(terms)[-10:][::-1]
        top_k = (top_idx + 1).tolist()
        top_terms = terms[top_idx].tolist()

        # Check if top k are near convergent denominators
        near_convergent = []
        for tk in top_k:
            for q in convergent_denoms:
                if abs(tk - q) <= 2:
                    near_convergent.append((tk, q))

        print(f"  m={m} (K={K}):")
        print(f"    S_m  = {S_m:.6f}")
        print(f"    S_low (|k|<={m}) = {S_low:.6f}")
        print(f"    S_mid ({m}<|k|<={m*m}) = {S_mid:.6f}")
        print(f"    S_high (|k|>{m*m}) = {S_high:.6f}")
        print(f"    rho_m = {rho:.6e}")
        print(f"    Top-5 terms: k = {top_k[:5]}")
        print(f"    Top-5 values: {[f'{v:.4f}' for v in top_terms[:5]]}")
        if near_convergent:
            print(f"    Near convergent denoms: {near_convergent}")
        print()

        sm_results[m] = {
            "S_m": float(S_m),
            "S_low": float(S_low),
            "S_mid": float(S_mid),
            "S_high": float(S_high),
            "K_max": K,
            "rho_m": rho,
            "top10_k": top_k,
            "top10_terms": [float(t) for t in top_terms],
        }

    all_results["partE"] = sm_results

    # Summary table
    print("  SUMMARY: S_m vs m")
    print("  " + "-" * 60)
    print(f"  {'m':>3} {'S_m':>12} {'S_low':>12} {'S_mid':>12} {'S_high':>12} {'rho_m':>12}")
    print("  " + "-" * 60)
    for m in sorted(sm_results.keys()):
        r = sm_results[m]
        print(
            f"  {m:>3} {r['S_m']:>12.4f} {r['S_low']:>12.4f} "
            f"{r['S_mid']:>12.4f} {r['S_high']:>12.4f} {r['rho_m']:>12.6e}"
        )
    print()

    # =================================================================
    # Part F: Test heuristic |hat(k)| / rho_m ~ 1
    # =================================================================
    print()
    print("=" * 70)
    print("  PART F: Heuristic test |hat(k)| / rho_m")
    print("=" * 70)
    print()

    heuristic_data = {}

    for m in sorted(fourier_data.keys()):
        mags = fourier_data[m]
        rho = (9.0 / 10.0) ** (m - 1)
        K_test = min(100, len(mags))
        ratios = mags[:K_test] / rho

        print(f"  m={m}: |hat(k)|/rho_m for k=1..{K_test}")
        print(f"    mean ratio  = {np.mean(ratios):.6f}")
        print(f"    median ratio = {np.median(ratios):.6f}")
        print(f"    max ratio   = {np.max(ratios):.6f} at k={np.argmax(ratios)+1}")
        print(f"    min ratio   = {np.min(ratios):.6f} at k={np.argmin(ratios)+1}")

        # Show first 10 ratios
        print(f"    k=1..10: {', '.join(f'{r:.4f}' for r in ratios[:10])}")
        print()

        heuristic_data[m] = {
            "mean_ratio": float(np.mean(ratios)),
            "median_ratio": float(np.median(ratios)),
            "max_ratio": float(np.max(ratios)),
            "min_ratio": float(np.min(ratios)),
            "ratios_k1_20": [float(r) for r in ratios[:20]],
        }

    all_results["partF"] = heuristic_data

    # =================================================================
    # Part G: Dangerous frequencies
    # =================================================================
    print()
    print("=" * 70)
    print("  PART G: Dangerous frequencies")
    print("=" * 70)
    print()

    dangerous_data = {}

    for m in sorted(fourier_data.keys()):
        mags = fourier_data[m]
        K = len(mags)
        rho = (9.0 / 10.0) ** (m - 1)

        ratios = mags / rho
        sorted_idx = np.argsort(ratios)[::-1]

        print(f"  m={m}: Top-20 by |hat(k)|/rho_m")
        print(f"  {'k':>6} {'|hat(k)|':>14} {'|hat(k)|/rho':>14} {'||k*theta||':>14} {'|hat|/||k*th||':>14}")
        print(f"  {'-'*66}")

        top20 = []
        for rank in range(min(20, K)):
            idx = sorted_idx[rank]
            k = idx + 1
            mag = mags[idx]
            ratio = ratios[idx]
            norm_kth = frac_dist(k * theta)
            contrib = mag / norm_kth

            is_conv = ""
            for q in convergent_denoms:
                if abs(k - q) <= 1:
                    is_conv = f" <-- q={q}"

            print(
                f"  {k:>6} {mag:>14.6e} {ratio:>14.6f} "
                f"{norm_kth:>14.6e} {contrib:>14.6f}{is_conv}"
            )
            top20.append({
                "k": int(k),
                "mag": float(mag),
                "ratio": float(ratio),
                "norm_ktheta": float(norm_kth),
                "contribution": float(contrib),
            })

        print()
        dangerous_data[m] = top20

    all_results["partG"] = dangerous_data

    # =================================================================
    # Save results
    # =================================================================
    print("=" * 70)
    print("  SAVING RESULTS")
    print("=" * 70)

    with open(os.path.join(DATA_DIR, "exp36_results.json"), "w") as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"  Saved to {os.path.join(DATA_DIR, 'exp36_results.json')}")

    # =================================================================
    # Final assessment
    # =================================================================
    print()
    print("=" * 70)
    print("  FINAL ASSESSMENT")
    print("=" * 70)
    print()

    if sm_results:
        ms = sorted(sm_results.keys())
        sms = [sm_results[m]["S_m"] for m in ms]
        print("  S_m trend:")
        for i, m in enumerate(ms):
            trend = ""
            if i > 0:
                if sms[i] < sms[i - 1]:
                    trend = " (decreasing)"
                else:
                    trend = " (INCREASING)"
            print(f"    m={m}: S_m = {sms[i]:.4f}{trend}")

        if len(ms) >= 3:
            if all(sms[i] > sms[i + 1] for i in range(len(ms) - 1)):
                print("\n  VERDICT: S_m is monotonically decreasing. Strategy C' looks VIABLE.")
            elif sms[-1] < sms[0]:
                print("\n  VERDICT: S_m has overall downward trend. Strategy C' is PLAUSIBLE.")
            else:
                print("\n  VERDICT: S_m is NOT decreasing. Strategy C' faces obstacles.")

    print()
    print("  Literature note: Maynard's product formula")
    print("  |mu_B(Theta)| = prod_{j=0}^{k-1} |sum_{z_j in B_j} e(z_j g^j Theta)|")
    print("  applies to the DISCRETE exponential sum, not the circle integral.")
    print("  For Strategy C', the circle Fourier coefficients (computed here)")
    print("  are the relevant quantity.")
    print()
    print("=" * 70)
    print("  EXPERIMENT 36 COMPLETE")
    print("=" * 70)
