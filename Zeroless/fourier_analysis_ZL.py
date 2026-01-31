"""
Fourier Analysis of Zeroless Sets Z_L

Investigate whether the indicator function 1_{Z_L} has Fourier decay
despite having 9^L components.

For f ∈ [0,1), define Z_L = {f : digits 2,...,L of 10^f all in {1,...,9}}

The Fourier coefficient is:
  hat{1_{Z_L}}(k) = ∫_{Z_L} e^{2πikf} df
"""

import numpy as np
from collections import defaultdict


def get_zeroless_intervals(L):
    """
    Get all intervals in Z_L.

    For L digits, Z_L is union of 9^L intervals.
    Each interval corresponds to a choice of digits (d_1, ..., d_L) ∈ {1,...,9}^L

    The interval is [a, b) where:
      a = 0.d_1 d_2 ... d_L 0 0 0 ...
      b = 0.d_1 d_2 ... d_L 9 9 9 ...
    """
    intervals = []

    # Generate all L-digit sequences with digits in {1,...,9}
    def generate_sequences(pos, current):
        if pos == L:
            # Convert to interval [a, b)
            # a = 0.d_1 d_2 ... d_L (exact decimal)
            # b = 0.d_1 d_2 ... d_L + 10^(-L)
            a = sum(d * 10**(-i-1) for i, d in enumerate(current))
            b = a + 10**(-L)
            intervals.append((a, b))
            return

        for digit in range(1, 10):
            generate_sequences(pos + 1, current + [digit])

    generate_sequences(0, [])
    return sorted(intervals)


def fourier_coefficient_numerical(intervals, k):
    """
    Compute Fourier coefficient numerically:
      hat{f}(k) = ∫_0^1 f(x) e^{2πikx} dx

    For indicator function on union of intervals:
      = Σ_{[a,b) in intervals} ∫_a^b e^{2πikx} dx
      = Σ_{[a,b)} [e^{2πikx} / (2πik)]_{x=a}^{x=b}
      = Σ_{[a,b)} (e^{2πikb} - e^{2πika}) / (2πik)
    """
    if k == 0:
        # DC component = measure of the set
        return sum(b - a for a, b in intervals)

    total = 0
    for a, b in intervals:
        total += (np.exp(2j * np.pi * k * b) - np.exp(2j * np.pi * k * a)) / (2j * np.pi * k)

    return total


def fourier_coefficient_exact(intervals, k):
    """
    Exact formula for Fourier coefficient.

    For each interval [a, b):
      ∫_a^b e^{2πikx} dx = (e^{2πikb} - e^{2πika}) / (2πik)

    For digit-structured intervals, look for cancelation.
    """
    if k == 0:
        return sum(b - a for a, b in intervals)

    # Use high precision
    total = complex(0, 0)
    for a, b in intervals:
        # e^{2πikb} - e^{2πika} = e^{2πika}(e^{2πik(b-a)} - 1)
        width = b - a
        midpoint = (a + b) / 2

        # Using sinc function for numerical stability
        # ∫_a^b e^{2πikx} dx = (b-a) · e^{2πik·midpoint} · sinc(πk(b-a))
        # where sinc(x) = sin(x)/x

        omega = 2 * np.pi * k
        phase = np.exp(1j * omega * midpoint)

        if abs(omega * width) < 1e-10:
            # Use Taylor expansion for small arguments
            sinc_val = 1 - (omega * width)**2 / 6
        else:
            sinc_val = np.sin(omega * width / 2) / (omega * width / 2)

        total += width * phase * sinc_val

    return total


def analyze_fourier_decay(L_max=6, k_max=100):
    """
    Analyze Fourier decay for Z_L with L = 2, ..., L_max.
    """
    print("="*70)
    print("FOURIER ANALYSIS OF ZEROLESS SETS Z_L")
    print("="*70)

    for L in range(2, L_max + 1):
        print(f"\n{'='*70}")
        print(f"L = {L} (9^{L} = {9**L} intervals)")
        print(f"{'='*70}")

        intervals = get_zeroless_intervals(L)

        # DC component (measure)
        mu = sum(b - a for a, b in intervals)
        print(f"\nMeasure μ(Z_{L}) = {mu:.6f}")
        print(f"Expected (9/10)^{L-1} = {(9/10)**(L-1):.6f}")
        print(f"Ratio: {mu / (9/10)**(L-1):.6f}")

        # Fourier coefficients
        print(f"\nFourier coefficients:")
        print(f"{'k':<6} {'|hat(k)|':<15} {'|hat(k)|/μ':<15} {'Decay rate':<15}")
        print("-"*60)

        fourier_data = []

        for k in [1, 2, 3, 4, 5, 10, 20, 50, 100]:
            if k > k_max:
                break

            hat_k = fourier_coefficient_exact(intervals, k)
            mag = abs(hat_k)
            normalized = mag / mu if mu > 0 else 0

            # Decay rate: if |hat(k)| ~ k^{-α}, then α = -log(|hat(k)|) / log(k)
            if k > 1 and mag > 1e-15:
                prev_k = fourier_data[-1][0]
                prev_mag = fourier_data[-1][1]
                if prev_mag > 1e-15:
                    alpha = -np.log(mag / prev_mag) / np.log(k / prev_k)
                else:
                    alpha = float('nan')
            else:
                alpha = float('nan')

            fourier_data.append((k, mag, normalized, alpha))

            print(f"{k:<6} {mag:<15.6e} {normalized:<15.6f} {alpha:<15.3f}" if not np.isnan(alpha) else f"{k:<6} {mag:<15.6e} {normalized:<15.6f} {'—':<15}")

        # Check for power-law decay
        if len(fourier_data) >= 5:
            # Fit |hat(k)| ~ k^{-α}
            k_vals = np.array([d[0] for d in fourier_data[1:]])  # Skip k=0
            mag_vals = np.array([d[1] for d in fourier_data[1:]])

            # Filter out near-zero values
            valid = mag_vals > 1e-15
            if np.sum(valid) >= 3:
                log_k = np.log(k_vals[valid])
                log_mag = np.log(mag_vals[valid])

                # Linear fit: log|hat(k)| = log(C) - α·log(k)
                alpha_fit = -np.polyfit(log_k, log_mag, 1)[0]

                print(f"\nPower-law fit: |hat(k)| ~ k^{{-α}} with α ≈ {alpha_fit:.3f}")

                if alpha_fit > 1:
                    print(f"*** Fourier decay is FASTER than k^{{-1}} ***")
                else:
                    print(f"*** Fourier decay is SLOWER than k^{{-1}} ***")


def compare_to_random(L=3, k_max=20, n_trials=100):
    """
    Compare Fourier decay of Z_L to random unions of same measure.
    """
    print("\n" + "="*70)
    print(f"COMPARISON: Z_{L} vs Random Unions")
    print("="*70)

    intervals_ZL = get_zeroless_intervals(L)
    mu_ZL = sum(b - a for a, b in intervals_ZL)
    n_intervals = len(intervals_ZL)

    print(f"\nZ_{L}: {n_intervals} intervals, measure {mu_ZL:.6f}")

    # Generate random unions with same number of intervals and same measure
    print(f"\nComparing to {n_trials} random unions with same properties...")

    fourier_ZL = []
    fourier_random_mean = []
    fourier_random_std = []

    for k in range(1, k_max + 1):
        # Z_L coefficient
        hat_ZL = abs(fourier_coefficient_exact(intervals_ZL, k))
        fourier_ZL.append(hat_ZL)

        # Random coefficients
        random_hats = []
        for trial in range(n_trials):
            # Generate n_intervals random intervals with total measure mu_ZL
            # Simple method: random starts, equal widths
            width = mu_ZL / n_intervals
            starts = np.sort(np.random.uniform(0, 1 - width, n_intervals))
            random_intervals = [(s, s + width) for s in starts]

            hat_random = abs(fourier_coefficient_exact(random_intervals, k))
            random_hats.append(hat_random)

        fourier_random_mean.append(np.mean(random_hats))
        fourier_random_std.append(np.std(random_hats))

    # Print comparison
    print(f"\n{'k':<6} {'Z_L':<15} {'Random (mean)':<15} {'Random (std)':<15} {'Z_L / Random':<15}")
    print("-"*75)

    for i, k in enumerate(range(1, k_max + 1)):
        ratio = fourier_ZL[i] / fourier_random_mean[i] if fourier_random_mean[i] > 0 else float('inf')
        print(f"{k:<6} {fourier_ZL[i]:<15.6e} {fourier_random_mean[i]:<15.6e} {fourier_random_std[i]:<15.6e} {ratio:<15.3f}")

    # Summary
    mean_ratio = np.mean([fourier_ZL[i] / fourier_random_mean[i] for i in range(len(fourier_ZL)) if fourier_random_mean[i] > 0])
    print(f"\nMean ratio Z_L/Random: {mean_ratio:.3f}")

    if mean_ratio < 0.8:
        print("*** Z_L has BETTER Fourier decay than random unions ***")
    elif mean_ratio > 1.2:
        print("*** Z_L has WORSE Fourier decay than random unions ***")
    else:
        print("*** Z_L has SIMILAR Fourier decay to random unions ***")


if __name__ == "__main__":
    # Main Fourier analysis
    analyze_fourier_decay(L_max=5, k_max=100)

    # Comparison to random
    compare_to_random(L=3, k_max=20, n_trials=50)

    print("\n" + "="*70)
    print("CONCLUSION")
    print("="*70)
    print("""
If Fourier coefficients decay as |hat(k)| ~ k^{-α} with α > 1, this suggests
the set Z_L has better regularity than a generic union of intervals.

This could be key to proving ML1 - structured sets may have better
equidistribution properties despite having exponentially many components.
""")
