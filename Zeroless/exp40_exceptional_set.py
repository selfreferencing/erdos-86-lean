#!/usr/bin/env python3
"""
Experiment 40: Structure of the Exceptional Set B_m

MOTIVATION:
The proof of the Erdos 86 Conjecture reduces to two steps:
  Step 1 (SOLVED): ||R_m||_2 = O(m * 0.95^m) -> 0
  Step 2 (OPEN): Show m*theta avoids B_m = {x : |R_m(x)| > 1/2} for large m

The APPROACH8 GPT response showed that the "desired theorem" (finite type +
summable measures => orbit avoids targets) is FALSE for general targets.
Known shrinking target theorems require monotone ball targets, not our B_m.

Whether Route C (new shrinking target theorem for digit-cylinder targets)
is feasible depends critically on the INTERVAL COMPLEXITY of B_m:
  - If B_m has O(poly(m)) connected components, shrinking target methods
    for intervals might be adaptable.
  - If B_m has O(9^m) components, Route C is likely infeasible.

This experiment computes:
A) R_m(x) on a fine grid for m = 2..8
B) The set B_m = {x : |R_m(x)| > 1/2}
C) Number of connected components of B_m
D) Total measure mu(B_m) and comparison to O(m^2 * 0.9^m) prediction
E) Distance from m*theta mod 1 to B_m
F) Histogram of R_m values
G) Whether B_m can be covered by O(poly(m)) intervals

KEY QUESTIONS:
1. How many connected components does B_m have?
2. Does mu(B_m) match the Chebyshev prediction 4 * ||R_m||_2^2?
3. How far is m*theta from B_m?
4. Is the interval complexity polynomial or exponential in m?
"""

import sys
import os
import json
import math
import time
import numpy as np
from decimal import Decimal, getcontext

# Set high precision for decimal arithmetic
getcontext().prec = 50

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

theta = math.log10(2)
C_const = 1.0 / theta  # ~ 3.32

results = {}


def is_zeroless_significand(x_frac, m):
    """
    Check if x_frac (in [0,1)) gives a zeroless significand at depth m.

    1_{F_m}(x) = 1 iff all digits d_1,...,d_{m-1} of floor(10^{m-1+x}) are nonzero.

    For efficiency, compute 10^{m-1+x} = 10^{m-1} * 10^x, take floor, check digits.
    """
    # Compute 10^{m-1+x}
    val = 10**(m - 1 + x_frac)
    n = int(val)
    # Check that n has m digits and all are nonzero
    s = str(n)
    if len(s) < m:
        return False
    # Check first m digits (the most significant ones)
    for c in s[:m]:
        if c == '0':
            return False
    return True


def compute_rho_m(m, N_grid=100000):
    """
    Compute the exact measure rho_m = mu(F_m) by counting on a fine grid.
    Also returns the grid values of 1_{F_m}.
    """
    xs = np.linspace(0, 1, N_grid, endpoint=False)
    indicator = np.zeros(N_grid)
    for i, x in enumerate(xs):
        indicator[i] = 1.0 if is_zeroless_significand(x, m) else 0.0
    rho = np.mean(indicator)
    return rho, indicator, xs


def compute_Rm(m, N_grid=100000):
    """
    Compute R_m(x) = sum_{j=0}^{L-1} (1_{F_m}(x + j*theta) - rho_m) on a grid.

    Returns: xs, Rm_values, rho_m, L_m
    """
    L_m = math.ceil(m / theta)

    # First compute rho_m
    rho_m, _, _ = compute_rho_m(m, N_grid)

    xs = np.linspace(0, 1, N_grid, endpoint=False)
    Rm = np.zeros(N_grid)

    for j in range(L_m):
        shift = (j * theta) % 1.0
        for i in range(N_grid):
            x_shifted = (xs[i] + shift) % 1.0
            val = 1.0 if is_zeroless_significand(x_shifted, m) else 0.0
            Rm[i] += val - rho_m

    return xs, Rm, rho_m, L_m


def find_Bm_components(xs, Rm, threshold=0.5):
    """
    Find connected components of B_m = {x : |R_m(x)| > threshold}.

    Returns: list of (start, end) intervals, total measure.
    """
    N = len(xs)
    dx = xs[1] - xs[0] if N > 1 else 1.0 / N

    in_Bm = np.abs(Rm) > threshold

    # Find connected components (runs of True in in_Bm)
    components = []
    start = None
    for i in range(N):
        if in_Bm[i] and start is None:
            start = i
        elif not in_Bm[i] and start is not None:
            components.append((xs[start], xs[i-1] + dx))
            start = None
    if start is not None:
        # Check wrap-around
        if in_Bm[0] and len(components) > 0:
            # Merge with first component (wrap-around)
            first_start = components[0][0]
            components[0] = (xs[start], 1.0 + first_start)
        else:
            components.append((xs[start], 1.0))

    total_measure = np.sum(in_Bm) * dx

    return components, total_measure, in_Bm


def distance_to_Bm(m_theta_mod1, xs, in_Bm):
    """
    Compute the distance from m*theta mod 1 to B_m.
    """
    N = len(xs)
    dx = xs[1] - xs[0]

    if not np.any(in_Bm):
        return float('inf')  # B_m is empty

    # Find closest point in B_m to m*theta
    Bm_indices = np.where(in_Bm)[0]
    Bm_xs = xs[Bm_indices]

    # Circular distance on [0,1)
    dists = np.minimum(np.abs(Bm_xs - m_theta_mod1),
                       np.minimum(np.abs(Bm_xs - m_theta_mod1 + 1),
                                  np.abs(Bm_xs - m_theta_mod1 - 1)))

    return np.min(dists)


print("=" * 70)
print("EXPERIMENT 40: Structure of the Exceptional Set B_m")
print("=" * 70)

# ======================================================================
# PART A: Compute R_m(x) and basic statistics
# ======================================================================
print("\n" + "=" * 70)
print("PART A: R_m(x) computation and basic statistics")
print("=" * 70)

# Grid size: trade off accuracy vs speed
# For m <= 5: use 200K grid points (fast enough)
# For m = 6: use 100K
# For m = 7-8: use 50K
grid_sizes = {2: 200000, 3: 200000, 4: 100000, 5: 100000, 6: 50000, 7: 30000, 8: 20000}

part_a_results = {}

for m in range(2, 9):
    t0 = time.time()
    N_grid = grid_sizes.get(m, 50000)
    print(f"\n--- m = {m}, L_m = {math.ceil(m/theta)}, grid = {N_grid} ---")

    xs, Rm, rho_m, L_m = compute_Rm(m, N_grid)

    elapsed = time.time() - t0

    # Basic statistics
    Rm_mean = np.mean(Rm)
    Rm_std = np.std(Rm)
    Rm_max = np.max(Rm)
    Rm_min = np.min(Rm)
    Rm_L2 = np.sqrt(np.mean(Rm**2))

    # Theoretical L2 bound: L * sqrt(rho_m)
    crude_L2_bound = L_m * math.sqrt(rho_m)

    # Expected value E[N_m] = L_m * rho_m
    E_Nm = L_m * rho_m

    # m*theta mod 1
    m_theta = (m * theta) % 1.0

    # R_m at the specific point x = m*theta
    idx_mtheta = int(m_theta * N_grid) % N_grid
    Rm_at_mtheta = Rm[idx_mtheta]

    print(f"  rho_m = {rho_m:.6f}")
    print(f"  L_m = {L_m}, E[N_m] = L_m*rho_m = {E_Nm:.4f}")
    print(f"  ||R_m||_2 = {Rm_L2:.6f}")
    print(f"  Crude L2 bound (L*sqrt(rho)) = {crude_L2_bound:.4f}")
    print(f"  Ratio ||R_m||_2 / crude_bound = {Rm_L2/crude_L2_bound:.4f}")
    print(f"  R_m range: [{Rm_min:.4f}, {Rm_max:.4f}]")
    print(f"  R_m at m*theta = {Rm_at_mtheta:.4f}")
    print(f"  m*theta mod 1 = {m_theta:.6f}")
    print(f"  Elapsed: {elapsed:.1f}s")

    part_a_results[m] = {
        'rho_m': rho_m,
        'L_m': L_m,
        'E_Nm': E_Nm,
        'Rm_L2': Rm_L2,
        'Rm_L2_squared': Rm_L2**2,
        'crude_L2_bound': crude_L2_bound,
        'ratio': Rm_L2 / crude_L2_bound,
        'Rm_min': Rm_min,
        'Rm_max': Rm_max,
        'Rm_at_mtheta': Rm_at_mtheta,
        'm_theta_mod1': m_theta,
        'N_grid': N_grid,
        'elapsed': elapsed
    }

results['part_a'] = part_a_results

# ======================================================================
# PART B: B_m = {x : |R_m(x)| > 1/2} - components and measure
# ======================================================================
print("\n" + "=" * 70)
print("PART B: Exceptional set B_m analysis")
print("=" * 70)

part_b_results = {}

for m in range(2, 9):
    t0 = time.time()
    N_grid = grid_sizes.get(m, 50000)

    print(f"\n--- m = {m} ---")

    xs, Rm, rho_m, L_m = compute_Rm(m, N_grid)

    # Find B_m with threshold 1/2
    components, total_measure, in_Bm = find_Bm_components(xs, Rm, threshold=0.5)

    # Also find B_m with threshold 1 (stricter)
    components_strict, measure_strict, in_Bm_strict = find_Bm_components(xs, Rm, threshold=1.0)

    # Distance from m*theta to B_m
    m_theta = (m * theta) % 1.0
    dist = distance_to_Bm(m_theta, xs, in_Bm)

    # Is m*theta in B_m?
    idx_mtheta = int(m_theta * N_grid) % N_grid
    mtheta_in_Bm = bool(in_Bm[idx_mtheta])

    # Chebyshev prediction: mu(B_m) <= 4 * ||R_m||_2^2
    Rm_L2_sq = np.mean(Rm**2)
    chebyshev_bound = 4 * Rm_L2_sq

    # Theoretical prediction: O(m^2 * 0.9^m)
    theoretical_pred = m**2 * 0.9**m

    n_components = len(components)
    n_components_strict = len(components_strict)

    print(f"  B_m (|R_m| > 0.5):")
    print(f"    Number of components: {n_components}")
    print(f"    Total measure: {total_measure:.6f}")
    print(f"    Chebyshev bound (4*||R||_2^2): {chebyshev_bound:.6f}")
    print(f"    m^2 * 0.9^m = {theoretical_pred:.6f}")
    print(f"    m*theta in B_m? {mtheta_in_Bm}")
    print(f"    Distance from m*theta to B_m: {dist:.6f}")

    print(f"  B_m (|R_m| > 1.0):")
    print(f"    Number of components: {n_components_strict}")
    print(f"    Total measure: {measure_strict:.6f}")

    # Histogram of |R_m| values
    abs_Rm = np.abs(Rm)
    pct_gt_half = np.mean(abs_Rm > 0.5) * 100
    pct_gt_1 = np.mean(abs_Rm > 1.0) * 100
    pct_gt_2 = np.mean(abs_Rm > 2.0) * 100

    print(f"  Distribution of |R_m|:")
    print(f"    |R_m| > 0.5: {pct_gt_half:.2f}%")
    print(f"    |R_m| > 1.0: {pct_gt_1:.2f}%")
    print(f"    |R_m| > 2.0: {pct_gt_2:.2f}%")

    elapsed = time.time() - t0

    part_b_results[m] = {
        'n_components_half': n_components,
        'measure_half': total_measure,
        'n_components_strict': n_components_strict,
        'measure_strict': measure_strict,
        'chebyshev_bound': chebyshev_bound,
        'theoretical_pred': theoretical_pred,
        'mtheta_in_Bm': mtheta_in_Bm,
        'dist_to_Bm': dist,
        'Rm_at_mtheta': float(Rm[idx_mtheta]),
        'pct_gt_half': pct_gt_half,
        'pct_gt_1': pct_gt_1,
        'pct_gt_2': pct_gt_2,
        'elapsed': elapsed
    }

results['part_b'] = part_b_results

# ======================================================================
# PART C: Component size distribution
# ======================================================================
print("\n" + "=" * 70)
print("PART C: Component size distribution")
print("=" * 70)

part_c_results = {}

for m in range(2, 9):
    N_grid = grid_sizes.get(m, 50000)

    xs, Rm, rho_m, L_m = compute_Rm(m, N_grid)
    components, total_measure, in_Bm = find_Bm_components(xs, Rm, threshold=0.5)

    if len(components) == 0:
        print(f"\n  m = {m}: B_m is EMPTY")
        part_c_results[m] = {'n_components': 0, 'sizes': [], 'max_size': 0, 'min_size': 0}
        continue

    # Component sizes
    sizes = [end - start for start, end in components]
    sizes.sort(reverse=True)

    print(f"\n  m = {m}: {len(components)} components")
    print(f"    Largest 5: {[f'{s:.6f}' for s in sizes[:5]]}")
    print(f"    Smallest 5: {[f'{s:.6f}' for s in sizes[-5:]]}")
    print(f"    Mean size: {np.mean(sizes):.6f}")
    print(f"    Max/min ratio: {max(sizes)/min(sizes):.2f}" if min(sizes) > 0 else "")

    part_c_results[m] = {
        'n_components': len(components),
        'sizes': sizes[:20],  # top 20 sizes
        'max_size': max(sizes),
        'min_size': min(sizes),
        'mean_size': float(np.mean(sizes))
    }

results['part_c'] = part_c_results

# ======================================================================
# PART D: R_m at m*theta - the critical evaluation
# ======================================================================
print("\n" + "=" * 70)
print("PART D: R_m at the critical point x = m*theta")
print("=" * 70)

part_d_results = {}

for m in range(2, 31):
    L_m = math.ceil(m / theta)
    m_theta = (m * theta) % 1.0

    # Compute R_m(m*theta) exactly: count how many j in {0,...,L-1} have
    # frac((m*theta + j*theta)) = frac((m+j)*theta) in F_m.
    # This is N_m(m*theta) - L_m * rho_m, where N_m(m*theta) counts
    # orbit points in F_m.

    # Actually, N_m(m*theta) = #{j : 0 <= j < L_m and frac((m+j)*theta) in F_m}
    # This is the count of n in {m, m+1, ..., m+L_m-1} with 2^n zeroless in first m digits.

    count = 0
    for j in range(L_m):
        n = m + j
        power = 2**n
        s = str(power)
        # Check first m digits
        if len(s) >= m:
            first_m = s[:m]
            if '0' not in first_m:
                count += 1

    # Use exact rho_m from prior computations if available
    # For speed, compute rho_m analytically: count m-digit zeroless integers
    # rho_m = 9^{m-1} * integral factor
    # Actually, let's just use the known approximation
    # More precise: count zeroless integers with m digits
    import itertools
    if m <= 8:
        zeroless_count = 9**(m-1)  # exact: 9 choices for each of m-1 non-leading digits, leading is 1-9
        # Wait: m-digit numbers have leading digit 1-9 and remaining m-1 digits 1-9
        # Actually total m-digit numbers: 9 * 10^{m-1}
        # Zeroless m-digit numbers: 9^m (each digit 1-9)
        # Wait: m-digit numbers go from 10^{m-1} to 10^m - 1
        # Leading digit: 1-9 (9 choices), remaining m-1 digits: 0-9 (10 choices each)
        # Zeroless: leading 1-9 (9), remaining 1-9 (9 each) = 9^m
        # rho_m = 9^m / (9 * 10^{m-1}) = 9^{m-1} / 10^{m-1} = (9/10)^{m-1}
        # But this is approximate. The exact rho_m involves the logarithmic measure.
        # Use the grid computation for m <= 8
        rho_m = part_a_results.get(m, {}).get('rho_m', (9/10)**(m-1))
    else:
        rho_m = (9/10)**(m-1)

    E_Nm = L_m * rho_m
    Rm_at_mtheta = count - E_Nm

    print(f"  m = {m:3d}: L_m = {L_m:4d}, N_m(m*theta) = {count:3d}, "
          f"E[N_m] = {E_Nm:7.3f}, R_m(m*theta) = {Rm_at_mtheta:+8.3f}, "
          f"|R_m| > 0.5? {'YES' if abs(Rm_at_mtheta) > 0.5 else 'no'}")

    part_d_results[m] = {
        'L_m': L_m,
        'N_m': count,
        'E_Nm': E_Nm,
        'Rm_at_mtheta': Rm_at_mtheta,
        'abs_Rm_gt_half': abs(Rm_at_mtheta) > 0.5,
        'm_theta_mod1': m_theta
    }

results['part_d'] = part_d_results

# ======================================================================
# PART E: Scaling of B_m complexity with m
# ======================================================================
print("\n" + "=" * 70)
print("PART E: Scaling of B_m complexity with m")
print("=" * 70)

print("\n  Summary table:")
print(f"  {'m':>3} {'#comp(>0.5)':>12} {'#comp(>1.0)':>12} {'mu(B_m)':>10} "
      f"{'Cheby bound':>12} {'m^2*0.9^m':>10} {'dist(m*th,B_m)':>15}")
print("  " + "-" * 80)

for m in range(2, 9):
    b = part_b_results.get(m, {})
    print(f"  {m:3d} {b.get('n_components_half', 0):12d} "
          f"{b.get('n_components_strict', 0):12d} "
          f"{b.get('measure_half', 0):10.6f} "
          f"{b.get('chebyshev_bound', 0):12.6f} "
          f"{b.get('theoretical_pred', 0):10.6f} "
          f"{b.get('dist_to_Bm', float('inf')):15.6f}")

# Check growth pattern
print("\n  Component count growth:")
comp_counts = [(m, part_b_results.get(m, {}).get('n_components_half', 0)) for m in range(2, 9)]
for m, c in comp_counts:
    # Is it polynomial or exponential?
    if m > 2 and comp_counts[0][1] > 0:
        ratio_to_prev = c / max(comp_counts[m-3][1], 1) if m > 2 else 0
        print(f"  m = {m}: {c} components (ratio to m-1: {ratio_to_prev:.2f})")

# ======================================================================
# PART F: Where does R_m exceed threshold? Correlation with F_m structure
# ======================================================================
print("\n" + "=" * 70)
print("PART F: R_m extremes and their location relative to F_m")
print("=" * 70)

for m in range(2, 7):
    N_grid = grid_sizes.get(m, 50000)
    xs, Rm, rho_m, L_m = compute_Rm(m, N_grid)

    # Find where |R_m| is maximized
    idx_max = np.argmax(np.abs(Rm))
    x_max = xs[idx_max]

    # Is the maximum in F_m?
    max_in_Fm = is_zeroless_significand(x_max, m)

    # What is N_m at the maximum?
    Nm_at_max = Rm[idx_max] + L_m * rho_m

    print(f"\n  m = {m}:")
    print(f"    Max |R_m| = {np.abs(Rm[idx_max]):.4f} at x = {x_max:.6f}")
    print(f"    N_m at max = {Nm_at_max:.1f} (E[N_m] = {L_m*rho_m:.1f})")
    print(f"    Max location in F_m? {max_in_Fm}")

    # Distribution: are B_m points clustered near F_m boundaries?
    in_Bm = np.abs(Rm) > 0.5
    if np.any(in_Bm):
        Bm_xs = xs[in_Bm]
        # Check how many B_m points are also in F_m
        Bm_in_Fm = sum(1 for x in Bm_xs[:1000] if is_zeroless_significand(x, m))
        Bm_total = min(len(Bm_xs), 1000)
        print(f"    B_m points in F_m: {Bm_in_Fm}/{Bm_total} = {Bm_in_Fm/Bm_total:.3f}")

# ======================================================================
# PART G: Summary and conclusions
# ======================================================================
print("\n" + "=" * 70)
print("PART G: Summary and Conclusions")
print("=" * 70)

print("\n  KEY QUESTION: Is B_m interval complexity polynomial or exponential?")
print()
for m in range(2, 9):
    n = part_b_results.get(m, {}).get('n_components_half', 0)
    n_strict = part_b_results.get(m, {}).get('n_components_strict', 0)
    print(f"  m = {m}: {n} components (threshold 0.5), "
          f"{n_strict} components (threshold 1.0)")

print("\n  KEY QUESTION: Does m*theta avoid B_m?")
print()
for m in range(2, 31):
    d = part_d_results.get(m, {})
    in_Bm = d.get('abs_Rm_gt_half', False)
    print(f"  m = {m:3d}: |R_m(m*theta)| = {abs(d.get('Rm_at_mtheta', 0)):7.3f}, "
          f"in B_m? {'YES' if in_Bm else 'no'}")

# Save results
print("\n  Saving results...")
# Convert for JSON serialization
json_results = {}
for key, val in results.items():
    json_results[key] = {}
    for k2, v2 in val.items():
        if isinstance(k2, int):
            k2 = str(k2)
        if isinstance(v2, dict):
            json_results[key][k2] = {
                str(k3): (float(v3) if isinstance(v3, (np.floating, np.integer))
                          else [float(x) for x in v3] if isinstance(v3, (list, np.ndarray))
                          else v3)
                for k3, v3 in v2.items()
            }
        else:
            json_results[key][k2] = v2

with open(os.path.join(DATA_DIR, "exp40_results.json"), 'w') as f:
    json.dump(json_results, f, indent=2, default=str)

print("  Results saved to data/exp40_results.json")
print("\n  DONE.")
