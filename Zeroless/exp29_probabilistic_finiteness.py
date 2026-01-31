#!/usr/bin/env python3
"""
Experiment 29: Probabilistic Finiteness Analysis

Can we prove N_m = 0 for large m using probabilistic arguments?

The Borel-Cantelli lemma gives: for a.e. alpha, N_m(alpha) = 0 for all large m,
since sum_m L_m * mu(F_m) < infinity. But we need to certify theta = log10(2)
specifically.

This experiment:
(A) Compute E[N_m] = L_m * mu(F_m) exactly and check when it drops below 1
(B) Compute the actual N_m for theta = log10(2) and measure the oversampling factor
(C) Compute pair correlations: P(orbit points i,j both in F_m) vs P(i in F_m)*P(j in F_m)
(D) Estimate E[N_m^2] and check if E[N_m^2]/E[N_m]^2 -> 1 (concentration)
(E) Test the "persistent wide component" hypothesis: does the oversampling come from
    a few specific orbit points that keep hitting the same wide components?
"""

import mpmath
from math import log10 as mlog10, ceil, floor
import numpy as np

mpmath.mp.dps = 50
theta = float(mpmath.log10(2))
C_const = 1.0 / theta


def is_zeroless_alpha(alpha, m):
    """Check if 10^{m-1+alpha} has all m digits nonzero."""
    if m <= 15:
        base = 10.0**alpha
        for k in range(2, m + 1):
            val = base * 10.0**(k - 1)
            digit = int(val) % 10
            if digit == 0:
                return False
        return True
    else:
        mpmath.mp.dps = m + 10
        base = mpmath.power(10, mpmath.mpf(alpha))
        for k in range(2, m + 1):
            val = base * mpmath.power(10, k - 1)
            digit = int(val) % 10
            if digit == 0:
                return False
        return True


print("=" * 70)
print("EXPERIMENT 29: PROBABILISTIC FINITENESS ANALYSIS")
print("=" * 70)

# =====================================================================
# Part A: E[N_m] = L_m * mu(F_m)
# =====================================================================
print("\n### Part A: Expected N_m under uniform distribution ###\n")

print(f"{'m':>3s}  {'L_m':>5s}  {'mu(F_m)':>12s}  {'E[N_m]':>12s}  "
      f"{'sum_E':>12s}  {'E<1?':>5s}")
print("-" * 55)

sum_E = 0.0
for m in range(2, 300):
    L_m = int(ceil(C_const * m))
    rho_m = 0.9**(m-1)
    E_Nm = L_m * rho_m
    sum_E += E_Nm
    below_1 = "YES" if E_Nm < 1 else "NO"

    if m <= 35 or m % 10 == 0 or (E_Nm < 1.5 and E_Nm > 0.5):
        print(f"{m:3d}  {L_m:5d}  {rho_m:12.6e}  {E_Nm:12.6e}  "
              f"{sum_E:12.6e}  {below_1:>5s}")

print(f"\nBorel-Cantelli sum = sum_m E[N_m] = {sum_E:.4f}")
print(f"This is finite, confirming: for a.e. alpha, N_m = 0 for all large m.")

# =====================================================================
# Part B: Actual N_m and oversampling factor
# =====================================================================
print("\n\n### Part B: Actual N_m for theta = log10(2) ###\n")

print(f"{'m':>3s}  {'L_m':>5s}  {'N_m':>5s}  {'E[N_m]':>12s}  "
      f"{'ratio':>10s}  {'oversampling':>12s}")
print("-" * 60)

actual_Nm = {}
orbit_hits = {}  # m -> list of hit indices

for m in range(2, 35):
    L_m = int(ceil(C_const * m))
    c_m = (m * theta) % 1.0

    hits = 0
    hit_indices = []
    for i in range(L_m):
        alpha = (i * theta + c_m) % 1.0
        if is_zeroless_alpha(alpha, m):
            hits += 1
            hit_indices.append(i)

    rho_m = 0.9**(m-1)
    E_Nm = L_m * rho_m
    ratio = hits / E_Nm if E_Nm > 1e-10 else float('inf')

    actual_Nm[m] = hits
    orbit_hits[m] = hit_indices

    print(f"{m:3d}  {L_m:5d}  {hits:5d}  {E_Nm:12.6e}  "
          f"{ratio:10.4f}  {'---' if E_Nm < 0.01 else f'{ratio:.2f}x'}")

# =====================================================================
# Part C: Pair correlations
# =====================================================================
print("\n\n### Part C: Pair correlations among orbit points ###\n")
print("For each pair (i,j) of orbit points that both hit F_m,")
print("check if they tend to hit the same component or different ones.\n")

for m in [5, 8, 10, 12, 15, 18, 20, 25, 29]:
    L_m = int(ceil(C_const * m))
    c_m = (m * theta) % 1.0

    # Get all hit statuses
    statuses = []
    for i in range(L_m):
        alpha = (i * theta + c_m) % 1.0
        statuses.append(is_zeroless_alpha(alpha, m))

    N_m_val = sum(statuses)
    if N_m_val < 2:
        print(f"m={m:2d}: N_m = {N_m_val}, fewer than 2 hits, skip")
        continue

    # Count pairs where both hit
    pair_hits = 0
    total_pairs = 0
    gap_distribution = []  # gaps between consecutive hits

    hit_indices_m = [i for i, s in enumerate(statuses) if s]

    for a in range(len(hit_indices_m)):
        for b in range(a+1, len(hit_indices_m)):
            pair_hits += 1
            gap = hit_indices_m[b] - hit_indices_m[a]
            gap_distribution.append(gap)

    # Under independence: P(both hit) = rho_m^2 * L_m * (L_m-1) / 2
    rho_m = 0.9**(m-1)
    E_pairs = rho_m**2 * L_m * (L_m - 1) / 2
    actual_pairs = pair_hits
    pair_ratio = actual_pairs / E_pairs if E_pairs > 1e-10 else float('inf')

    # Gap between consecutive hits
    consec_gaps = [hit_indices_m[i+1] - hit_indices_m[i]
                   for i in range(len(hit_indices_m)-1)]

    print(f"m={m:2d}: N_m={N_m_val}, pairs={actual_pairs}, E[pairs]={E_pairs:.2f}, "
          f"ratio={pair_ratio:.2f}")
    if consec_gaps:
        print(f"  Consecutive hit gaps: {consec_gaps}")
        print(f"  Min gap={min(consec_gaps)}, Max gap={max(consec_gaps)}, "
              f"Mean={np.mean(consec_gaps):.1f}")

# =====================================================================
# Part D: Second moment and concentration
# =====================================================================
print("\n\n### Part D: Second moment analysis ###\n")
print("E[N_m^2] = E[N_m] + 2 * sum_{i<j} P(both i,j in F_m)")
print("Under independence: E[N_m^2] = E[N_m] + E[N_m]*(E[N_m]-1) = E[N_m]^2")
print("Oversampling inflates E[N_m^2].\n")

print("We estimate E[N_m^2] by actual N_m^2, which is an upper bound for")
print("the expected value if we're at the maximum of the distribution.\n")

print(f"{'m':>3s}  {'N_m':>5s}  {'N_m^2':>8s}  {'E[N_m]':>12s}  {'E[N_m]^2':>12s}  "
      f"{'N_m^2/E^2':>10s}")
print("-" * 60)

for m in range(2, 35):
    N_val = actual_Nm.get(m, 0)
    L_m = int(ceil(C_const * m))
    rho_m = 0.9**(m-1)
    E_Nm = L_m * rho_m
    E_Nm_sq = E_Nm ** 2

    ratio = N_val**2 / E_Nm_sq if E_Nm_sq > 1e-15 else float('inf')

    print(f"{m:3d}  {N_val:5d}  {N_val**2:8d}  {E_Nm:12.6e}  {E_Nm_sq:12.6e}  "
          f"{ratio:10.4f}")

# =====================================================================
# Part E: Hit persistence across m
# =====================================================================
print("\n\n### Part E: Hit persistence -- do specific orbit points keep hitting? ###\n")
print("For each orbit index i, track across which m values it's a hit.\n")

# The orbit point alpha_i(m) = frac((i + m/theta)*theta) = frac(i*theta + m*theta)
# Note: i is relative to the start of the transition zone for digit count m.
# Different m values have different transition zones, so "orbit index i" at
# different m values corresponds to DIFFERENT actual n values.
#
# But we can track: for a fixed actual n, at which m values does it survive?
# n survives at m iff D(n)=m and 2^n is zeroless.
# But D(n) is fixed for each n, so a given n contributes to exactly one m.
#
# The persistent hits across m come from DIFFERENT n values that happen to
# have similar frac(n*theta).

# Let's instead look at it this way: for orbit index i at digit count m,
# the actual n is approximately floor(m/theta) + i.
# The orbit point is alpha = frac(n * theta) where n = floor(m/theta) + i.

print("Tracking actual n values that correspond to hits:\n")

n_to_m_hits = {}  # n -> list of m values where n corresponds to a hit

for m in range(2, 35):
    L_m = int(ceil(C_const * m))
    c_m = (m * theta) % 1.0
    n_start = int(ceil((m-1) / theta))  # smallest n with D(n) >= m

    for i in range(L_m):
        alpha = (i * theta + c_m) % 1.0
        n = n_start + i
        if is_zeroless_alpha(alpha, m):
            if n not in n_to_m_hits:
                n_to_m_hits[n] = []
            n_to_m_hits[n].append(m)

# Show n values that hit at multiple m (shouldn't happen since D(n) is unique)
# Actually, the orbit index i corresponds to n = n_start + i, and D(n) might
# not equal m. Let me reconsider.
#
# The transition zone for m is {n : D(n) = m}, i.e., floor((m-1)/theta) < n <= floor(m/theta).
# We're checking L_m orbit points starting from frac(m*theta), which correspond to
# n = m/theta + 0, m/theta + 1, ..., m/theta + L_m - 1 approximately.
#
# For the purpose of tracking, let's just look at frac(n*theta) values
# and see which ones persistently land in F_m for their respective m.

print("Alpha values of orbit hits (frac(n*theta)), sorted:\n")

alpha_hits = {}  # m -> list of alpha values that hit
for m in range(2, 35):
    L_m = int(ceil(C_const * m))
    c_m = (m * theta) % 1.0
    alphas = []
    for i in range(L_m):
        alpha = (i * theta + c_m) % 1.0
        if is_zeroless_alpha(alpha, m):
            alphas.append(alpha)
    alpha_hits[m] = sorted(alphas)

# Check: are specific alpha values persistent?
print("Top recurring alpha values across m:\n")

from collections import Counter
all_alphas = []
for m in range(10, 35):
    for a in alpha_hits[m]:
        # Round to 3 decimals for bucketing
        all_alphas.append(round(a, 3))

alpha_counts = Counter(all_alphas)
print("Most common alpha buckets (rounded to 3 decimals):")
for alpha_bucket, count in alpha_counts.most_common(20):
    m_list = []
    for m in range(10, 35):
        for a in alpha_hits[m]:
            if abs(a - alpha_bucket) < 0.001:
                m_list.append(m)
                break
    print(f"  alpha ~ {alpha_bucket:.3f}: appears in {count} m-values: {m_list}")

# =====================================================================
# Part F: Oversampling decomposition
# =====================================================================
print("\n\n### Part F: Oversampling decomposition ###\n")
print("Decompose N_m into contributions from 'wide' and 'narrow' components.\n")
print("A hit in a 'wide' component (width > 0.01) vs 'narrow' (width < 0.01):\n")

def find_component_width(alpha, m):
    """Quick estimate of component width by bisection."""
    if not is_zeroless_alpha(alpha, m):
        return 0.0

    # Left boundary
    lo, hi = 0.0, alpha
    for _ in range(50):
        mid = (lo + hi) / 2
        if is_zeroless_alpha(mid, m):
            hi = mid
        else:
            lo = mid
    left = lo

    # Right boundary
    lo, hi = alpha, 1.0
    for _ in range(50):
        mid = (lo + hi) / 2
        if is_zeroless_alpha(mid, m):
            lo = mid
        else:
            hi = mid
    right = hi

    return right - left


for m in [10, 15, 20, 25, 29]:
    L_m = int(ceil(C_const * m))
    c_m = (m * theta) % 1.0

    wide_hits = 0
    narrow_hits = 0
    widths = []

    for i in range(L_m):
        alpha = (i * theta + c_m) % 1.0
        if is_zeroless_alpha(alpha, m):
            w = find_component_width(alpha, m)
            widths.append(w)
            if w > 0.01:
                wide_hits += 1
            else:
                narrow_hits += 1

    total = wide_hits + narrow_hits
    rho_m = 0.9**(m-1)
    E_Nm = L_m * rho_m

    print(f"m={m:2d}: N_m={total}, wide={wide_hits}, narrow={narrow_hits}, "
          f"E[N_m]={E_Nm:.3f}")
    if widths:
        widths_sorted = sorted(widths, reverse=True)
        print(f"  Component widths: {', '.join(f'{w:.4e}' for w in widths_sorted[:8])}")
    print()

# =====================================================================
# Part G: When does E[N_m] < 1 and what is actual N_m there?
# =====================================================================
print("\n### Part G: Critical m where E[N_m] < 1 ###\n")

critical_m = None
for m in range(2, 500):
    L_m = int(ceil(C_const * m))
    rho_m = 0.9**(m-1)
    E_Nm = L_m * rho_m
    if E_Nm < 1 and critical_m is None:
        critical_m = m

print(f"E[N_m] first drops below 1 at m = {critical_m}")
if critical_m is not None:
    L_crit = int(ceil(C_const * critical_m))
    rho_crit = 0.9**(critical_m - 1)
    print(f"  L_{critical_m} = {L_crit}, mu(F_{critical_m}) = {rho_crit:.6e}")
    print(f"  E[N_{critical_m}] = {L_crit * rho_crit:.6f}")

    if critical_m <= 34:
        actual = actual_Nm.get(critical_m, "?")
        print(f"  Actual N_{critical_m} = {actual}")
else:
    print("  Not found in m <= 499!")

print(f"\nE[N_m] < 0.1 at m = ?:")
for m in range(2, 500):
    L_m = int(ceil(C_const * m))
    rho_m = 0.9**(m-1)
    E_Nm = L_m * rho_m
    if E_Nm < 0.1:
        print(f"  m = {m}: E[N_m] = {E_Nm:.6e}")
        break

print(f"\nE[N_m] < 0.01 at m = ?:")
for m in range(2, 500):
    L_m = int(ceil(C_const * m))
    rho_m = 0.9**(m-1)
    E_Nm = L_m * rho_m
    if E_Nm < 0.01:
        print(f"  m = {m}: E[N_m] = {E_Nm:.6e}")
        break

# =====================================================================
# Part H: Borel-Cantelli tail
# =====================================================================
print("\n\n### Part H: Borel-Cantelli tail sum ###\n")
print("sum_{m >= M} E[N_m] for various M:\n")

for M in [2, 10, 20, 27, 30, 40, 50, 80, 100, 150]:
    tail = sum(int(ceil(C_const * m)) * 0.9**(m-1) for m in range(M, 500))
    print(f"  sum_{{m >= {M:2d}}} E[N_m] = {tail:.4f}")

print("\nThe BC sum is finite = sum E[N_m] < infinity.")
print("For a.e. alpha, only finitely many m have N_m > 0.")
print("The tail sum gives: for alpha near log10(2), the expected number")
print("of surviving m-values beyond M is given by the tail sum.")


print("\n" + "=" * 70)
print("EXPERIMENT 29 COMPLETE")
print("=" * 70)
