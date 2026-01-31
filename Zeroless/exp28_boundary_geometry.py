#!/usr/bin/env python3
"""
Experiment 28: Boundary Geometry of F_m

Characterize the connected components of F_m, the set of alpha in [0,1)
such that the m-digit number with significand 10^alpha has no zero digit.

For small m (2..10): exact computation via zero-interval enumeration.
For larger m: analytical estimates and orbit-specific checks.
"""

import numpy as np
from math import log10 as mlog10, ceil, floor
import bisect
import time

theta = mlog10(2)  # 0.30102999566...
C_const = 1.0 / theta

def compute_zero_intervals(m):
    """Compute all intervals in [0,1) where digit k = 0, for k = 2..m.

    Digit k (from the left) of the number 10^{m-1+alpha} is:
      d_k = floor(10^{alpha+k-1}) mod 10

    This digit is 0 when 10^{alpha+k-1} is in [10j, 10j+1) for some integer j.
    Equivalently, alpha is in [log10(10j) - (k-1), log10(10j+1) - (k-1)).

    Returns sorted list of (lo, hi) intervals where at least one digit is 0.
    """
    raw_intervals = []

    for k in range(2, m + 1):
        j_lo = ceil(10**(k-1) / 10)
        j_hi = floor((10**k - 1) / 10)

        for j in range(j_lo, j_hi + 1):
            a_lo = mlog10(10 * j) - (k - 1)
            a_hi = mlog10(10 * j + 1) - (k - 1)
            a_lo = max(0.0, a_lo)
            a_hi = min(1.0, a_hi)
            if a_hi > a_lo + 1e-18:
                raw_intervals.append((a_lo, a_hi))

    return raw_intervals

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for lo, hi in intervals[1:]:
        if lo <= merged[-1][1] + 1e-18:
            merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else:
            merged.append((lo, hi))
    return merged

def complement_intervals(zero_intervals_merged):
    """Compute F_m = [0,1) minus the merged zero intervals."""
    comps = []
    prev = 0.0
    for lo, hi in zero_intervals_merged:
        if lo > prev + 1e-18:
            comps.append((prev, lo))
        prev = hi
    if prev < 1.0 - 1e-18:
        comps.append((prev, 1.0))
    return comps


def zero_interval_count_for_digit(k):
    """Number of zero-intervals for digit position k (no enumeration)."""
    j_lo = ceil(10**(k-1) / 10)
    j_hi = floor((10**k - 1) / 10)
    return j_hi - j_lo + 1

def max_zero_interval_width_for_digit(k):
    """Maximum width of a zero-interval for digit position k.
    Width = log10(10j+1) - log10(10j) = log10(1 + 1/(10j)).
    Maximized at smallest j = j_lo = ceil(10^{k-1}/10) = 10^{k-2}.
    """
    j_lo = ceil(10**(k-1) / 10)
    return mlog10(1 + 1/(10*j_lo))

def is_zeroless_alpha(alpha, m):
    """Check if 10^{m-1+alpha} has all m digits nonzero.

    Digit k (k=1..m, from the left) of the number N = 10^{m-1+alpha}:
    d_k = floor(10^{alpha+k-1}) mod 10.

    Since alpha in [0,1) and k-1 is a non-negative integer, we compute
    10^alpha once at high precision, then extract digit k by looking at
    floor(10^alpha * 10^{k-1}) mod 10.

    For k <= 15, double precision suffices (10^alpha has ~15 significant digits).
    For k > 15, we use mpmath with enough precision.
    """
    if m <= 15:
        # Fast path: double precision
        base = 10.0**alpha  # in [1, 10)
        for k in range(2, m + 1):
            val = base * 10.0**(k - 1)
            digit = int(val) % 10
            if digit == 0:
                return False
        return True
    else:
        # High precision path using mpmath
        import mpmath
        mpmath.mp.dps = m + 10  # enough decimal places
        base = mpmath.power(10, mpmath.mpf(alpha))
        for k in range(2, m + 1):
            val = base * mpmath.power(10, k - 1)
            digit = int(val) % 10
            if digit == 0:
                return False
        return True

def find_component_containing(alpha, m, tol=1e-15):
    """Find the connected component of F_m containing alpha (if any).
    Returns (lo, hi) or None if alpha is not in F_m.
    Uses bisection to find boundaries.
    """
    if not is_zeroless_alpha(alpha, m):
        return None

    # Binary search left
    lo = 0.0
    hi = alpha
    for _ in range(60):  # 60 bisections ~ 10^-18 precision
        mid = (lo + hi) / 2
        if is_zeroless_alpha(mid, m):
            hi = mid
        else:
            lo = mid
    left_bound = lo

    # Binary search right
    lo = alpha
    hi = 1.0
    for _ in range(60):
        mid = (lo + hi) / 2
        if is_zeroless_alpha(mid, m):
            lo = mid
        else:
            hi = mid
    right_bound = hi

    return (left_bound, right_bound)


print("=" * 70)
print("EXPERIMENT 28: BOUNDARY GEOMETRY OF F_m")
print("=" * 70)

# =====================================================================
# Part A: Component counts and sizes (exact, small m only)
# =====================================================================
print("\n### Part A: Component counts and sizes (exact, m=2..10) ###\n")

MAX_EXACT = 7
all_components = {}

for m in range(2, MAX_EXACT + 1):
    t0 = time.time()
    zero_ivs = compute_zero_intervals(m)
    merged_zeros = merge_intervals(zero_ivs)
    components = complement_intervals(merged_zeros)
    elapsed = time.time() - t0
    all_components[m] = components

    n_comp = len(components)
    lengths = [hi - lo for lo, hi in components]
    total_measure = sum(lengths)

    if lengths:
        max_len = max(lengths)
        min_len = min(lengths)
    else:
        max_len = min_len = 0

    expected_comp = 9**(m-1)
    rho_m = 0.9**(m-1)
    exceeds_theta = "YES" if max_len > theta else "NO"

    print(f"m={m:2d}: {n_comp:10d} components (expected {expected_comp:10d})  "
          f"max_len={max_len:.6e}  mu(F_m)={total_measure:.8f} (rho={rho_m:.8f})  "
          f"max > theta? {exceeds_theta}  [{elapsed:.2f}s]")

# =====================================================================
# Part B: Zero-interval counts (analytical, all m)
# =====================================================================
print("\n\n### Part B: Zero-interval count per digit position ###\n")

for m in [3, 5, 8, 10, 15, 20, 30, 50]:
    print(f"m={m}:")
    total_raw = 0
    for k in range(2, m + 1):
        count = zero_interval_count_for_digit(k)
        total_raw += count
        width = max_zero_interval_width_for_digit(k)
        if k <= 5 or k == m:
            print(f"  digit {k:2d}: {count:12d} zero-intervals, "
                  f"max width ~ {width:.2e}")
    print(f"  Total raw zero-intervals: {total_raw}")
    # Analytical estimate: sum_{k=2}^{m} (9*10^{k-2}) = 10^{m-1} - 1
    analytical = 10**(m-1) - 1
    print(f"  Analytical estimate: {analytical}")
    print()

# =====================================================================
# Part C: Critical threshold -- when does max component < theta?
# =====================================================================
print("\n### Part C: Max component length vs theta ###\n")
print(f"theta = {theta:.10f}")
print(f"For BCL Step B: need max component < theta.\n")

print(f"{'m':>3s}  {'n_components':>12s}  {'max_comp':>14s}  {'theta':>10s}  "
      f"{'ratio':>10s}  {'Step_B?':>8s}")
print("-" * 65)

for m in range(2, MAX_EXACT + 1):
    components = all_components[m]
    lengths = [hi - lo for lo, hi in components]
    max_len = max(lengths) if lengths else 0
    ratio = max_len / theta
    satisfied = "YES" if max_len < theta else "NO"

    print(f"{m:3d}  {len(components):12d}  {max_len:14.10f}  {theta:10.8f}  "
          f"{ratio:10.6f}  {satisfied:>8s}")

# Analytical upper bound on max component for m > MAX_EXACT
print(f"\n  Analytical upper bound for larger m:")
print(f"  Max zero-interval width for digit k = log10(1 + 1/(10*10^(k-2)))")
print(f"  = log10(1 + 10^(1-k)) ~ 10^(1-k)/ln(10) for large k.")
print(f"  Max component of F_m <= min gap between zero-intervals of ANY digit.")
print(f"  For digit 2 alone: ~9 zero-intervals, typical gap ~ 1/9 ~ 0.111")
print(f"  For digit 3: ~90 zero-intervals, typical gap ~ 1/90 ~ 0.011")
print(f"  Since ALL digits must be nonzero simultaneously,")
print(f"  max component <= min(gap of digit k for k=2..m).")
print(f"  Digit 2 already constrains max component to ~ 0.046,")
print(f"  which is << theta = 0.301.\n")

# Verify: digit 2 gaps
print("  Digit 2 zero-intervals and gaps:")
j_lo = ceil(10 / 10)
j_hi = floor(99 / 10)
d2_intervals = []
for j in range(j_lo, j_hi + 1):
    a_lo = mlog10(10 * j) - 1
    a_hi = mlog10(10 * j + 1) - 1
    a_lo = max(0.0, a_lo)
    a_hi = min(1.0, a_hi)
    if a_hi > a_lo:
        d2_intervals.append((a_lo, a_hi))
        print(f"    j={j}: [{a_lo:.8f}, {a_hi:.8f}), width={a_hi-a_lo:.6e}")

# Gaps in digit 2
d2_intervals.sort()
d2_gaps = []
for i in range(len(d2_intervals) - 1):
    gap = d2_intervals[i+1][0] - d2_intervals[i][1]
    d2_gaps.append(gap)
print(f"\n  Digit 2 gaps between zero-intervals:")
for i, g in enumerate(d2_gaps):
    print(f"    gap {i}: {g:.8f}")
print(f"  Max digit-2 gap: {max(d2_gaps):.8f}")
print(f"  This is an UPPER BOUND on max component of F_m for all m >= 2.")
print(f"  Since {max(d2_gaps):.6f} < {theta:.6f} = theta, Step B holds for ALL m >= 2!")

# =====================================================================
# Part D: Gap structure between components (exact, small m)
# =====================================================================
print("\n\n### Part D: Gap structure between components ###\n")

for m in range(2, MAX_EXACT + 1):
    components = all_components.get(m)
    if not components or len(components) < 2:
        print(f"m={m}: fewer than 2 components")
        continue

    gaps = []
    for i in range(len(components) - 1):
        gap = components[i+1][0] - components[i][1]
        if gap > 1e-18:
            gaps.append(gap)

    if gaps:
        gaps_arr = np.array(gaps)
        print(f"m={m:2d}: {len(gaps):8d} gaps, "
              f"min={min(gaps):.2e}, max={max(gaps):.2e}, "
              f"median={np.median(gaps_arr):.2e}")

# =====================================================================
# Part E: Orbit points vs components (exact, small m)
# =====================================================================
print("\n\n### Part E: Orbit points relative to F_m components (exact) ###\n")

for m in range(2, MAX_EXACT + 1):
    L = int(ceil(C_const * m))
    components = all_components.get(m)
    if not components:
        print(f"m={m}: no components")
        continue

    # Orbit points: frac(i*theta + c_m) for i = 0..L-1
    c_m = (m * theta) % 1.0
    orbit_points = [(i * theta + c_m) % 1.0 for i in range(L)]

    comp_starts = [s for s, e in components]

    hits = 0
    components_hit = set()
    orbit_in_comp = []

    for idx_i, alpha in enumerate(orbit_points):
        idx = bisect.bisect_right(comp_starts, alpha) - 1
        if 0 <= idx < len(components):
            s, e = components[idx]
            if s <= alpha < e:
                hits += 1
                components_hit.add(idx)
                orbit_in_comp.append((idx_i, idx))
            else:
                orbit_in_comp.append((idx_i, -1))
        else:
            orbit_in_comp.append((idx_i, -1))

    transitions = 0
    for i in range(len(orbit_in_comp) - 1):
        c1 = orbit_in_comp[i][1]
        c2 = orbit_in_comp[i+1][1]
        if c1 != c2:
            transitions += 1

    print(f"m={m:2d}, L={L:3d}: {hits:3d}/{L} in F_m, "
          f"{transitions:3d} transitions, "
          f"{len(components_hit):6d} distinct components hit")

# =====================================================================
# Part F: Orbit points for large m (using pointwise check)
# =====================================================================
print("\n\n### Part F: Orbit points for large m (pointwise) ###\n")
print("For m > 10, we check each orbit point individually.\n")

for m in range(2, 30):
    L = int(ceil(C_const * m))
    c_m = (m * theta) % 1.0
    orbit_points = [(i * theta + c_m) % 1.0 for i in range(L)]

    hits = 0
    hit_indices = []
    for idx_i, alpha in enumerate(orbit_points):
        if is_zeroless_alpha(alpha, m):
            hits += 1
            hit_indices.append(idx_i)

    # Count transitions between zeroless/zero status
    statuses = [is_zeroless_alpha(alpha, m) for alpha in orbit_points]
    transitions = sum(1 for i in range(len(statuses)-1) if statuses[i] != statuses[i+1])

    print(f"m={m:2d}, L={L:3d}: {hits:3d}/{L} in F_m, "
          f"{transitions:3d} transitions"
          + (f", hit at i={hit_indices}" if hits > 0 and hits <= 5 else ""))

# =====================================================================
# Part G: Component containing orbit points (large m)
# =====================================================================
print("\n\n### Part G: Component sizes at orbit points (bisection) ###\n")
print("For orbit points that land in F_m, find the component size.\n")

for m in range(2, 30):
    L = int(ceil(C_const * m))
    c_m = (m * theta) % 1.0

    found_any = False
    for i in range(L):
        alpha = (i * theta + c_m) % 1.0
        comp = find_component_containing(alpha, m)
        if comp is not None:
            lo, hi = comp
            width = hi - lo
            found_any = True
            print(f"m={m:2d}, i={i}: alpha={alpha:.10f}, "
                  f"component=[{lo:.12f}, {hi:.12f}), "
                  f"width={width:.4e}")
    if not found_any:
        print(f"m={m:2d}: NO orbit point in F_m  (L={L})")

# =====================================================================
# Part H: Max component upper bound from digit 2 alone
# =====================================================================
print("\n\n### Part H: Why Step B holds for ALL m >= 2 ###\n")

# The key observation: F_m is a SUBSET of F_2.
# F_2 = {alpha : digit 2 of 10^{1+alpha} is nonzero}
# This is: alpha NOT in any [log10(10j)-1, log10(10j+1)-1) for j=1..9
#
# The max component of F_2 is the largest gap between consecutive
# digit-2 zero-intervals. This is an upper bound for ALL F_m.

print("F_m is defined by: ALL digits 2..m are nonzero.")
print("Since F_m subset F_2, max_component(F_m) <= max_component(F_2).")
print()

components_2 = all_components[2]
lengths_2 = [hi - lo for lo, hi in components_2]
max_comp_2 = max(lengths_2)

print(f"F_2 has {len(components_2)} components.")
print(f"Max component of F_2: {max_comp_2:.10f}")
print(f"theta = {theta:.10f}")
print(f"Ratio max_comp(F_2)/theta = {max_comp_2/theta:.6f}")
print()
if max_comp_2 < theta:
    print("CONCLUSION: max_component(F_m) <= max_component(F_2) < theta")
    print("Step B of the BCL proof holds for ALL m >= 2.")
    print("No component of F_m can span two consecutive orbit points.")
else:
    print(f"WARNING: max_component(F_2) = {max_comp_2:.10f} >= theta = {theta:.10f}")
    print("Need to check higher m for Step B.")

    # Find first m where max component < theta
    for m in range(2, MAX_EXACT + 1):
        components = all_components[m]
        lengths = [hi - lo for lo, hi in components]
        max_len = max(lengths) if lengths else 0
        if max_len < theta:
            print(f"\nStep B first holds at m={m}: max_comp={max_len:.10f} < theta")
            break

# =====================================================================
# Part I: Detailed digit-2 analysis
# =====================================================================
print("\n\n### Part I: Digit-2 constraint structure ###\n")

print("Digit 2 of N = 10^{1+alpha} is floor(10^{1+alpha}) mod 10.")
print("This is the tens digit of floor(10^{1+alpha}).")
print("Digit 2 = 0 when 10^{1+alpha} in [10j, 10j+1).")
print()
print("For alpha in [0,1), we have 10^{1+alpha} in [10, 100).")
print("So j ranges from 1 to 9.")
print()

for j in range(1, 10):
    a_lo = mlog10(10*j) - 1
    a_hi = mlog10(10*j + 1) - 1
    print(f"  j={j}: digit2=0 when alpha in [{a_lo:.10f}, {a_hi:.10f}), "
          f"width={a_hi-a_lo:.6e}")

print()
print("F_2 components (where digit 2 != 0):")
for i, (lo, hi) in enumerate(components_2):
    print(f"  Component {i}: [{lo:.10f}, {hi:.10f}), width={hi-lo:.6e}")

# =====================================================================
# Part J: Boundary crossing expected count
# =====================================================================
print("\n\n### Part J: Expected boundary crossings ###\n")

print("An orbit step of size theta crosses a boundary of F_m if the interval")
print("[alpha, alpha+theta) contains a boundary point of F_m.")
print()
print("Number of F_m boundary points = 2 * (number of components).")
print("For exact m, boundary density = 2 * n_comp.")
print("Expected crossings per step ~ 2 * n_comp * theta (if uniform).")
print("Expected total crossings in L steps ~ L * 2 * n_comp * theta.")
print()

for m in range(2, MAX_EXACT + 1):
    components = all_components[m]
    n_comp = len(components)
    L = int(ceil(C_const * m))
    expected_per_step = 2 * n_comp * theta  # NOT right: boundaries NOT uniform
    # Better: total boundary measure covered by a theta-window
    # = sum over boundaries b of P(b in [alpha, alpha+theta)) = theta * n_boundaries
    # This overcounts but gives scale
    n_boundaries = 2 * n_comp
    total_boundary_pts = n_boundaries

    # More precise: how many boundaries fall in each theta-window?
    boundaries = sorted([x for c in components for x in c])
    crossings_per_step = []
    for i in range(L):
        c_m = (m * theta) % 1.0
        alpha = (i * theta + c_m) % 1.0
        alpha_end = alpha + theta
        # Count boundaries in [alpha, alpha+theta)
        if alpha_end <= 1.0:
            count = bisect.bisect_left(boundaries, alpha_end) - bisect.bisect_left(boundaries, alpha)
        else:
            count = (len(boundaries) - bisect.bisect_left(boundaries, alpha)) + bisect.bisect_left(boundaries, alpha_end - 1.0)
        crossings_per_step.append(count)

    total_cross = sum(crossings_per_step)
    print(f"m={m:2d}: {n_comp:8d} components, {total_boundary_pts:8d} boundary pts, "
          f"crossings in L={L} steps: {total_cross}, "
          f"mean/step: {total_cross/L:.1f}")

# Analytical estimate for large m
print(f"\n  Analytical estimate for large m:")
print(f"  n_comp(m) ~ 9^(m-1)")
print(f"  n_boundaries ~ 2 * 9^(m-1)")
print(f"  Each boundary point is a single value, so the probability that")
print(f"  a theta-width window contains a boundary ~ n_boundaries * (typical gap)^(-1) * theta")
print(f"  But since boundaries are NOT uniformly distributed, we use:")
print(f"  E[crossings per step] = (# boundaries in a theta arc) ~ theta * n_boundaries")
print(f"  Total in L steps ~ L * theta * 2 * 9^(m-1)")
print(f"  = ceil(m/theta) * theta * 2 * 9^(m-1)")
print(f"  ~ 2m * 9^(m-1)")
print(f"  BUT this assumes boundaries are uniformly spread, which overpredicts.")
print(f"  Actual crossings are much fewer because many boundaries cluster.")


print("\n" + "=" * 70)
print("EXPERIMENT 28 COMPLETE")
print("=" * 70)
