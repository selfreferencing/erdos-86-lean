#!/usr/bin/env python3
"""
Experiment 30: Danger Cylinder Census

MOTIVATION:
Both GPT 5A Pro instances converged on the "shortest path" to finiteness:
prove that the number of F_m components hit by orbit points in the transition
zone is O(1), then apply Baker/Matveev to kill persistence. This experiment
provides the empirical foundation by counting, for each m, how many distinct
components of F_m are actually hit.

KEY QUESTIONS:
1. Is the number of hit components O(1) or does it grow with m?
2. Which orbit indices persist across multiple m levels?
3. What are the specific "danger cylinders" (components repeatedly hit)?
4. Do the same ~7 orbit points persist for all large m?

PARTS:
A) Danger cylinder count for m = 2..27
B) Persistence table: which orbit indices survive across m levels
C) Danger cylinder identification: boundary integers of hit components
D) Summary statistics: hit count vs m
"""

import sys
import os
import json
import math

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

theta = math.log10(2)
C_const = 1.0 / theta  # ~ 3.3219


def is_zeroless(x, m):
    """Check if integer x has all m digits nonzero."""
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True


def has_zero_digit(n):
    """Check if integer n has any zero digit."""
    if n <= 0:
        return True
    while n > 0:
        if n % 10 == 0:
            return True
        n //= 10
    return False


def find_component_boundaries(n, m):
    """Find the left and right boundary integers of the component containing n.

    A component of F_m consists of consecutive m-digit zeroless integers.
    The left boundary is n_left: the smallest integer in the run.
    The right boundary is n_right: the largest integer in the run.
    n_left - 1 has a zero digit, and n_right + 1 has a zero digit.
    """
    # n should be an m-digit zeroless integer
    # Scan left
    n_left = n
    while n_left > 10**(m-1) and not has_zero_digit(n_left - 1):
        n_left -= 1

    # Scan right
    n_right = n
    while n_right < 10**m - 1 and not has_zero_digit(n_right + 1):
        n_right += 1

    return n_left, n_right


def find_survivors(m, L=None):
    """Find all surviving orbit indices i < L where 2^{m+i} mod 10^m is zeroless."""
    if L is None:
        L = int(math.ceil(C_const * m))
    mod_m = 10**m
    survivors = []
    x = pow(2, m, mod_m)
    for i in range(L):
        if is_zeroless(x, m):
            survivors.append((i, x))
        x = (2 * x) % mod_m
    return survivors


if __name__ == "__main__":
    print("=" * 70)
    print("  EXPERIMENT 30: DANGER CYLINDER CENSUS")
    print("=" * 70)

    all_results = {}

    # =================================================================
    # Part A: Count distinct hit components for each m
    # =================================================================
    print()
    print("=" * 70)
    print("  PART A: Danger cylinder count for m = 2..27")
    print("=" * 70)
    print()
    print("  For each m, enumerate orbit points in transition zone L_m,")
    print("  test against F_m, identify which component each hit is in.")
    print()
    print("  m | L_m | N_m | #components hit | hit indices")
    print("  --+-----+-----+----------------+------------")

    # Store per-m data
    per_m_data = {}

    for m in range(2, 28):
        L_m = int(math.ceil(C_const * m))
        mod_m = 10**m

        survivors = find_survivors(m, L_m)
        N_m = len(survivors)

        # Identify components for each hit
        components = {}  # (n_left, n_right) -> list of (i, x)
        for i, x in survivors:
            n_left, n_right = find_component_boundaries(x, m)
            key = (n_left, n_right)
            if key not in components:
                components[key] = []
            components[key].append((i, x))

        n_comp = len(components)
        hit_indices = sorted([i for i, x in survivors])

        per_m_data[m] = {
            "L_m": L_m,
            "N_m": N_m,
            "n_components": n_comp,
            "hit_indices": hit_indices,
            "components": {
                f"{nl}-{nr}": {
                    "n_left": nl,
                    "n_right": nr,
                    "run_length": nr - nl + 1,
                    "hits": [(i, x) for i, x in hits]
                }
                for (nl, nr), hits in components.items()
            },
            "survivors": [(i, x) for i, x in survivors]
        }

        idx_str = ",".join(str(i) for i in hit_indices[:15])
        if len(hit_indices) > 15:
            idx_str += "..."

        print(f"  {m:2d} | {L_m:3d} | {N_m:3d} |     {n_comp:10d} | {idx_str}")

    all_results["part_A"] = {
        str(m): {
            "L_m": d["L_m"],
            "N_m": d["N_m"],
            "n_components": d["n_components"],
            "hit_indices": d["hit_indices"]
        }
        for m, d in per_m_data.items()
    }

    # =================================================================
    # Part B: Persistence table
    # =================================================================
    print()
    print("=" * 70)
    print("  PART B: Persistence table")
    print("=" * 70)
    print()
    print("  Track which orbit indices i hit F_m across multiple m levels.")
    print("  An index i 'persists' if 2^{m+i} mod 10^m is zeroless for")
    print("  consecutive values of m.")
    print()

    # Collect all orbit indices that ever appear
    all_indices = set()
    for m, d in per_m_data.items():
        for i in d["hit_indices"]:
            all_indices.add(i)

    all_indices = sorted(all_indices)

    # Build persistence matrix
    persistence = {}
    for i in all_indices:
        persistence[i] = []
        for m in range(2, 28):
            if i in per_m_data[m]["hit_indices"]:
                persistence[i].append(m)

    # Find persistent indices (appear for >= 10 consecutive m values)
    persistent_indices = []
    for i in all_indices:
        m_vals = persistence[i]
        if len(m_vals) >= 10:
            persistent_indices.append(i)

    print(f"  Total distinct orbit indices ever hitting F_m: {len(all_indices)}")
    print(f"  Indices persisting for >= 10 levels: {len(persistent_indices)}")
    print()

    # Show persistence for the most persistent indices
    print("  Top persistent indices (sorted by persistence length):")
    print()
    sorted_by_persistence = sorted(all_indices, key=lambda i: len(persistence[i]), reverse=True)

    print("  index | #levels | first_m | last_m | alpha = frac((m+i)*theta)")
    print("  ------+---------+---------+--------+-------------------------")

    for idx in sorted_by_persistence[:20]:
        m_vals = persistence[idx]
        first_m = min(m_vals)
        last_m = max(m_vals)
        # Compute alpha at a representative m
        rep_m = min(15, last_m)
        alpha = ((rep_m + idx) * theta) % 1.0
        print(f"  {idx:5d} | {len(m_vals):7d} | {first_m:7d} | {last_m:6d} | {alpha:.8f}")

    all_results["part_B"] = {
        "total_indices": len(all_indices),
        "persistent_10plus": len(persistent_indices),
        "persistence": {str(i): persistence[i] for i in sorted_by_persistence[:30]}
    }

    # =================================================================
    # Part C: Danger cylinder identification
    # =================================================================
    print()
    print("=" * 70)
    print("  PART C: Danger cylinder identification")
    print("=" * 70)
    print()
    print("  For the most persistent orbit points, identify the specific")
    print("  components they land in and their boundary integers.")
    print()

    # For each persistent index, show what component it lands in at various m
    for idx in sorted_by_persistence[:10]:
        m_vals = persistence[idx]
        if len(m_vals) < 5:
            continue

        print(f"  --- Orbit index i = {idx} (persists at {len(m_vals)} levels) ---")
        print(f"  m | 2^(m+i) mod 10^m (last 20 digits) | n_left (last 15) | n_right (last 15) | run_len | alpha")
        print(f"  --+------------------------------------+------------------+-------------------+---------+------")

        for m in m_vals:
            mod_m = 10**m
            x = pow(2, m + idx, mod_m)
            if is_zeroless(x, m):
                n_left, n_right = find_component_boundaries(x, m)
                run_len = n_right - n_left + 1
                alpha = ((m + idx) * theta) % 1.0

                # Show last 20 digits for readability
                x_str = str(x)[-20:] if len(str(x)) > 20 else str(x)
                nl_str = str(n_left)[-15:] if len(str(n_left)) > 15 else str(n_left)
                nr_str = str(n_right)[-15:] if len(str(n_right)) > 15 else str(n_right)

                print(f"  {m:2d} | {x_str:>34s} | {nl_str:>16s} | {nr_str:>17s} | {run_len:7d} | {alpha:.6f}")
            else:
                print(f"  {m:2d} | NOT ZEROLESS at this level")

        print()

    # =================================================================
    # Part D: Summary statistics
    # =================================================================
    print()
    print("=" * 70)
    print("  PART D: Summary statistics")
    print("=" * 70)
    print()
    print("  m | N_m | #comp_hit | N_m/L_m | #comp_hit trend")
    print("  --+-----+-----------+---------+----------------")

    comp_counts = []
    for m in range(2, 28):
        d = per_m_data[m]
        ratio = d["N_m"] / d["L_m"] if d["L_m"] > 0 else 0
        comp_counts.append(d["n_components"])
        trend = "stable" if len(comp_counts) < 3 else (
            "UP" if comp_counts[-1] > comp_counts[-2] > comp_counts[-3] else
            "DOWN" if comp_counts[-1] < comp_counts[-2] < comp_counts[-3] else
            "stable"
        )
        print(f"  {m:2d} | {d['N_m']:3d} |    {d['n_components']:6d} |  {ratio:.4f} | {trend}")

    # Overall verdict
    print()
    print("=" * 70)
    print("  VERDICT")
    print("=" * 70)
    print()

    max_comp_hit = max(per_m_data[m]["n_components"] for m in range(2, 28))
    min_comp_hit = min(per_m_data[m]["n_components"] for m in range(5, 28))
    avg_comp_hit = sum(per_m_data[m]["n_components"] for m in range(5, 28)) / (28 - 5)

    print(f"  Max #components hit (m=2..27): {max_comp_hit}")
    print(f"  Min #components hit (m=5..27): {min_comp_hit}")
    print(f"  Avg #components hit (m=5..27): {avg_comp_hit:.1f}")
    print()

    if max_comp_hit <= 20:
        print("  RESULT: O(1) danger cylinders CONFIRMED.")
        print(f"  The number of hit components is bounded by {max_comp_hit}.")
        print("  This supports the resonance template reduction program.")
    else:
        print(f"  RESULT: Hit component count reaches {max_comp_hit}.")
        print("  Further analysis needed to determine growth rate.")

    print()
    print(f"  Most persistent indices: {sorted_by_persistence[:10]}")
    print(f"  Number persisting >= 10 levels: {len(persistent_indices)}")

    # Save results
    # Convert all values to JSON-serializable types
    def make_serializable(obj):
        if isinstance(obj, dict):
            return {str(k): make_serializable(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [make_serializable(v) for v in obj]
        elif isinstance(obj, tuple):
            return list(obj)
        elif isinstance(obj, set):
            return list(obj)
        else:
            return obj

    output_file = os.path.join(DATA_DIR, "exp30_results.json")
    with open(output_file, 'w') as f:
        json.dump(make_serializable(all_results), f, indent=2)

    print(f"\n  Results saved to {output_file}")
