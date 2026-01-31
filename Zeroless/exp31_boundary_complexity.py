#!/usr/bin/env python3
"""
Experiment 31: Boundary Point Complexity Analysis

MOTIVATION:
The "shortest path" to finiteness requires showing that persistent orbit
points approach boundary points of F_m with bounded prime-factorization
complexity. If boundary integers factor into {2,3,5,7} with bounded
exponents, Baker/Matveev gives a lower bound on |n*theta - log10(n_0)|
that contradicts the proximity required by persistence.

KEY QUESTIONS:
1. For each hit 2^{m+i} mod 10^m, what are the nearest boundary integers?
2. Do these boundary integers factor into small primes?
3. As m grows, do persistent orbit points approach boundaries with
   bounded or unbounded complexity?
4. Is the Baker/Matveev strategy feasible?

PARTS:
A) Boundary identification for all hits
B) Factorization of boundary integers
C) Complexity analysis: max prime factor and number of distinct primes
D) Persistence vs boundary structure
"""

import sys
import os
import json
import math

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

theta = math.log10(2)
C_const = 1.0 / theta


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
    """Find boundaries of component containing n."""
    n_left = n
    while n_left > 10**(m-1) and not has_zero_digit(n_left - 1):
        n_left -= 1
    n_right = n
    while n_right < 10**m - 1 and not has_zero_digit(n_right + 1):
        n_right += 1
    return n_left, n_right


def trial_factor(n, limit=100000):
    """Factor n using trial division up to limit.
    Returns (factors_dict, remainder).
    factors_dict maps prime -> exponent.
    remainder is the unfactored part (1 if fully factored).
    """
    if n <= 1:
        return {}, n
    factors = {}
    rem = n
    for p in range(2, min(limit + 1, int(math.isqrt(rem)) + 2)):
        if rem <= 1:
            break
        while rem % p == 0:
            factors[p] = factors.get(p, 0) + 1
            rem //= p
    return factors, rem


def smooth_check(n, primes={2, 3, 5, 7}):
    """Check if n is smooth with respect to the given primes.
    Returns (is_smooth, factors_dict, remainder).
    """
    factors = {}
    rem = n
    for p in sorted(primes):
        while rem % p == 0:
            factors[p] = factors.get(p, 0) + 1
            rem //= p
    return rem == 1, factors, rem


def factor_string(factors, remainder):
    """Human-readable factorization string."""
    parts = []
    for p in sorted(factors.keys()):
        e = factors[p]
        if e == 1:
            parts.append(str(p))
        else:
            parts.append(f"{p}^{e}")
    s = " * ".join(parts)
    if remainder > 1:
        if s:
            s += f" * {remainder}"
        else:
            s = str(remainder)
    return s if s else "1"


if __name__ == "__main__":
    print("=" * 70)
    print("  EXPERIMENT 31: BOUNDARY POINT COMPLEXITY ANALYSIS")
    print("=" * 70)

    all_results = {}

    # =================================================================
    # Part A: Boundary identification
    # =================================================================
    print()
    print("=" * 70)
    print("  PART A: Boundary identification for all hits")
    print("=" * 70)
    print()
    print("  For each hit at level m, find the left/right boundary of its")
    print("  component. The boundary integers are the first/last zeroless")
    print("  integers in the run containing the hit.")
    print()

    boundary_data = {}

    for m in range(2, 21):  # Cap at 20 for boundary scanning feasibility
        L_m = int(math.ceil(C_const * m))
        mod_m = 10**m

        x = pow(2, m, mod_m)
        for i in range(L_m):
            if is_zeroless(x, m):
                n_left, n_right = find_component_boundaries(x, m)
                alpha = ((m + i) * theta) % 1.0

                # Distance to nearest boundary
                alpha_left = math.log10(n_left) - (m - 1)  # alpha coord of left edge
                alpha_right = math.log10(n_right + 1) - (m - 1)  # alpha coord of right edge (gap starts here)
                dist_left = alpha - alpha_left
                dist_right = alpha_right - alpha

                key = f"m{m}_i{i}"
                boundary_data[key] = {
                    "m": m, "i": i,
                    "x": x, "alpha": alpha,
                    "n_left": n_left, "n_right": n_right,
                    "run_length": n_right - n_left + 1,
                    "dist_left": dist_left,
                    "dist_right": dist_right,
                    "nearest_boundary": "left" if dist_left < dist_right else "right",
                    "nearest_boundary_int": n_left - 1 if dist_left < dist_right else n_right + 1,
                    "min_dist": min(dist_left, dist_right)
                }

            x = (2 * x) % mod_m

    # Print summary
    print("  m | i | hit integer (last 15) | n_left-1 | n_right+1 | nearest | dist")
    print("  --+---+-----------------------+----------+-----------+---------+----")

    for key in sorted(boundary_data.keys(), key=lambda k: (boundary_data[k]["m"], boundary_data[k]["i"])):
        d = boundary_data[key]
        m, i = d["m"], d["i"]
        x_str = str(d["x"])[-15:]
        nb_int = d["nearest_boundary_int"]
        nb_str = str(nb_int)[-15:]
        side = d["nearest_boundary"]
        dist = d["min_dist"]
        nl1 = str(d["n_left"] - 1)[-10:]
        nr1 = str(d["n_right"] + 1)[-10:]

        if m <= 12:  # Print details for small m
            print(f"  {m:2d} | {i:2d} | {x_str:>21s} | {nl1:>8s} | {nr1:>9s} | {side:>7s} | {dist:.4e}")

    all_results["part_A"] = {
        k: {kk: vv for kk, vv in v.items() if kk != "x"}
        for k, v in boundary_data.items()
    }

    # =================================================================
    # Part B: Factorization of boundary integers
    # =================================================================
    print()
    print("=" * 70)
    print("  PART B: Factorization of boundary integers")
    print("=" * 70)
    print()
    print("  The boundary integers are n_left - 1 (has a zero digit, marks")
    print("  left edge of gap) and n_right + 1 (has a zero digit, marks")
    print("  right edge of gap).")
    print()
    print("  For Baker/Matveev, we need beta = log10(boundary_int) to be")
    print("  expressible as a linear form in log(2), log(3), log(5), log(7).")
    print("  This requires boundary_int to be {2,3,5,7}-smooth.")
    print()

    factorization_data = {}
    smooth_count = 0
    total_count = 0

    print("  m | i | boundary_int (last 20) | {2,3,5,7}-smooth? | factorization (partial)")
    print("  --+---+------------------------+-------------------+------------------------")

    for key in sorted(boundary_data.keys(), key=lambda k: (boundary_data[k]["m"], boundary_data[k]["i"])):
        d = boundary_data[key]
        m, i = d["m"], d["i"]
        nb_int = d["nearest_boundary_int"]

        is_smooth, smooth_factors, smooth_rem = smooth_check(nb_int)
        factors, full_rem = trial_factor(nb_int)
        total_count += 1

        if is_smooth:
            smooth_count += 1

        fdata = {
            "m": m, "i": i,
            "boundary_int": nb_int,
            "is_7smooth": is_smooth,
            "smooth_remainder": smooth_rem,
            "factors": factors,
            "full_remainder": full_rem,
            "max_prime": max(factors.keys()) if factors else 1,
            "n_distinct_primes": len(factors) + (1 if full_rem > 1 else 0)
        }
        factorization_data[key] = fdata

        nb_str = str(nb_int)[-20:]
        smooth_str = "YES" if is_smooth else "no"
        fact_str = factor_string(factors, full_rem)
        if len(fact_str) > 50:
            fact_str = fact_str[:47] + "..."

        if m <= 15:
            print(f"  {m:2d} | {i:2d} | {nb_str:>22s} | {smooth_str:>17s} | {fact_str}")

    print()
    print(f"  Total boundary integers examined: {total_count}")
    print(f"  {{2,3,5,7}}-smooth: {smooth_count} ({100*smooth_count/total_count:.1f}%)")

    all_results["part_B"] = {
        "total": total_count,
        "smooth_count": smooth_count,
        "smooth_pct": 100 * smooth_count / total_count if total_count > 0 else 0
    }

    # =================================================================
    # Part C: Complexity analysis
    # =================================================================
    print()
    print("=" * 70)
    print("  PART C: Max prime factor and complexity by m")
    print("=" * 70)
    print()
    print("  Track how boundary integer complexity grows with m.")
    print()

    # Group by m
    by_m = {}
    for key, fdata in factorization_data.items():
        m = fdata["m"]
        if m not in by_m:
            by_m[m] = []
        by_m[m].append(fdata)

    print("  m | #hits | #smooth | max_prime | avg_distinct_primes | max_distinct_primes")
    print("  --+-------+---------+-----------+---------------------+--------------------")

    complexity_by_m = {}
    for m in sorted(by_m.keys()):
        entries = by_m[m]
        n_hits = len(entries)
        n_smooth = sum(1 for e in entries if e["is_7smooth"])
        max_p = max(e["max_prime"] for e in entries) if entries else 0
        avg_np = sum(e["n_distinct_primes"] for e in entries) / n_hits if n_hits > 0 else 0
        max_np = max(e["n_distinct_primes"] for e in entries) if entries else 0

        complexity_by_m[m] = {
            "n_hits": n_hits, "n_smooth": n_smooth,
            "max_prime": max_p, "avg_distinct_primes": avg_np,
            "max_distinct_primes": max_np
        }

        print(f"  {m:2d} | {n_hits:5d} | {n_smooth:7d} | {max_p:9d} | {avg_np:19.1f} | {max_np:18d}")

    all_results["part_C"] = {str(m): v for m, v in complexity_by_m.items()}

    # =================================================================
    # Part D: Persistent boundaries
    # =================================================================
    print()
    print("=" * 70)
    print("  PART D: Do persistent orbit points approach structured boundaries?")
    print("=" * 70)
    print()
    print("  For orbit indices that persist across multiple m levels,")
    print("  track how their nearest boundary changes.")
    print()

    # Find indices that appear at multiple m levels
    index_persistence = {}
    for key, d in boundary_data.items():
        i = d["i"]
        if i not in index_persistence:
            index_persistence[i] = []
        index_persistence[i].append(d)

    # Sort by persistence length
    persistent_sorted = sorted(index_persistence.items(),
                               key=lambda x: len(x[1]), reverse=True)

    for idx, entries in persistent_sorted[:10]:
        if len(entries) < 2:
            continue
        entries.sort(key=lambda e: e["m"])
        print(f"  --- Orbit index i = {idx} (hits at {len(entries)} levels) ---")
        for e in entries:
            m = e["m"]
            nb = e["nearest_boundary_int"]
            dist = e["min_dist"]
            side = e["nearest_boundary"]
            fdata = factorization_data.get(f"m{m}_i{idx}", {})
            is_sm = fdata.get("is_7smooth", False)
            max_p = fdata.get("max_prime", 0)
            smooth_str = "SMOOTH" if is_sm else f"max_p={max_p}"
            nb_last = str(nb)[-20:]
            print(f"    m={m:2d}: boundary={nb_last:>20s} dist={dist:.4e} {smooth_str}")
        print()

    # =================================================================
    # Overall verdict
    # =================================================================
    print()
    print("=" * 70)
    print("  VERDICT")
    print("=" * 70)
    print()
    print(f"  Out of {total_count} boundary integers examined:")
    print(f"    - {smooth_count} are {{2,3,5,7}}-smooth ({100*smooth_count/total_count:.1f}%)")
    print(f"    - {total_count - smooth_count} have prime factors > 7")
    print()

    if smooth_count / total_count > 0.5:
        print("  Many boundary integers are smooth.")
        print("  Baker/Matveev MAY apply to the smooth cases.")
    else:
        print("  Most boundary integers are NOT {2,3,5,7}-smooth.")
        print("  The naive Baker/Matveev strategy (requiring smooth boundaries)")
        print("  faces a complexity barrier.")
        print()
        print("  However, the cluster forcing lemma (Strategy E) does NOT")
        print("  require smooth boundaries. It uses pigeonhole on component")
        print("  positions to force small |h*theta|, then applies Baker to")
        print("  theta = log10(2) directly (which IS a ratio of logs of")
        print("  algebraic numbers).")
        print()
        print("  RECOMMENDATION: Pivot from Strategy D (boundary Baker)")
        print("  to Strategy E (cluster forcing + direct Baker on theta).")

    # Save
    output_file = os.path.join(DATA_DIR, "exp31_results.json")
    serializable = {}
    for k, v in all_results.items():
        if isinstance(v, dict):
            serializable[k] = {str(kk): vv for kk, vv in v.items()}
        else:
            serializable[k] = v
    with open(output_file, 'w') as f:
        json.dump(serializable, f, indent=2, default=str)

    print(f"\n  Results saved to {output_file}")
