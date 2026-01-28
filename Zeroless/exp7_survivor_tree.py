#!/usr/bin/env python3
import sys
sys.set_int_max_str_digits(100000)
"""
EXPERIMENT 7: Survivor Tree Structure

Synthesis motivation: "Vertical correlation" (Section 8), cross-scale extinction (M4-B).

Build the survivor tree: at each level k, the set S_k of residues mod 4*5^{k-1}
that give k zeroless trailing digits. Track which survivors at level k "lift" to
level k+1 (which branches die, which survive).
"""

import numpy as np
import os
import json
from collections import defaultdict

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


def compute_survivor_set(k):
    """
    Compute S_k: set of residues n mod T_k (where T_k = 4*5^{k-1})
    such that 2^n mod 10^k has all nonzero digits.
    """
    period = 4 * (5 ** (k - 1))
    mod = 10 ** k
    survivors = set()

    for n in range(k, k + period):  # Need n >= k so 2^n has at least k digits mod 10^k meaningful
        r = pow(2, n, mod)
        s = str(r).zfill(k)
        if '0' not in s:
            survivors.add(n % period)

    return survivors


def test1_survivor_tree():
    """
    Build the survivor tree and analyze branching structure.
    """
    print("=" * 70)
    print("TEST 1: Survivor tree structure")
    print("=" * 70)

    max_k = 9

    prev_survivors = None
    prev_period = None

    tree_data = {}

    for k in range(1, max_k + 1):
        period = 4 * (5 ** (k - 1))
        survivors = compute_survivor_set(k)

        tree_data[k] = {
            'period': period,
            'survivor_count': len(survivors),
            'density': len(survivors) / period,
        }

        print(f"\n  k={k}: period={period}, survivors={len(survivors)}, "
              f"density={len(survivors)/period:.6f}, (9/10)^{k}={0.9**k:.6f}")

        if prev_survivors is not None:
            # Map survivors at level k to their residues mod prev_period (level k-1)
            lifts = 0
            deaths = 0
            orphans = 0

            # Each survivor at level k has a unique residue mod prev_period
            # Check which level k-1 survivors have children at level k
            parent_map = defaultdict(list)
            for s in survivors:
                parent = s % prev_period
                parent_map[parent].append(s)

            parents_with_children = set(parent_map.keys())
            parents_that_died = prev_survivors - parents_with_children

            # Branching analysis
            branch_counts = []
            for parent in prev_survivors:
                n_children = len(parent_map.get(parent, []))
                branch_counts.append(n_children)

            bc = np.array(branch_counts)
            print(f"    Level {k-1} -> {k}:")
            print(f"      Parents: {len(prev_survivors)}")
            print(f"      Parents with children: {len(parents_with_children & prev_survivors)}")
            print(f"      Parents that died: {len(parents_that_died)}")
            print(f"      Death rate: {len(parents_that_died)/len(prev_survivors):.4f}")
            print(f"      Branching: mean={bc.mean():.4f}, max={bc.max()}, "
                  f"min={bc.min()}")

            # Branch count distribution
            print(f"      Branch count distribution:")
            for b in range(0, max(bc) + 1):
                count = np.sum(bc == b)
                if count > 0:
                    print(f"        {b} children: {count} parents ({count/len(prev_survivors):.4f})")

            tree_data[k]['death_rate'] = len(parents_that_died) / len(prev_survivors)
            tree_data[k]['mean_branching'] = float(bc.mean())

        prev_survivors = survivors
        prev_period = period

    return tree_data


def test2_bottleneck_analysis():
    """
    Identify bottleneck levels where many branches die simultaneously.
    """
    print("\n" + "=" * 70)
    print("TEST 2: Bottleneck analysis")
    print("=" * 70)

    max_k = 9

    survivor_sets = {}
    for k in range(1, max_k + 1):
        survivor_sets[k] = compute_survivor_set(k)

    # For each transition k -> k+1, compute which survivors die
    print("\n  Death rates at each level transition:")
    print(f"  {'k->k+1':>8}  {'parents':>8}  {'died':>8}  {'death_rate':>12}  {'survived':>10}")
    print("  " + "-" * 55)

    for k in range(1, max_k):
        prev_period = 4 * (5 ** (k - 1))
        curr_survivors = survivor_sets[k]
        next_survivors = survivor_sets[k + 1]

        # Map next level survivors to their parents
        parent_map = defaultdict(int)
        for s in next_survivors:
            parent = s % prev_period
            parent_map[parent] += 1

        died = sum(1 for s in curr_survivors if parent_map.get(s, 0) == 0)
        survived = len(curr_survivors) - died

        print(f"  {k}->{k+1}:  {len(curr_survivors):8d}  {died:8d}  "
              f"{died/len(curr_survivors):12.6f}  {survived:10d}")


def test3_orbit_tracking():
    """
    For specific 2^n values, track which survivor branch they follow and where they exit.
    """
    print("\n" + "=" * 70)
    print("TEST 3: Orbit tracking through survivor tree")
    print("=" * 70)

    # Track several interesting n values
    test_ns = [86, 87, 95, 129, 1958, 7931, 100, 200, 500, 1000]

    max_k = 9

    for n in test_ns:
        print(f"\n  n={n}:")
        for k in range(1, max_k + 1):
            mod = 10 ** k
            r = pow(2, n, mod)
            s = str(r).zfill(k)
            is_surv = '0' not in s
            period = 4 * (5 ** (k - 1))
            residue = n % period

            if is_surv:
                print(f"    k={k}: 2^{n} mod 10^{k} = {r:>{k}} (residue {residue} mod {period}) -- SURVIVOR")
            else:
                # Find position of first zero
                first_zero = None
                for pos, ch in enumerate(s):
                    if ch == '0':
                        first_zero = k - pos  # position from right (1-indexed)
                        break
                print(f"    k={k}: 2^{n} mod 10^{k} = {r:>{k}} (zero at position {first_zero} from right) -- EXIT")
                break


def test4_narrow_waist():
    """
    Check if the survivor tree has a "narrow waist" -- a level where very few
    branches pass through, creating a bottleneck.
    """
    print("\n" + "=" * 70)
    print("TEST 4: Narrow waist analysis")
    print("=" * 70)

    max_k = 9

    # For each k, compute the minimal "waist" -- the smallest number of
    # independent survivor branches
    for k in range(1, max_k + 1):
        period = 4 * (5 ** (k - 1))
        survivors = compute_survivor_set(k)

        # Group survivors by their residue mod the PREVIOUS period
        if k > 1:
            prev_period = 4 * (5 ** (k - 2))
            groups = defaultdict(list)
            for s in survivors:
                groups[s % prev_period].append(s)

            group_sizes = [len(v) for v in groups.values()]
            print(f"\n  k={k}: {len(survivors)} survivors in {len(groups)} groups")
            print(f"    Group size distribution: mean={np.mean(group_sizes):.2f}, "
                  f"min={min(group_sizes)}, max={max(group_sizes)}")
            print(f"    Groups of size 1 (singleton): {sum(1 for g in group_sizes if g == 1)}")
            print(f"    Groups of size 0 (empty = dead): "
                  f"{len(compute_survivor_set(k-1)) - len(groups)}")
        else:
            print(f"\n  k={k}: {len(survivors)} survivors (root level)")


def test5_survivor_residue_patterns():
    """
    Look at the actual residues in the survivor set for patterns.
    """
    print("\n" + "=" * 70)
    print("TEST 5: Survivor residue patterns")
    print("=" * 70)

    for k in range(1, 6):
        period = 4 * (5 ** (k - 1))
        survivors = compute_survivor_set(k)
        survivor_list = sorted(survivors)

        print(f"\n  k={k}: period={period}, |S_k|={len(survivors)}")
        if len(survivor_list) <= 50:
            print(f"    Survivors: {survivor_list}")

        # Gap analysis
        gaps = [survivor_list[i + 1] - survivor_list[i] for i in range(len(survivor_list) - 1)]
        if gaps:
            gap_arr = np.array(gaps)
            print(f"    Gaps between survivors: mean={gap_arr.mean():.2f}, "
                  f"min={gap_arr.min()}, max={gap_arr.max()}, std={gap_arr.std():.2f}")

            # Gap distribution
            unique_gaps, gap_counts = np.unique(gap_arr, return_counts=True)
            if len(unique_gaps) <= 20:
                print(f"    Gap distribution:")
                for g, c in zip(unique_gaps, gap_counts):
                    print(f"      gap={g}: {c} times ({c/len(gaps):.4f})")

        # Residues mod 4
        mod4_dist = defaultdict(int)
        for s in survivors:
            mod4_dist[s % 4] += 1
        print(f"    Distribution mod 4: {dict(mod4_dist)}")

        # Residues mod 5
        if k >= 2:
            mod5_dist = defaultdict(int)
            for s in survivors:
                mod5_dist[s % 5] += 1
            print(f"    Distribution mod 5: {dict(mod5_dist)}")


if __name__ == "__main__":
    print("EXPERIMENT 7: SURVIVOR TREE STRUCTURE")
    print("=" * 70)

    tree_data = test1_survivor_tree()
    test2_bottleneck_analysis()
    test3_orbit_tracking()
    test4_narrow_waist()
    test5_survivor_residue_patterns()

    # Save results
    output = {str(k): v for k, v in tree_data.items()}
    with open(os.path.join(DATA_DIR, "exp7_results.json"), 'w') as f:
        json.dump(output, f, indent=2)

    print(f"\n{'='*70}")
    print("EXPERIMENT 7 COMPLETE")
    print(f"{'='*70}")
