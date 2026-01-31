#!/usr/bin/env python3
"""
Experiment 14: Verify the Refresh Fraction delta = 3/23

The Transfer Lemma (Lemma 6) is proved with theta = 1/3 via the pure mod-8
transfer matrix. The refined theta = 20/69 ~ 0.2899 matches the empirical
theta_late ~ 0.289 and arises from a "uniform refresh" channel:

    T_eff = (1 - delta) P_0 + delta * Pi

where delta = 3/23 is the contraction factor from Lemma 4.

This experiment verifies:
1. The effective theta at each level (should approach 20/69)
2. The fraction of odd children that are "refreshed" (lose mod-8 correlation)
3. The connection between delta = 3/23 and the even-parent contribution
4. The mechanism: even parents produce parity-neutral children that are
   uniformly distributed mod 8, acting as the "refresh" channel.

Key insight being tested: The fraction delta = 3/23 comes from the fact
that even parents contribute 4E_m children to Z_{m+1} = 4E_m + 5O_m.
Among these, the odd children from even parents are uncorrelated with
the parent's mod-8 class (because even parents produce 2E+2O children
uniformly). This "refresh" fraction dilutes the mod-8 memory.
"""

import sys
import os
import json
import time
import math
import numpy as np
from collections import defaultdict

sys.set_int_max_str_digits(100000)
DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

M_MAX = 12


def part_A():
    """
    Compute the refresh fraction: what fraction of odd children at level m+1
    come from even parents vs odd parents?

    Even parents contribute children that are mod-8-uncorrelated (refresh).
    Odd parents contribute children that inherit mod-8 structure (transfer).
    """
    print("=" * 90)
    print("PART A: Source Decomposition of Odd Children")
    print("=" * 90)

    results = {}
    for m in range(2, M_MAX + 1):
        mod_m = 10 ** m
        mod_prev = 10 ** (m - 1)
        T_period = 4 * 5 ** (m - 1)
        min_val = mod_m // 10

        t0 = time.time()
        x = pow(2, m, mod_m)

        # Track odd children by parent type
        odd_from_even_parent = 0  # refresh channel
        odd_from_odd_parent = 0   # transfer channel

        # Also track mod-8 distribution of each source
        mod8_from_even = {1: 0, 3: 0, 5: 0, 7: 0}
        mod8_from_odd = {1: 0, 3: 0, 5: 0, 7: 0}

        Z_m = E_m = O_m = 0

        for i in range(T_period):
            if x >= min_val and '0' not in str(x):
                u_child = x >> m
                Z_m += 1
                if u_child % 2 == 0:
                    E_m += 1
                else:
                    O_m += 1
                    r_child = u_child % 8

                    # Determine parent type
                    parent = x % mod_prev
                    if parent >= mod_prev // 10 and '0' not in str(parent):
                        u_parent = parent >> (m - 1)
                        if u_parent % 2 == 0:
                            odd_from_even_parent += 1
                            mod8_from_even[r_child] += 1
                        else:
                            odd_from_odd_parent += 1
                            mod8_from_odd[r_child] += 1

            x = (x * 2) % mod_m

            if m >= 10 and i > 0 and i % (T_period // 5) == 0:
                el = time.time() - t0
                print(f"  [m={m}: {100*i//T_period}%, {el:.1f}s]",
                      file=sys.stderr, flush=True)

        elapsed = time.time() - t0
        total_odd = odd_from_even_parent + odd_from_odd_parent

        # Refresh fraction
        delta_empirical = odd_from_even_parent / total_odd if total_odd > 0 else 0

        results[m] = {
            'Z_m': Z_m,
            'E_m': E_m,
            'O_m': O_m,
            'odd_from_even': odd_from_even_parent,
            'odd_from_odd': odd_from_odd_parent,
            'mod8_from_even': mod8_from_even.copy(),
            'mod8_from_odd': mod8_from_odd.copy(),
            'delta_empirical': delta_empirical,
            'elapsed': elapsed
        }

        e_m = E_m / Z_m if Z_m > 0 else 0.5
        delta_predicted = (2 * e_m) / (2 * e_m + 3 * (1 - e_m))

        print(f"\nm={m:2d} | O_m={O_m:>10,} | elapsed={elapsed:.2f}s")
        print(f"  Odd from even parents: {odd_from_even_parent:>10,} "
              f"({100*delta_empirical:.2f}%)")
        print(f"  Odd from odd parents:  {odd_from_odd_parent:>10,} "
              f"({100*(1-delta_empirical):.2f}%)")
        print(f"  delta_empirical = {delta_empirical:.6f}")
        print(f"  delta_predicted (2e/(2e+3(1-e))) = {delta_predicted:.6f}")
        print(f"  3/23 = {3/23:.6f}")

    return results


def part_B(results):
    """
    Test whether odd children from even parents are uniformly distributed mod 8.
    This is the "refresh" hypothesis: even parents produce mod-8-neutral children.
    """
    print("\n" + "=" * 90)
    print("PART B: Mod-8 Uniformity of Refresh Channel")
    print("=" * 90)

    ms = sorted(results.keys())

    print(f"\n{'m':>3} {'E-src O(1)':>10} {'E-src O(3)':>10} "
          f"{'E-src O(5)':>10} {'E-src O(7)':>10} {'max_dev':>10}")
    print("-" * 65)

    for m in ms:
        r = results[m]
        counts = r['mod8_from_even']
        total = sum(counts.values())
        if total == 0:
            continue
        uniform = total / 4
        max_dev = max(abs(counts[k] - uniform) for k in [1, 3, 5, 7])
        rel_dev = max_dev / total

        ratios = {k: counts[k] / total for k in [1, 3, 5, 7]}
        print(f"{m:3d} {ratios[1]:10.4f} {ratios[3]:10.4f} "
              f"{ratios[5]:10.4f} {ratios[7]:10.4f} {rel_dev:10.4f}")

    print(f"\n{'m':>3} {'O-src O(1)':>10} {'O-src O(3)':>10} "
          f"{'O-src O(5)':>10} {'O-src O(7)':>10} {'max_dev':>10}")
    print("-" * 65)

    for m in ms:
        r = results[m]
        counts = r['mod8_from_odd']
        total = sum(counts.values())
        if total == 0:
            continue
        uniform = total / 4
        max_dev = max(abs(counts[k] - uniform) for k in [1, 3, 5, 7])
        rel_dev = max_dev / total

        ratios = {k: counts[k] / total for k in [1, 3, 5, 7]}
        print(f"{m:3d} {ratios[1]:10.4f} {ratios[3]:10.4f} "
              f"{ratios[5]:10.4f} {ratios[7]:10.4f} {rel_dev:10.4f}")


def part_C(results):
    """
    Derive the refresh fraction delta from first principles.

    At level m+1:
    - Z_{m+1} = 4*E_m + 5*O_m
    - Even parents contribute 4*E_m children total, of which 2*E_m are odd
    - Odd parents contribute 5*O_m children total, of which 3*O_m are odd
    - Total odd at m+1: O_{m+1} = 2*E_m + 3*O_m

    So the refresh fraction is:
        delta = (2*E_m) / (2*E_m + 3*O_m)
              = 2*e_m / (2*e_m + 3*(1-e_m))
              = 2*e_m / (3 - e_m)

    At e_m = 1/2: delta = 1 / (3 - 1/2) = 1/2.5 = 2/5

    Wait -- that's 2/5, not 3/23. Let me check the F5B derivation more carefully.
    """
    print("\n" + "=" * 90)
    print("PART C: Theoretical Refresh Fraction Derivation")
    print("=" * 90)

    ms = sorted(results.keys())

    print("\nDirect computation of delta = (odd children from even parents) / (all odd children)")
    print(f"\n{'m':>3} {'2*E_m':>12} {'3*O_m':>12} {'delta=2E/(2E+3O)':>18} {'empirical':>12}")
    print("-" * 65)

    for m in ms:
        r = results[m]
        E = r['E_m']
        O = r['O_m']
        # At level m, even parents contribute 2*E odd children (Lemma 2: 2E+2O from even)
        # Odd parents contribute 3*O odd children (average of 3 and 2 odd depending on v0)
        # Actually: Odd parents contribute 2 or 3 odd children.
        # With e_m ~ 1/2, p_m ~ 1/2: half contribute 2 odd, half contribute 3 odd
        # Average = 2.5 odd per odd parent, total = 2.5*O
        # But total odd children = O_{m+1} = 2E + (varies)
        # Let's just use the exact fiber formula
        # Even parents: 4 children each. Split: 2E + 2O. So 2*E_m odd children.
        # Odd parents: 5 children each. Split: either 3E+2O or 2E+3O.
        # Average odd children from odd parents: depends on p_m.
        # With fraction p_m having v0 even (3E+2O), and (1-p_m) having v0 odd (2E+3O):
        # Odd from odd = p_m*O*2 + (1-p_m)*O*3 = O*(3 - p_m)
        # We don't know p_m, so let's compute the actual even/odd parent contributions

        two_E = 2 * E
        from_odd = r['odd_from_odd']
        from_even = r['odd_from_even']
        delta_formula = two_E / (two_E + from_odd) if (two_E + from_odd) > 0 else 0
        delta_emp = r['delta_empirical']

        print(f"{m:3d} {two_E:12,} {from_odd:12,} {delta_formula:18.6f} {delta_emp:12.6f}")

    print("\n\nKey question: What is delta at e = 1/2?")
    print("Even parents produce 2 odd children each -> 2*E_m total")
    print("Odd parents produce 2 or 3 odd children each -> average 2.5*O_m (at p=1/2)")
    print("delta = 2E / (2E + 2.5O) = 2*(1/2) / (2*(1/2) + 2.5*(1/2)) = 1 / 2.25 = 4/9")
    print(f"4/9 = {4/9:.6f}")
    print(f"3/23 = {3/23:.6f}")
    print("\nSo delta is NOT 3/23. It's approximately 4/9.")
    print("The 3/23 = (1-e)/(5-e) at e=0.4 is the CONTRACTION FACTOR from the bias identity,")
    print("not the refresh fraction.")
    print("\nLet's compute what theta_eff would be with the actual delta:")
    delta_actual = 4/9
    theta_eff = (1 - delta_actual) / 3
    print(f"theta_eff = (1 - {delta_actual:.4f}) / 3 = {theta_eff:.6f}")
    print(f"Hmm, that gives {theta_eff:.4f}, not 0.289.")
    print("\nThe F5B model T = (1-delta)P + delta*Pi is too simple.")
    print("The actual mechanism is more subtle: even parents don't refresh to")
    print("exact uniform. Let's measure the effective theta directly.")


def part_D(results):
    """
    Measure the effective theta directly from the mod-8 deviation dynamics.

    For each level, compute the deviation vector d_m = p_m - uniform,
    then compute |P*d_{m-1}|/|d_{m-1}| to get the effective contraction.
    """
    print("\n" + "=" * 90)
    print("PART D: Effective Theta from Deviation Dynamics")
    print("=" * 90)

    # Load exp13 results for O_by_mod8
    exp13_path = os.path.join(DATA_DIR, "exp13_results.json")
    with open(exp13_path) as f:
        exp13 = json.load(f)

    ms = sorted([int(k) for k in exp13.keys() if k != '_meta'])

    # Compute deviation vectors
    devs = {}
    for m in ms:
        r = exp13[str(m)]
        O = r['O_m']
        if O == 0:
            continue
        p = np.array([r['O_by_mod8'][str(k)] / O for k in [1, 3, 5, 7]])
        d = p - 0.25
        devs[m] = d

    print(f"\n{'m':>3} {'|d_m|_2':>14} {'|d_m|/|d_{m-1}|':>18} "
          f"{'L(p_m)':>14} {'|L|/|L_prev|':>14}")
    print("-" * 70)

    prev_norm = None
    prev_L = None
    for m in ms:
        if m not in devs:
            continue
        d = devs[m]
        norm = np.linalg.norm(d)
        L = d[0] - d[2]  # O(1)/O - O(5)/O - (1/4 - 1/4) = (O(1)-O(5))/O

        ratio_norm = norm / prev_norm if prev_norm and prev_norm > 0 else 0
        ratio_L = abs(L) / abs(prev_L) if prev_L and abs(prev_L) > 0 else 0

        rn_str = f"{ratio_norm:.6f}" if prev_norm else "---"
        rl_str = f"{ratio_L:.6f}" if prev_L else "---"

        print(f"{m:3d} {norm:14.2e} {rn_str:>18} {L:14.2e} {rl_str:>14}")

        prev_norm = norm if norm > 0 else prev_norm
        prev_L = L if abs(L) > 0 else prev_L

    # Compute effective theta from successive ratios of |d|
    valid = [(m, np.linalg.norm(devs[m])) for m in ms
             if m in devs and np.linalg.norm(devs[m]) > 0 and m >= 3]

    if len(valid) >= 3:
        xv = np.array([v[0] for v in valid])
        yv = np.array([np.log(v[1]) for v in valid])
        slope, intercept = np.polyfit(xv, yv, 1)
        theta_eff = np.exp(slope)
        print(f"\nEffective theta from |d_m| fit (m >= 3): {theta_eff:.6f}")
        print(f"  1/3 = {1/3:.6f}")
        print(f"  20/69 = {20/69:.6f}")
        print(f"  exp11 theta_late = 0.2894")


def part_E(results):
    """
    Test the actual mixing mechanism more carefully.

    The pure mod-8 transfer gives theta = 1/3.
    The empirical theta ~ 0.289 < 1/3.
    The difference arises because the mod-8 transfer T operates only on
    odd-to-odd children, but the ACTUAL odd population at level m+1
    includes children from BOTH even and odd parents.

    The combined evolution for the odd mod-8 vector v_{m+1} is:
        v_{m+1} = T * v_m^{odd} + (contribution from even parents)

    where the even-parent contribution is approximately uniform (refresh).
    Let's measure this precisely.
    """
    print("\n" + "=" * 90)
    print("PART E: Combined Transfer + Refresh Dynamics")
    print("=" * 90)

    ms = sorted(results.keys())

    # For each level, decompose the mod-8 distribution into transfer + refresh
    print(f"\n{'m':>3} {'delta_eff':>12} {'dev(transfer)':>14} "
          f"{'dev(refresh)':>14} {'dev(combined)':>14}")
    print("-" * 65)

    for m in ms:
        r = results[m]
        # Combined mod-8 distribution
        O = r['O_m']
        if O == 0:
            continue

        # From-odd mod-8 distribution (transfer channel)
        odd_total = sum(r['mod8_from_odd'].values())
        if odd_total == 0:
            continue
        p_transfer = np.array([r['mod8_from_odd'][k] / odd_total for k in [1, 3, 5, 7]])

        # From-even mod-8 distribution (refresh channel)
        even_total = sum(r['mod8_from_even'].values())
        if even_total == 0:
            continue
        p_refresh = np.array([r['mod8_from_even'][k] / even_total for k in [1, 3, 5, 7]])

        # Combined
        p_combined = np.array([
            (r['mod8_from_odd'][k] + r['mod8_from_even'][k]) / O
            for k in [1, 3, 5, 7]])

        delta = even_total / O

        dev_transfer = np.linalg.norm(p_transfer - 0.25)
        dev_refresh = np.linalg.norm(p_refresh - 0.25)
        dev_combined = np.linalg.norm(p_combined - 0.25)

        print(f"{m:3d} {delta:12.4f} {dev_transfer:14.2e} "
              f"{dev_refresh:14.2e} {dev_combined:14.2e}")

    print("\nIf refresh channel is near-uniform, dev(refresh) ~ 0")
    print("Combined deviation ≈ (1-delta) * dev(transfer)")
    print("This extra (1-delta) factor per step gives theta_eff = (1-delta)/3")


def main():
    print(f"Experiment 14: Refresh Fraction Verification (m=2..{M_MAX})\n")
    t_start = time.time()

    results = part_A()
    part_B(results)
    part_C(results)
    part_D(results)
    part_E(results)

    # SUMMARY
    print("\n" + "=" * 90)
    print("SUMMARY")
    print("=" * 90)

    ms = sorted(results.keys())

    print(f"\n{'m':>3} {'delta_emp':>12} {'2E/(2E+from_odd)':>18}")
    print("-" * 40)
    for m in ms:
        r = results[m]
        print(f"{m:3d} {r['delta_empirical']:12.6f}")

    print(f"\nTheoretical predictions:")
    print(f"  Pure mod-8 transfer: theta = 1/3 = {1/3:.6f}")
    print(f"  F5B refined: theta = 20/69 = {20/69:.6f}")
    print(f"  exp11 measured: theta_late = 0.2894")

    elapsed = time.time() - t_start
    print(f"\nTotal time: {elapsed:.1f}s")

    # Save
    save_data = {}
    for m in ms:
        r = results[m]
        save_data[str(m)] = {
            'delta_empirical': r['delta_empirical'],
            'odd_from_even': r['odd_from_even'],
            'odd_from_odd': r['odd_from_odd']
        }
    path = os.path.join(DATA_DIR, "exp14_results.json")
    with open(path, 'w') as f:
        json.dump(save_data, f, indent=2)
    print(f"\nSaved to {path}")


if __name__ == '__main__':
    main()
