#!/usr/bin/env python3
"""
Experiment 12: Pair-to-Orbit Transfer Verification

The D-series identified theta = 2*sqrt(6)/(9+sqrt(65)) = 0.28712 as the spectral
gap ratio of the parity-augmented carry matrix M_aug. Independent verification
showed that M_aug describes the PAIR constraint, not the exact orbit transfer,
overcounting by ~1.9x. This experiment investigates the transfer argument:

  How does the pair-constraint spectral gap control the orbit's parity balance?

Sub-experiments:
  A. Pair-constraint parity balance from M_aug vs orbit parity balance
  B. Overcount correction: asymmetric factors (2 for even, 9/5 for odd)
  C. Carry-0 exact balance: structural explanation
  D. Minimal Markov state space search (u mod 2^k for k=1..5)
  E. Carry-path enumeration vs orbit survivors
  F. Direct spectral gap verification on orbit data
"""

import sys, os, json, time, math
import numpy as np

sys.set_int_max_str_digits(100000)
DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

M_MAX = 10  # T_10 = 7.8M

# Known matrices
M_TOT = np.array([[4, 4], [4, 5]], dtype=float)
M_AUG_1 = np.array([[3, 1, 3, 1],
                     [1, 3, 1, 3],
                     [1, 3, 3, 2],
                     [3, 1, 2, 3]], dtype=float)
M_AUG_2 = np.array([[1, 3, 0, 4],
                     [3, 1, 4, 0],
                     [4, 0, 5, 0],
                     [0, 4, 0, 5]], dtype=float)

# Exact spectral data
PF = (9 + math.sqrt(65)) / 2  # ~ 8.531
SQRT6 = math.sqrt(6)          # ~ 2.449
THETA = 2 * SQRT6 / (9 + math.sqrt(65))  # ~ 0.28712


def enumerate_orbit(m):
    """Enumerate orbit of 2^n mod 10^m, return list of survivors with metadata.

    Returns list of dicts with keys: x, u, u_parity, carry_out, digits
    """
    mod = 10 ** m
    T = 4 * 5 ** (m - 1)
    min_val = mod // 10
    two_m = 2 ** m

    survivors = []
    x = pow(2, m, mod)
    for i in range(T):
        if x >= min_val:
            s = str(x)
            if '0' not in s:
                u = x >> m  # x // 2^m
                # carry_out: what carry does doubling x produce at position m+1?
                # 2*x mod 10^{m+1} vs 2*x mod 10^m:
                # carry_out = (2*x) // 10^m mod 10 ... but more precisely:
                # The m-th digit of 2*x (0-indexed from right) determines carry
                # Actually: carry_out for the zeroless chain = floor((2*d_m + c_{m-1})/10)
                # But we can compute directly: the leading digit of x in the doubling
                # Simpler: carry_out = floor(2*x / 10^m) mod 2
                # Since x < 10^m, 2*x < 2*10^m, so floor(2*x/10^m) in {0, 1}
                carry_out = (2 * x) // mod
                survivors.append({
                    'x': x,
                    'u': u,
                    'u_parity': u % 2,  # 0=even, 1=odd
                    'carry_out': carry_out,
                    'u_mod4': u % 4,
                    'u_mod8': u % 8,
                    'u_mod16': u % 16,
                    'u_mod32': u % 32,
                })
        x = (x * 2) % mod

    return survivors


def part_A(all_survivors):
    """Compare pair-constraint parity balance (from M_aug) with orbit parity balance."""
    print("=" * 90)
    print("PART A: Pair-Constraint vs Orbit Parity Balance")
    print("=" * 90)

    # Orbit parity balance at each level
    print(f"\n{'m':>3} {'Z_m':>10} {'E_orbit':>10} {'O_orbit':>10} "
          f"{'e_orbit':>10} {'e_orbit-0.5':>12}")
    print("-" * 65)

    orbit_data = {}
    for m in sorted(all_survivors.keys()):
        surv = all_survivors[m]
        Z = len(surv)
        E = sum(1 for s in surv if s['u_parity'] == 0)
        O = Z - E
        e = E / Z if Z > 0 else 0
        orbit_data[m] = {'Z': Z, 'E': E, 'O': O, 'e': e}
        print(f"{m:3d} {Z:10,} {E:10,} {O:10,} {e:10.8f} {e-0.5:>+12.2e}")

    # Pair-constraint parity balance from M_aug iteration
    # Start from orbit carry/parity vector at m=1
    print(f"\n--- Pair-constraint prediction from M_aug #1 ---")
    print(f"{'m':>3} {'e_pair':>12} {'e_orbit':>12} {'diff':>12} "
          f"{'|diff|/theta^m':>14}")
    print("-" * 60)

    for m in sorted(all_survivors.keys()):
        if m < 2:
            continue
        surv_prev = all_survivors[m-1]
        # Actual orbit (carry, parity) vector at m-1
        v = np.zeros(4)
        for s in surv_prev:
            idx = 2 * s['carry_out'] + s['u_parity']
            v[idx] += 1

        # Apply M_aug to predict level m
        v_pred = M_AUG_1 @ v
        # Predicted E and O (from indices 0,2 = even and 1,3 = odd)
        E_pred = v_pred[0] + v_pred[2]
        O_pred = v_pred[1] + v_pred[3]
        Z_pred = E_pred + O_pred
        e_pred = E_pred / Z_pred if Z_pred > 0 else 0

        e_orb = orbit_data[m]['e']
        diff = e_pred - e_orb
        ratio = abs(diff) / (THETA ** m) if THETA ** m > 0 else 0
        print(f"{m:3d} {e_pred:12.8f} {e_orb:12.8f} {diff:>+12.2e} {ratio:14.4f}")

    return orbit_data


def part_B(all_survivors):
    """Overcount correction analysis: asymmetric factors for even vs odd parents."""
    print("\n" + "=" * 90)
    print("PART B: Overcount Correction Analysis")
    print("=" * 90)

    print(f"\n{'m':>3} {'Z_m+1':>10} {'carry_pred':>12} {'ratio':>8} "
          f"{'E_factor':>10} {'O_factor':>10} {'E/O_asym':>10}")
    print("-" * 75)

    for m in sorted(all_survivors.keys()):
        if m + 1 not in all_survivors:
            continue
        surv = all_survivors[m]
        Z_next = len(all_survivors[m + 1])

        # Carry-level count: even parents contribute 8, odd contribute 9
        E_m = sum(1 for s in surv if s['u_parity'] == 0)
        O_m = len(surv) - E_m

        carry_total = 8 * E_m + 9 * O_m  # Total carry transitions
        orbit_total = 4 * E_m + 5 * O_m  # Orbit children (= Z_{m+1})

        ratio = carry_total / orbit_total if orbit_total > 0 else 0

        # Per-type factors
        E_factor = 8 / 4  # always 2.0
        O_factor = 9 / 5  # always 1.8

        # Asymmetry in parity ratio
        # If pair-constraint has E_pair/Z_pair = alpha, then orbit has:
        # E_orbit/Z_orbit = (E_pair/2) / (E_pair/2 + O_pair * 5/9)
        # Since E_pair + O_pair = Z_pair, and E_pair = alpha * Z_pair:
        # E_orbit/Z_orbit = (alpha/2) / (alpha/2 + (1-alpha)*5/9)
        # = (9*alpha) / (9*alpha + 10*(1-alpha))
        # = (9*alpha) / (10 - alpha)

        e_pair = E_m / len(surv) if surv else 0.5  # orbit e IS the pair e
        # Actually the orbit parity balance is the source; the question is
        # whether the carry matrix preserves it

        print(f"{m:3d} {Z_next:10,} {carry_total:12,} {ratio:8.4f} "
              f"{E_factor:10.4f} {O_factor:10.4f} {E_factor/O_factor:10.4f}")

    # The key computation: if pair-constraint E/Z = 1/2 + delta,
    # what is orbit E/Z?
    print("\n--- Overcount correction formula ---")
    print("If pair E/Z = 1/2 + delta, orbit E/Z depends on the conversion.")
    print("Even parents: 8 carry -> 4 orbit children (factor 2)")
    print("Odd parents: 9 carry -> 5 orbit children (factor 9/5)")
    print()
    print("Carry transitions by type:")
    print("  From E parent: 8 transitions (4 to E-child, 4 to O-child) [exact 50/50]")
    print("  From O parent: 9 transitions (distribution varies)")
    print()
    print("Orbit children by type:")
    print("  From E parent: 4 children (2 E, 2 O) [exact 50/50]")
    print("  From O parent: 5 children (2+p E, 3-p O) [depends on p]")
    print()
    print("The RATIO E/O is the same in orbit and carry if:")
    print("  E_carry/O_carry = E_orbit/O_orbit")
    print("  This holds iff the overcount factor is the same for E and O children.")
    print("  From E parents: factor = 8/4 = 2 for both E-children and O-children")
    print("  From O parents: factor for E-child = ?, for O-child = ?")
    print()

    # Detailed transition analysis: from odd parents, how many carry transitions
    # go to E-children vs O-children, and how does this compare with orbit?
    for m in range(2, min(M_MAX, 8) + 1):
        surv_m = all_survivors[m]
        surv_prev = all_survivors[m - 1]

        # Build parent-child mapping
        mod_m = 10 ** m
        mod_prev = 10 ** (m - 1)

        # Map child x -> parent (x mod 10^{m-1}) and check parentage
        parent_set = {s['x'] for s in surv_prev}
        child_by_parent_type = {'E': {'E': 0, 'O': 0}, 'O': {'E': 0, 'O': 0}}

        for s in surv_m:
            parent_x = s['x'] % mod_prev
            if parent_x in parent_set:
                # Find parent type
                p_u = parent_x >> (m - 1)
                p_type = 'E' if p_u % 2 == 0 else 'O'
                c_type = 'E' if s['u_parity'] == 0 else 'O'
                child_by_parent_type[p_type][c_type] += 1

        E_par = sum(1 for s in surv_prev if s['u_parity'] == 0)
        O_par = len(surv_prev) - E_par

        print(f"\nm={m}: E_parents={E_par}, O_parents={O_par}")
        for pt in ['E', 'O']:
            n_par = E_par if pt == 'E' else O_par
            if n_par > 0:
                ecc = child_by_parent_type[pt]['E']
                occ = child_by_parent_type[pt]['O']
                total = ecc + occ
                print(f"  {pt}-parent -> E-child: {ecc:>8,} "
                      f"({ecc/n_par:.4f}/parent)  "
                      f"O-child: {occ:>8,} ({occ/n_par:.4f}/parent)  "
                      f"total: {total/n_par:.4f}/parent")


def part_C(all_survivors):
    """Carry-0 exact balance verification and structural explanation."""
    print("\n" + "=" * 90)
    print("PART C: Carry-0 Exact Balance Verification")
    print("=" * 90)

    print(f"\n{'m':>3} {'Z_c0':>8} {'E_c0':>8} {'O_c0':>8} {'E-O_c0':>8} "
          f"{'Z_c1':>8} {'E_c1':>8} {'O_c1':>8} {'E-O_c1':>8} "
          f"{'c0_frac':>8}")
    print("-" * 90)

    for m in sorted(all_survivors.keys()):
        surv = all_survivors[m]
        # Split by carry-out
        c0 = [s for s in surv if s['carry_out'] == 0]
        c1 = [s for s in surv if s['carry_out'] == 1]
        E_c0 = sum(1 for s in c0 if s['u_parity'] == 0)
        O_c0 = len(c0) - E_c0
        E_c1 = sum(1 for s in c1 if s['u_parity'] == 0)
        O_c1 = len(c1) - E_c1
        c0_frac = len(c0) / len(surv) if surv else 0

        print(f"{m:3d} {len(c0):8,} {E_c0:8,} {O_c0:8,} {E_c0-O_c0:>+8,} "
              f"{len(c1):8,} {E_c1:8,} {O_c1:8,} {E_c1-O_c1:>+8,} "
              f"{c0_frac:8.6f}")

    # Structural analysis: Why is carry-0 balanced?
    print("\n--- Structural Analysis ---")
    print("Carry-out = 0 means 2*x < 10^m, i.e., x < 5*10^{m-1}.")
    print("The leading digit d_m of x satisfies d_m <= 4.")
    print("For x = 2^m * u mod 10^m with u in (Z/5^m Z)*:")
    print("  carry-out = floor(2x / 10^m) = floor(2*u*2^m / 10^m)")
    print("  = floor(2*u / 5^m) since 2^m / 10^m = 1/5^m")
    print("  = floor(2u / 5^m)")
    print("Since u < 5^m, carry-out = 0 iff 2u < 5^m, i.e., u < 5^m/2.")
    print("The even units u < 5^m/2 and odd units u < 5^m/2 are being counted.")
    print()

    # Direct verification: among survivors with u < 5^m/2, count E vs O
    print("Verification: among survivors, u < 5^m/2 iff carry-out = 0")
    for m in range(1, min(M_MAX, 6) + 1):
        surv = all_survivors[m]
        five_m = 5 ** m
        half = five_m / 2
        u_small = [s for s in surv if s['u'] < half]
        c0 = [s for s in surv if s['carry_out'] == 0]
        match = len(u_small) == len(c0) and all(
            s in [{'x': t['x']} for t in c0] for s in [{'x': t['x']} for t in u_small]
        )
        # Simpler check
        u_small_set = {s['x'] for s in u_small}
        c0_set = {s['x'] for s in c0}
        print(f"  m={m}: |u<5^m/2| = {len(u_small)}, |carry-0| = {len(c0)}, "
              f"match = {u_small_set == c0_set}")

    # Now the key question: among units u < 5^m/2 that are zeroless survivors,
    # is E = O? Why?
    print("\n--- Why carry-0 has E = O ---")
    print("Consider the involution u -> 5^m - u on (Z/5^m Z)*.")
    print("This maps u to 5^m - u, which flips parity (even <-> odd).")
    print("If this involution preserves the survivor set AND maps carry-0 to carry-0,")
    print("then E_c0 = O_c0.")
    print()

    for m in range(1, min(M_MAX, 6) + 1):
        surv = all_survivors[m]
        five_m = 5 ** m
        mod = 10 ** m
        two_m = 2 ** m

        c0_survs = [s for s in surv if s['carry_out'] == 0]
        # Check involution u -> 5^m - u
        surv_u_set = {s['u'] for s in surv}
        c0_u_set = {s['u'] for s in c0_survs}

        involution_preserves_surv = all(
            (five_m - u) % five_m in surv_u_set for u in surv_u_set
            if (five_m - u) % five_m != 0
        )
        involution_preserves_c0 = all(
            (five_m - u) % five_m in c0_u_set for u in c0_u_set
            if (five_m - u) % five_m != 0
        )

        print(f"  m={m}: involution preserves survivors? {involution_preserves_surv}, "
              f"preserves carry-0? {involution_preserves_c0}")

    # Alternative involution: u -> u + 5^m (which would be identity mod 5^m)
    # Try: u -> -u mod 5^m (multiplicative inverse of sign)
    print("\n--- Try involution u -> -u mod 5^m ---")
    for m in range(1, min(M_MAX, 6) + 1):
        surv = all_survivors[m]
        five_m = 5 ** m
        surv_u_set = {s['u'] for s in surv}
        c0_u_set = {s['u'] for s in surv if s['carry_out'] == 0}

        neg_preserves_surv = all((-u) % five_m in surv_u_set for u in surv_u_set)
        neg_preserves_c0 = all((-u) % five_m in c0_u_set for u in c0_u_set)

        # -u has opposite parity to u iff 5^m is even (it's not -- 5^m is odd)
        # So -u mod 5^m = 5^m - u, which has parity opposite to u since 5^m is odd
        print(f"  m={m}: -u preserves survivors? {neg_preserves_surv}, "
              f"preserves carry-0? {neg_preserves_c0}")

    # Try: u -> u + 1 (shift by 1, flips parity)
    print("\n--- Digit-level analysis of carry-0 balance ---")
    for m in range(1, min(M_MAX, 5) + 1):
        surv = all_survivors[m]
        five_m = 5 ** m
        mod = 10 ** m
        two_m = 2 ** m

        c0_survs = [s for s in surv if s['carry_out'] == 0]
        print(f"\n  m={m}: carry-0 survivors ({len(c0_survs)}):")

        # Show digits and u values
        for s in c0_survs[:20]:
            x = s['x']
            digits = [int(d) for d in str(x)]
            leading = digits[0]
            print(f"    x={x:>{m+2}}, u={s['u']:>6}, parity={'E' if s['u_parity']==0 else 'O'}, "
                  f"leading_digit={leading}")

        if len(c0_survs) > 20:
            print(f"    ... ({len(c0_survs) - 20} more)")


def part_D(all_survivors):
    """Minimal Markov state space search: u mod 2^k for k=1..5."""
    print("\n" + "=" * 90)
    print("PART D: Minimal Markov State Space Search")
    print("=" * 90)

    for k in range(1, 6):
        mod_k = 2 ** k
        n_states = 2 * mod_k  # carry in {0,1}, u mod 2^k
        print(f"\n--- k={k}: tracking (carry, u mod {mod_k}), {n_states} states ---")

        # For each level m >= 2, compute the empirical transition matrix
        # Parent state -> child state (normalized by parent count)
        matrices = {}
        for m in range(2, min(M_MAX, 9) + 1):
            surv_m = all_survivors[m]
            surv_prev = all_survivors[m - 1]
            if not surv_prev:
                continue

            mod_m = 10 ** m
            mod_prev = 10 ** (m - 1)

            # Map child -> parent
            parent_x_to_state = {}
            for s in surv_prev:
                c = s['carry_out']
                r = s['u'] % mod_k
                state = c * mod_k + r
                parent_x_to_state[s['x']] = state

            # Count transitions
            T = np.zeros((n_states, n_states))
            parent_count = np.zeros(n_states)

            for s in surv_m:
                parent_x = s['x'] % mod_prev
                if parent_x in parent_x_to_state:
                    p_state = parent_x_to_state[parent_x]
                    c_state = s['carry_out'] * mod_k + (s['u'] % mod_k)
                    T[c_state, p_state] += 1
                    parent_count[p_state] += 1

            # Normalize to get per-parent transition rates
            T_norm = np.zeros_like(T)
            for j in range(n_states):
                if parent_count[j] > 0:
                    T_norm[:, j] = T[:, j] / parent_count[j]

            matrices[m] = T_norm

        # Check stability: compare matrices at different levels
        if len(matrices) >= 3:
            levels = sorted(matrices.keys())
            print(f"  Transition matrix stability across levels {levels[0]}..{levels[-1]}:")

            # Compute max deviation between consecutive levels
            for i in range(1, len(levels)):
                m1, m2 = levels[i-1], levels[i]
                diff = np.max(np.abs(matrices[m2] - matrices[m1]))
                print(f"    max|T({m2}) - T({m1})| = {diff:.6f}")

            # Compare first and last
            diff_fl = np.max(np.abs(matrices[levels[-1]] - matrices[levels[0]]))
            print(f"    max|T({levels[-1]}) - T({levels[0]})| = {diff_fl:.6f}")

            # Eigenvalues of the average matrix
            avg_T = sum(matrices[m] for m in levels) / len(levels)
            evals = np.linalg.eigvals(avg_T)
            evals_sorted = sorted(evals, key=lambda x: -abs(x))
            print(f"  Average matrix eigenvalues (by modulus):")
            for j, ev in enumerate(evals_sorted[:min(6, len(evals_sorted))]):
                print(f"    lambda_{j} = {ev:.6f}  (|lambda| = {abs(ev):.6f})")
            if len(evals_sorted) > 1:
                ratio = abs(evals_sorted[1]) / abs(evals_sorted[0])
                print(f"  |lambda_1/lambda_0| = {ratio:.6f}  "
                      f"(theta_predicted = {THETA:.6f})")

            # Check if any level has a notably different matrix
            is_markov = diff_fl < 0.01
            print(f"  Approximately Markov? {'YES' if is_markov else 'NO'} "
                  f"(threshold: max_diff < 0.01)")


def part_E(all_survivors):
    """Carry-path enumeration vs orbit survivors."""
    print("\n" + "=" * 90)
    print("PART E: Carry-Path Enumeration vs Orbit Survivors")
    print("=" * 90)

    # Count admissible carry paths of length m starting from c=0
    # An admissible path: sequence of (d_1, c_1, d_2, c_2, ..., d_m, c_m)
    # where d_i in {1,...,9}, (2*d_i + c_{i-1}) mod 10 != 0,
    # c_i = floor((2*d_i + c_{i-1})/10), starting with c_0 = 0.

    # Also count with parity tracking.

    # Use matrix power: number of paths of length m from c=0 is
    # (M_tot^m * e_0) where e_0 = [1, 0] (start from carry 0)

    print(f"\n{'m':>3} {'carry_paths':>14} {'Z_orbit':>12} {'ratio':>10} "
          f"{'(8.531/4.5)^m':>14}")
    print("-" * 65)

    e0 = np.array([1.0, 0.0])
    ratio_expected = PF / 4.5

    for m in range(1, min(M_MAX, 10) + 1):
        # Carry paths from c=0 after m steps
        v = np.linalg.matrix_power(M_TOT.astype(int), m) @ np.array([1, 0])
        carry_paths = int(v[0] + v[1])

        Z_orbit = len(all_survivors.get(m, []))

        ratio = carry_paths / Z_orbit if Z_orbit > 0 else 0
        expected = ratio_expected ** m

        print(f"{m:3d} {carry_paths:14,} {Z_orbit:12,} {ratio:10.4f} {expected:14.4f}")

    # The carry paths grow as PF^m ~ 8.531^m
    # The orbit grows as ~4.5^m
    # So ratio ~ (8.531/4.5)^m ~ 1.896^m
    print(f"\nCarry paths grow as PF^m ~ {PF:.3f}^m")
    print(f"Orbit survivors grow as ~4.5^m")
    print(f"Ratio grows as (PF/4.5)^m ~ {ratio_expected:.4f}^m")
    print()
    print("This confirms: the carry matrix counts MULTI-STEP paths,")
    print("not single-step transitions from the orbit. The 1.9x factor")
    print("is per-step; over m steps it compounds to (1.9)^m.")

    # BUT: the SINGLE-STEP test (M_aug * v_m vs v_{m+1}) should give ~1.9x
    print("\n--- Single-step overcount test ---")
    print(f"{'m':>3} {'M_aug*v_m':>12} {'Z_m+1':>10} {'ratio':>10}")
    print("-" * 40)

    for m in range(1, min(M_MAX, 10)):
        if m not in all_survivors or m+1 not in all_survivors:
            continue
        surv = all_survivors[m]

        # Build carry/parity vector
        v = np.zeros(4)
        for s in surv:
            idx = 2 * s['carry_out'] + s['u_parity']
            v[idx] += 1

        pred = M_AUG_1 @ v
        pred_total = sum(pred)
        actual = len(all_survivors[m+1])
        ratio = pred_total / actual if actual > 0 else 0
        print(f"{m:3d} {pred_total:12.0f} {actual:10,} {ratio:10.4f}")


def part_F(all_survivors):
    """Direct spectral gap verification: fit orbit parity decay to theta."""
    print("\n" + "=" * 90)
    print("PART F: Spectral Gap Verification on Orbit Data")
    print("=" * 90)

    # Compute |e_m - 1/2| at each level
    ms = sorted(all_survivors.keys())
    biases = []

    print(f"\n{'m':>3} {'|e-0.5|':>12} {'theta^m':>12} {'C*theta^m':>12} "
          f"{'ratio':>10}")
    print("-" * 55)

    for m in ms:
        surv = all_survivors[m]
        Z = len(surv)
        E = sum(1 for s in surv if s['u_parity'] == 0)
        e = E / Z if Z > 0 else 0.5
        bias = abs(e - 0.5)
        theta_m = THETA ** m
        C_est = 0.26  # from prior fit
        pred = C_est * theta_m
        ratio = bias / theta_m if theta_m > 1e-15 else 0

        biases.append((m, bias))
        print(f"{m:3d} {bias:12.2e} {theta_m:12.2e} {pred:12.2e} {ratio:10.4f}")

    # Fit C and theta from data (only nonzero biases)
    valid = [(m, b) for m, b in biases if b > 0]
    if len(valid) >= 3:
        xv = np.array([v[0] for v in valid])
        yv = np.array([math.log(v[1]) for v in valid])
        slope, intercept = np.polyfit(xv, yv, 1)
        theta_fit = math.exp(slope)
        C_fit = math.exp(intercept)
        print(f"\nFitted: |e-0.5| ~ {C_fit:.4f} * {theta_fit:.6f}^m")
        print(f"Predicted theta = {THETA:.6f}")
        print(f"Fitted theta    = {theta_fit:.6f}")
        print(f"Ratio fitted/predicted = {theta_fit/THETA:.4f}")

    # Check the bias identity: e_{m+1} - 1/2 = (p_m - 1/2)(1-e_m)/(5-e_m)
    print(f"\n--- Bias Identity Verification ---")
    print(f"{'m':>3} {'e_m':>10} {'p_m':>10} {'LHS':>12} {'RHS':>12} "
          f"{'match':>8}")
    print("-" * 60)

    for m in range(1, max(ms)):
        if m not in all_survivors or m+1 not in all_survivors:
            continue
        surv_m = all_survivors[m]
        surv_next = all_survivors[m+1]

        Z = len(surv_m)
        E = sum(1 for s in surv_m if s['u_parity'] == 0)
        e_m = E / Z if Z > 0 else 0.5

        Z_next = len(surv_next)
        E_next = sum(1 for s in surv_next if s['u_parity'] == 0)
        e_next = E_next / Z_next if Z_next > 0 else 0.5

        # Compute p_m: fraction of odd-type parents at level m whose v_0 is even
        # v_0 = (u + 5^m) / 2 for odd u. v_0 even iff (u + 5^m) mod 4 == 0
        # Since 5^m is odd, u + 5^m is even (since u is odd).
        # (u + 5^m)/2 is even iff u + 5^m = 0 mod 4, i.e., u = -5^m mod 4
        # 5^m mod 4 = 1 for all m. So u = -1 mod 4 = 3 mod 4.
        # p_m = fraction of odd survivors with u = 3 mod 4.
        odd_surv = [s for s in surv_m if s['u_parity'] == 1]
        if odd_surv:
            p_m = sum(1 for s in odd_surv if s['u'] % 4 == 3) / len(odd_surv)
        else:
            p_m = 0.5

        LHS = e_next - 0.5
        RHS = (p_m - 0.5) * (1 - e_m) / (5 - e_m)

        match = abs(LHS - RHS) < 1e-10
        print(f"{m:3d} {e_m:10.6f} {p_m:10.6f} {LHS:>+12.2e} {RHS:>+12.2e} "
              f"{'YES' if match else f'NO (diff={abs(LHS-RHS):.2e})'}")

    # Compute the contraction factor: |e_{m+1} - 0.5| / |p_m - 0.5|
    print(f"\n--- Contraction factors ---")
    print(f"{'m':>3} {'|p_m-0.5|':>12} {'|e_m+1-0.5|':>12} "
          f"{'contraction':>12} {'(1-e_m)/(5-e_m)':>16}")
    print("-" * 60)

    for m in range(1, max(ms)):
        if m not in all_survivors or m+1 not in all_survivors:
            continue
        surv_m = all_survivors[m]
        surv_next = all_survivors[m+1]

        Z = len(surv_m)
        E = sum(1 for s in surv_m if s['u_parity'] == 0)
        e_m = E / Z if Z > 0 else 0.5

        Z_next = len(surv_next)
        E_next = sum(1 for s in surv_next if s['u_parity'] == 0)
        e_next = E_next / Z_next if Z_next > 0 else 0.5

        odd_surv = [s for s in surv_m if s['u_parity'] == 1]
        if odd_surv:
            p_m = sum(1 for s in odd_surv if s['u'] % 4 == 3) / len(odd_surv)
        else:
            p_m = 0.5

        bias_p = abs(p_m - 0.5)
        bias_e = abs(e_next - 0.5)
        contraction = bias_e / bias_p if bias_p > 1e-15 else float('inf')
        structural = (1 - e_m) / (5 - e_m)

        print(f"{m:3d} {bias_p:12.2e} {bias_e:12.2e} "
              f"{contraction:12.6f} {structural:16.6f}")


def main():
    print(f"Experiment 12: Pair-to-Orbit Transfer Verification (m=1..{M_MAX})\n")
    t_start = time.time()

    # Enumerate all orbit survivors with metadata
    print("Enumerating orbit survivors with full metadata...")
    all_survivors = {}
    for m in range(1, M_MAX + 1):
        t0 = time.time()
        surv = enumerate_orbit(m)
        elapsed = time.time() - t0
        all_survivors[m] = surv
        print(f"  m={m}: {len(surv):>10,} survivors ({elapsed:.2f}s)")

    print(f"\nTotal enumeration: {time.time() - t_start:.1f}s")
    print()

    part_A(all_survivors)
    part_B(all_survivors)
    part_C(all_survivors)
    part_D(all_survivors)
    part_E(all_survivors)
    part_F(all_survivors)

    # SUMMARY
    print("\n" + "=" * 90)
    print("EXPERIMENT 12 SUMMARY")
    print("=" * 90)

    elapsed_total = time.time() - t_start
    print(f"\nTotal time: {elapsed_total:.1f}s")

    print(f"\nKey questions addressed:")
    print(f"  A. Pair-constraint vs orbit parity: do they match?")
    print(f"  B. Overcount asymmetry (2 for even, 9/5 for odd): effect on ratio?")
    print(f"  C. Carry-0 exact balance: why?")
    print(f"  D. Minimal Markov state space: which k makes it constant?")
    print(f"  E. Carry paths vs orbit: the exponential divergence")
    print(f"  F. Spectral gap: does theta = {THETA:.5f} match data?")

    # Save results
    save_data = {
        '_meta': {
            'M_MAX': M_MAX,
            'PF': PF,
            'SQRT6': SQRT6,
            'THETA': THETA,
            'elapsed': elapsed_total,
        },
        'orbit_counts': {
            str(m): {
                'Z': len(all_survivors[m]),
                'E': sum(1 for s in all_survivors[m] if s['u_parity'] == 0),
                'O': sum(1 for s in all_survivors[m] if s['u_parity'] == 1),
                'Z_c0': sum(1 for s in all_survivors[m] if s['carry_out'] == 0),
                'E_c0': sum(1 for s in all_survivors[m]
                           if s['carry_out'] == 0 and s['u_parity'] == 0),
            }
            for m in sorted(all_survivors.keys())
        },
    }
    path = os.path.join(DATA_DIR, "exp12_results.json")
    with open(path, 'w') as f:
        json.dump(save_data, f, indent=2)
    print(f"\nSaved to {path}")


if __name__ == '__main__':
    main()
