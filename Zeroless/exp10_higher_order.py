#!/usr/bin/env python3
"""
Experiment 10: Higher-Order Constraint Transfer Matrices

Build transfer matrices for m-fold constraints (x, 2x, 4x, ..., 2^{m-1}x all zeroless)
for m=1..18. Track how the branching factor beta(m) = rho(m)/2 decreases with m.

Key question: does beta(m) cross below critical thresholds?
Known: beta(1)=4.5, beta(2)~4.266, beta(3)~4.018 (barely above 4).
"""

import sys
import os
import json
import time
import math
import numpy as np
from collections import deque

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)


# ============================================================
# Helpers
# ============================================================

def is_kdigit_zeroless(x, k):
    """Check if the last k digits of x are all nonzero."""
    for _ in range(k):
        if x % 10 == 0:
            return False
        x //= 10
    return True


def build_transfer_matrix(m):
    """
    Build 2^{m-1} x 2^{m-1} transfer matrix for m-fold zeroless constraint.

    State = carry vector (c_1, ..., c_{m-1}) encoded as integer.
    Bit i of state = c_{i+1}.

    For input digit d in {1,...,9}:
      y_0 = d
      t_i = 2*y_{i-1} + c_i, y_i = t_i mod 10, c_i' = t_i // 10
      Require y_i != 0 for i = 1..m-1.

    M[new_state, old_state] = number of valid digits producing this transition.
    """
    if m == 1:
        return np.array([[9.0]])

    dim = 1 << (m - 1)
    use_sparse = dim >= 8192

    if use_sparse:
        try:
            from scipy.sparse import lil_matrix
            M = lil_matrix((dim, dim), dtype=float)
        except ImportError:
            print(f"  WARNING: scipy not available, using dense for dim={dim}")
            M = np.zeros((dim, dim), dtype=float)
            use_sparse = False
    else:
        M = np.zeros((dim, dim), dtype=float)

    for old_state in range(dim):
        # Decode carry vector from state integer
        old_carries = [(old_state >> i) & 1 for i in range(m - 1)]

        for d in range(1, 10):
            y = d
            new_state = 0
            valid = True

            for i in range(m - 1):
                t = 2 * y + old_carries[i]
                y = t % 10
                new_state |= ((t // 10) << i)
                if y == 0:
                    valid = False
                    break

            if valid:
                M[new_state, old_state] += 1

    if use_sparse:
        return M.tocsr()
    return M


def compute_spectral_radius(M):
    """Compute spectral radius and top eigenvalues."""
    is_sparse = hasattr(M, 'toarray')

    if is_sparse and M.shape[0] > 4096:
        from scipy.sparse.linalg import eigs
        k = min(8, M.shape[0] - 2)
        vals, _ = eigs(M.astype(float), k=k, which='LM')
        rho = float(max(abs(vals)))
        eigs_sorted = sorted(vals, key=lambda x: -abs(x))
        return rho, eigs_sorted

    dense = M.toarray() if is_sparse else M
    eigenvalues = np.linalg.eigvals(dense)
    rho = float(max(abs(eigenvalues)))
    eigs_sorted = sorted(eigenvalues, key=lambda x: -abs(x))
    return rho, eigs_sorted


# ============================================================
# Part A: Transfer matrix construction and spectral analysis
# ============================================================

def part_A(max_m=18, time_limit=120):
    """Build matrices and compute spectral radii for m=1..max_m."""
    print("=" * 70)
    print("PART A: Transfer Matrix Construction and Spectral Analysis")
    print("=" * 70)

    results = []

    for m in range(1, max_m + 1):
        dim = 1 << (m - 1)
        print(f"\n--- m={m}, dim={dim}x{dim} ---")

        t0 = time.time()
        M = build_transfer_matrix(m)
        t_build = time.time() - t0
        print(f"  Built in {t_build:.3f}s")

        if t_build > time_limit:
            print(f"  Build exceeded {time_limit}s limit, stopping.")
            break

        t0 = time.time()
        rho, eigs_sorted = compute_spectral_radius(M)
        t_eig = time.time() - t0

        beta = rho / 2
        is_sparse = hasattr(M, 'toarray')
        col_sums = np.array(M.sum(axis=0)).flatten() if is_sparse else M.sum(axis=0)

        print(f"  Eigenvalues in {t_eig:.3f}s")
        print(f"  rho = {rho:.10f}")
        print(f"  beta = rho/2 = {beta:.10f}")
        print(f"  beta - 4 = {beta - 4:+.10f}")
        print(f"  Col sums: min={col_sums.min():.0f} max={col_sums.max():.0f} "
              f"mean={col_sums.mean():.4f}")

        n_show = min(6, len(eigs_sorted))
        print(f"  Top |eigenvalues|: {[f'{abs(e):.6f}' for e in eigs_sorted[:n_show]]}")

        # Print matrix for small m
        if m <= 4 and not is_sparse:
            print(f"  Matrix:\n{M.astype(int)}")

        # Characteristic polynomial for small m
        char_poly = None
        if m <= 8 and not is_sparse:
            try:
                coeffs = np.round(np.poly(np.linalg.eigvals(M))).astype(int).tolist()
                char_poly = coeffs
                print(f"  Char poly: {coeffs}")
            except Exception:
                pass

        result = {
            'm': m, 'dim': dim, 'rho': float(rho),
            'beta': float(beta), 'beta_minus_4': float(beta - 4),
            'col_sum_min': float(col_sums.min()),
            'col_sum_max': float(col_sums.max()),
            'col_sum_mean': float(col_sums.mean()),
            'top_eigenvalues': [{'real': float(e.real), 'imag': float(e.imag)}
                                for e in eigs_sorted[:n_show]],
            'build_time': t_build, 'eig_time': t_eig,
        }
        if char_poly:
            result['char_poly'] = char_poly
        results.append(result)

        if t_eig > time_limit:
            print(f"  Eigenvalue computation exceeded {time_limit}s, stopping.")
            break

    return results


# ============================================================
# Part B: Branching factor analysis and asymptotic modeling
# ============================================================

def part_B(results):
    """Analyze beta(m) sequence for threshold crossings and asymptotics."""
    print("\n" + "=" * 70)
    print("PART B: Branching Factor Analysis")
    print("=" * 70)

    ms = [r['m'] for r in results]
    betas = [r['beta'] for r in results]
    rhos = [r['rho'] for r in results]

    # Table
    print(f"\n{'m':>4} {'rho(m)':>14} {'beta(m)':>14} {'beta-4':>14} {'delta_beta':>14}")
    print("-" * 64)
    for i, (m, rho, beta) in enumerate(zip(ms, rhos, betas)):
        delta = betas[i] - betas[i - 1] if i > 0 else float('nan')
        tag = ""
        if beta < 4:
            tag = " *** SUBCRITICAL ***"
        elif beta < 4.05:
            tag = " <-- marginal"
        print(f"{m:4d} {rho:14.8f} {beta:14.8f} {beta - 4:+14.8f} "
              f"{delta:14.8f}{tag}")

    # Threshold crossings
    print("\nThreshold crossings:")
    for thresh in [5.0, 4.5, 4.0, 3.5, 3.0, 2.0, 1.0]:
        below = [(m, b) for m, b in zip(ms, betas) if b < thresh]
        if below:
            print(f"  beta < {thresh}: CROSSED at m={below[0][0]} "
                  f"(beta={below[0][1]:.8f})")
        else:
            print(f"  beta < {thresh}: not crossed "
                  f"(min={min(betas):.8f} at m={ms[betas.index(min(betas))]})")

    # Asymptotic fitting (need at least 5 points)
    if len(ms) >= 5:
        x = np.array(ms, dtype=float)
        y = np.array(betas, dtype=float)
        log_y = np.log(y)

        print("\nAsymptotic model fits:")

        # Exponential: beta = a * exp(-b*m)
        c1 = np.polyfit(x, log_y, 1)
        a_exp, b_exp = np.exp(c1[1]), -c1[0]
        resid = np.sum((log_y - np.polyval(c1, x)) ** 2)
        print(f"  Exponential: beta ~ {a_exp:.4f} * exp(-{b_exp:.6f}*m), "
              f"RSS={resid:.6f}")
        if b_exp > 0:
            print(f"    -> beta=4 crossing at m ~ "
                  f"{(math.log(a_exp) - math.log(4)) / b_exp:.1f}")

        # Linear: beta = a + b*m
        c2 = np.polyfit(x, y, 1)
        resid = np.sum((y - np.polyval(c2, x)) ** 2)
        print(f"  Linear: beta ~ {c2[1]:.4f} + ({c2[0]:.6f})*m, "
              f"RSS={resid:.6f}")
        if c2[0] < 0:
            print(f"    -> beta=4 crossing at m ~ "
                  f"{(4 - c2[1]) / (-c2[0]):.1f}")

        # Power law: beta = a / m^c
        log_x = np.log(x)
        c3 = np.polyfit(log_x, log_y, 1)
        c_pow, a_pow = -c3[0], np.exp(c3[1])
        resid = np.sum((log_y - np.polyval(c3, log_x)) ** 2)
        print(f"  Power law: beta ~ {a_pow:.4f} / m^{c_pow:.4f}, "
              f"RSS={resid:.6f}")
        if c_pow > 0:
            print(f"    -> beta=4 crossing at m ~ "
                  f"{(a_pow / 4) ** (1 / c_pow):.1f}")

        # Successive differences
        print("\n  Successive differences:")
        for i in range(1, len(betas)):
            diff = betas[i] - betas[i - 1]
            if i >= 2 and (betas[i - 1] - betas[i - 2]) != 0:
                ratio = diff / (betas[i - 1] - betas[i - 2])
                print(f"    delta({ms[i]}) = {diff:+.8f}  "
                      f"(ratio to prev: {ratio:.4f})")
            else:
                print(f"    delta({ms[i]}) = {diff:+.8f}")

        # Information per constraint
        print("\n  Information per additional constraint:")
        for i in range(1, len(betas)):
            info = math.log(betas[i - 1]) - math.log(betas[i])
            print(f"    m={ms[i - 1]}->{ms[i]}: {info:.6f} nats "
                  f"({info / math.log(2):.6f} bits)")

    return {'ms': ms, 'betas': betas, 'rhos': rhos}


# ============================================================
# Part C: Orbit verification
# ============================================================

def part_C(results):
    """Verify beta = rho/2 against orbit enumeration."""
    print("\n" + "=" * 70)
    print("PART C: Orbit Verification (beta = rho/2)")
    print("=" * 70)

    max_k = 8
    max_m = min(8, max(r['m'] for r in results))
    pred_betas = {r['m']: r['beta'] for r in results}

    orbit_data = {}

    for m in range(1, max_m + 1):
        print(f"\n--- m={m} (x, 2x, ..., 2^{{{m - 1}}}x zeroless) ---")
        counts = []

        for k in range(1, max_k + 1):
            mod = 10 ** k
            period = 4 * (5 ** (k - 1))

            # Sliding window of m consecutive powers
            window = deque()
            x = 1
            for j in range(m):
                window.append(x)
                x = (2 * x) % mod

            count = 0
            for n in range(period):
                if all(is_kdigit_zeroless(w, k) for w in window):
                    count += 1
                window.popleft()
                window.append(x)
                x = (2 * x) % mod

            counts.append(count)
            branching = counts[-1] / counts[-2] if k >= 2 and counts[-2] > 0 else float('nan')

            pred = pred_betas.get(m)
            extra = ""
            if pred and k >= 3 and not math.isnan(branching):
                extra = f"  pred={pred:.4f} err={abs(branching - pred):.4f}"

            print(f"  k={k}: count={count:>8d}  branching={branching:>8.4f}{extra}")

        orbit_data[m] = counts

    return orbit_data


# ============================================================
# Part D: Characteristic polynomial analysis
# ============================================================

def part_D(results):
    """Analyze characteristic polynomial patterns."""
    print("\n" + "=" * 70)
    print("PART D: Characteristic Polynomial Patterns")
    print("=" * 70)

    polys = [(r['m'], r['char_poly']) for r in results if 'char_poly' in r]

    for m, coeffs in polys:
        print(f"\nm={m} (degree {len(coeffs) - 1}): {coeffs}")

    # Look for patterns: sum of coefficients, alternating sum, etc.
    if polys:
        print("\nCoefficient analysis:")
        print(f"{'m':>3} {'sum':>8} {'alt_sum':>8} {'coeff[-1]':>10} {'coeff[-2]':>10}")
        for m, coeffs in polys:
            s = sum(coeffs)
            alt = sum(c * (-1) ** i for i, c in enumerate(coeffs))
            print(f"{m:3d} {s:8d} {alt:8d} {coeffs[-1]:10d} "
                  f"{coeffs[-2] if len(coeffs) > 1 else 0:10d}")


# ============================================================
# Main
# ============================================================

def main():
    print("Experiment 10: Higher-Order Constraint Transfer Matrices")
    print("=" * 70)
    print()

    results_A = part_A(max_m=18, time_limit=120)
    results_B = part_B(results_A)
    orbit_data = part_C(results_A)
    part_D(results_A)

    # Save
    output = {
        'transfer_matrices': results_A,
        'beta_sequence': results_B,
        'orbit_verification': {str(k): v for k, v in orbit_data.items()},
    }

    def convert(obj):
        if isinstance(obj, (np.integer,)):
            return int(obj)
        elif isinstance(obj, (np.floating,)):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        return obj

    path = os.path.join(DATA_DIR, "exp10_results.json")
    with open(path, 'w') as f:
        json.dump(output, f, indent=2, default=convert)
    print(f"\n\nResults saved to {path}")

    # Final summary
    ms = results_B['ms']
    betas = results_B['betas']

    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    print(f"\n{'m':>4} {'beta(m)':>14} {'beta-4':>14} {'status':>20}")
    print("-" * 56)
    for m, beta in zip(ms, betas):
        if beta < 4:
            status = "*** SUBCRITICAL ***"
        elif beta < 4.05:
            status = "MARGINAL"
        elif beta < 4.5:
            status = "MILDLY SUPER"
        else:
            status = "SUPERCRITICAL"
        print(f"{m:4d} {beta:14.8f} {beta - 4:+14.8f} {status:>20}")

    min_beta = min(betas)
    min_m = ms[betas.index(min_beta)]

    if min_beta < 4:
        print(f"\n*** CRITICAL: beta crosses below 4 at m={min_m}! ***")
        print(f"*** The {min_m}-fold constraint is SUBCRITICAL on the orbit. ***")
    else:
        print(f"\n  Minimum beta: {min_beta:.8f} at m={min_m}")
        print(f"  Gap above 4: {min_beta - 4:.8f}")


if __name__ == "__main__":
    main()
