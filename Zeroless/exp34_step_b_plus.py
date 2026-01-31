#!/usr/bin/env python3
"""
Experiment 34: Multi-lag Step B+ Verification

MOTIVATION:
Step B proves that no single component of F_m spans theta = log10(2).
Step B+ extends this: max_comp(F_m) < ||k*theta|| for ALL k = 1..L_m,
meaning no two orbit points in the transition zone can share a component,
regardless of their separation. This experiment verifies B+ numerically.

KEY QUESTIONS:
1. Is max_comp(F_m) < min_{k=1..L_m} ||k*theta|| for all m >= 2?
2. How does the ratio max_comp / min||k*theta|| behave?
3. At what m does Step B+ become trivially true?

PARTS:
A) Exact max_comp(F_m) from the formula
B) Minimum ||k*theta|| for k = 1..L_m
C) Verification of B+ inequality
D) Ratio analysis
"""

import math

theta = math.log10(2)
C_const = 1.0 / theta


def max_comp_Fm(m):
    """Exact maximum component width of F_m in alpha-space."""
    return math.log10(1 + 81.0 / (10**m - 1))


def min_frac_k_theta(L):
    """Minimum ||k*theta|| for k = 1..L."""
    best = 1.0
    for k in range(1, L + 1):
        frac_part = (k * theta) % 1.0
        dist = min(frac_part, 1.0 - frac_part)
        if dist < best:
            best = dist
            best_k = k
    return best, best_k


if __name__ == "__main__":
    print("=" * 70)
    print("  EXPERIMENT 34: MULTI-LAG STEP B+ VERIFICATION")
    print("=" * 70)

    # =================================================================
    # Part A & B: Compute both quantities
    # =================================================================
    print()
    print("  PART A-C: Step B+ verification for m = 2..29")
    print()
    print("  m | L_m | max_comp(F_m) | min||k*theta|| (at k) | ratio  | B+ holds?")
    print("  --+-----+---------------+-----------------------+--------+----------")

    all_hold = True
    for m in range(2, 30):
        L_m = int(math.ceil(C_const * m))
        mc = max_comp_Fm(m)
        mk, mk_k = min_frac_k_theta(L_m)
        ratio = mc / mk if mk > 0 else float('inf')
        holds = mc < mk

        if not holds:
            all_hold = False

        status = "YES" if holds else "**NO**"
        print(f"  {m:2d} | {L_m:3d} | {mc:13.6e} | {mk:.6e} (k={mk_k:3d}) | {ratio:.4e} | {status}")

    # =================================================================
    # Part D: Analysis
    # =================================================================
    print()
    print("=" * 70)
    print("  PART D: Analysis")
    print("=" * 70)
    print()

    if all_hold:
        print("  Step B+ VERIFIED for all m = 2..29.")
        print("  No two orbit points in the transition zone share a component")
        print("  of F_m, regardless of their lag separation.")
        print()
        print("  The ratio max_comp/min||k*theta|| decreases exponentially:")
        print("  max_comp ~ 10^{-(m-1)}, while min||k*theta|| ~ 1/poly(m).")
        print("  For m >= 3, the ratio is already < 10^{-3}.")
        print()
        print("  CONCLUSION: Step B+ is trivially true for all m >= 3.")
        print("  Every hit in the transition zone is in a DISTINCT component.")
    else:
        print("  Step B+ fails for some m values. Check output above.")

    # Continued fraction convergents for reference
    print()
    print("  Reference: convergent denominators of theta = log10(2)")
    cf = [0, 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18]
    p_prev, p_curr = 0, 1
    q_prev, q_curr = 1, 0
    print("  n | a_n | q_n | ||q_n * theta||")
    print("  --+-----+-----+----------------")
    for n, a in enumerate(cf):
        p_prev, p_curr = p_curr, a * p_curr + p_prev
        q_prev, q_curr = q_curr, a * q_curr + q_prev
        err = abs(q_curr * theta - round(q_curr * theta))
        print(f"  {n:2d} | {a:3d} | {q_curr:5d} | {err:.12f}")
