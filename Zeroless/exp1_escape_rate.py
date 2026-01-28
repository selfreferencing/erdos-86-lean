#!/usr/bin/env python3
"""
Experiment 1: Transfer Operator with Hole (Escape Rate)

Motivation: Thermodynamic formalism ranked #1 "unexpected source" by both M4-A
responses. Three fields (physics, QIT, probability) converge on the carry-mediated
transfer operator as the natural mathematical object.

The idea: model base-10 digit generation via "doubling with carry" as a transfer
operator. Remove digit-0 states (the "hole"). If the spectral radius of the
constrained operator is < 1, then the system escapes the zeroless region
exponentially fast.

Two formulations:
  (A) Single-step: doubling 2^{n-1} -> 2^n propagates carries right-to-left.
      The transfer matrix acts on carry states, with digit emission.
  (B) Full cylinder: at scale k, track which residues mod 10^k are zeroless
      and how the orbit cycles through them.
"""

import sys
import numpy as np
from collections import defaultdict

sys.set_int_max_str_digits(100000)

# ============================================================================
# FORMULATION A: Single-step doubling transfer operator
# ============================================================================

def build_doubling_transfer_matrix():
    """
    Build the transfer matrix for the "doubling with carry" digit-generation process.

    When we compute 2*x digit by digit (right to left):
      - At each position, we have: 2*d_j + carry_in = digit_out + 10*carry_out
      - carry_in is 0 or 1
      - d_j is the input digit (0-9)
      - digit_out = (2*d_j + carry_in) mod 10
      - carry_out = (2*d_j + carry_in) // 10

    State: carry value (0 or 1)
    For each input digit d, the transition is:
      (carry_in) -> (carry_out), emitting digit_out

    We build two versions:
      T_full: allows all output digits (0-9)
      T_hole: only allows output digits 1-9 (digit 0 is the "hole")
    """
    # State space: {0, 1} (carry values)
    # For each input digit d in {0,...,9}, we get a transition

    # But we need to think about this differently for the "zeroless" question.
    # The question is about the OUTPUT digits of 2^n, not the input.
    # When we double a number, each output digit depends on the input digit
    # at that position and the carry from the position to the right.

    # Actually, let's think about it as: we know 2^n = 2 * 2^{n-1}.
    # The digits of 2^n are determined by the digits of 2^{n-1} through
    # the doubling-with-carry process.

    # For the transfer operator, the state is the carry propagating left.
    # At each digit position j (right to left):
    #   new_digit_j = (2 * old_digit_j + carry_in) mod 10
    #   carry_out = (2 * old_digit_j + carry_in) // 10

    # The key insight: if we want ALL output digits to be nonzero,
    # we need constraints on the input digits given the carry.

    # For carry_in = 0: output digit = (2*d) mod 10
    #   Output 0 when d=0 or d=5
    #   So input digits {1,2,3,4,6,7,8,9} give nonzero output
    # For carry_in = 1: output digit = (2*d+1) mod 10
    #   Output 0 when 2d+1 = 10 or 20, i.e., d=4.5 (impossible) or d=9.5 (impossible)
    #   Actually: 2d+1 mod 10 = 0 when 2d+1 is multiple of 10, i.e., d = 4.5 -- impossible!
    #   So with carry_in=1, NO input digit produces output 0.

    # Carry transitions:
    # carry_in=0: carry_out = (2*d) // 10
    #   d in {0,1,2,3,4} -> carry_out = 0
    #   d in {5,6,7,8,9} -> carry_out = 1
    # carry_in=1: carry_out = (2*d+1) // 10
    #   d in {0,1,2,3,4} -> carry_out = 0 (since max is 2*4+1=9)
    #   d=5 -> 11 -> carry_out = 1
    #   d in {5,6,7,8,9} -> carry_out = 1

    print("="*70)
    print("FORMULATION A: Single-step doubling transfer operator")
    print("="*70)

    print("\nDigit transition table (carry_in, input_d -> output_d, carry_out):")
    print(f"{'c_in':>5} {'d_in':>5} {'d_out':>6} {'c_out':>6} {'d_out=0?':>9}")
    print("-"*35)

    transitions = {}  # (carry_in, d_in) -> (d_out, carry_out)
    for c_in in [0, 1]:
        for d_in in range(10):
            val = 2 * d_in + c_in
            d_out = val % 10
            c_out = val // 10
            transitions[(c_in, d_in)] = (d_out, c_out)
            if d_out == 0:
                print(f"{c_in:>5} {d_in:>5} {d_out:>6} {c_out:>6} {'YES':>9} ***")
            elif c_in == 0 and d_in <= 2:
                print(f"{c_in:>5} {d_in:>5} {d_out:>6} {c_out:>6}")

    print("\nKey observation:")
    print("  carry_in=0: output=0 when d_in in {0, 5}")
    print("  carry_in=1: output=0 NEVER (2d+1 is always odd)")
    print()

    # Build 2x2 transfer matrices
    # T[c_out, c_in] = number of input digits that produce this transition
    # T_full: all input digits allowed
    # T_hole: only input digits that DON'T produce output digit 0

    T_full = np.zeros((2, 2))
    T_hole = np.zeros((2, 2))

    for c_in in [0, 1]:
        for d_in in range(10):
            d_out, c_out = transitions[(c_in, d_in)]
            T_full[c_out, c_in] += 1
            if d_out != 0:
                T_hole[c_out, c_in] += 1

    print("T_full (all digits allowed):")
    print(T_full)
    print(f"  Eigenvalues: {np.linalg.eigvals(T_full)}")
    print(f"  Spectral radius: {max(abs(np.linalg.eigvals(T_full))):.6f}")

    print("\nT_hole (digit 0 forbidden in output):")
    print(T_hole)
    eigs_hole = np.linalg.eigvals(T_hole)
    print(f"  Eigenvalues: {eigs_hole}")
    rho = max(abs(eigs_hole))
    print(f"  Spectral radius: {rho:.6f}")
    print(f"  Ratio rho/10: {rho/10:.6f}")
    print(f"  (9/10 = 0.9 for comparison)")

    print("\nInterpretation:")
    print(f"  T_full has spectral radius 10 (each digit position has 10 choices)")
    print(f"  T_hole has spectral radius {rho:.4f}")
    print(f"  Ratio = {rho/10:.6f} (compare to 9/10 = 0.9)")
    print(f"  This means: fraction of paths avoiding digit 0 decays as ~{rho/10:.4f}^k")

    return T_full, T_hole


# ============================================================================
# FORMULATION B: Zeroless survivor counting via 5-adic structure
# ============================================================================

def build_fiveadic_transfer(k_max=10):
    """
    Build the transfer operator on the 5-adic survivor structure.

    At level k, the orbit 2^n mod 5^k cycles with period T_k = 4 * 5^{k-1}.
    Among these T_k residues, some give "zeroless" trailing k digits.

    The transfer from level k to k+1:
    - Each survivor at level k has either 4 or 5 "children" at level k+1
    - A child survives if the new (k+1)-th digit is nonzero
    - The growth factor per level is 4.5 (= average children surviving)

    We compute the actual survivor counts and the effective transfer operator.
    """
    print("\n" + "="*70)
    print("FORMULATION B: 5-adic survivor transfer operator")
    print("="*70)

    results = []

    for k in range(1, k_max + 1):
        period = 4 * 5**(k-1)

        # Count survivors: residues r mod period such that
        # 2^r mod 10^k has all nonzero digits
        survivors = []
        for r in range(period):
            n = r if r >= k else r + period  # ensure enough digits
            power_mod = pow(2, n, 10**k)

            # Check all k digits
            zeroless = True
            temp = power_mod
            for _ in range(k):
                if temp % 10 == 0:
                    zeroless = False
                    break
                temp //= 10

            if zeroless:
                survivors.append(r)

        count = len(survivors)
        density = count / period
        expected_count = 4 * 4.5**(k-1) if k >= 1 else 4
        expected_density = 0.9**(k-1) if k >= 1 else 1.0

        results.append({
            'k': k,
            'period': period,
            'survivors': count,
            'density': density,
            'expected_count': expected_count,
            'expected_density': expected_density,
            'ratio': count / expected_count if expected_count > 0 else 0
        })

        print(f"k={k:2d}: period={period:10d}, survivors={count:10d}, "
              f"density={density:.8f}, expected={expected_density:.8f}, "
              f"ratio={density/expected_density:.6f}")

    # Compute level-to-level growth factors
    print("\nLevel-to-level growth factors:")
    print(f"{'k':>4} {'survivors_k':>12} {'survivors_{k+1}':>15} {'growth':>10} {'(cf 4.5)':>10}")
    for i in range(len(results) - 1):
        s1 = results[i]['survivors']
        s2 = results[i+1]['survivors']
        growth = s2 / s1 if s1 > 0 else float('inf')
        print(f"{results[i]['k']:>4} {s1:>12} {s2:>15} {growth:>10.4f} {'4.5':>10}")

    return results


# ============================================================================
# FORMULATION C: Conditioned transfer matrix (the "right" formulation)
# ============================================================================

def build_conditioned_transfer(k_max=8):
    """
    The key formulation: condition on the INPUT being zeroless and track
    what fraction of transitions preserve zerolessness.

    At each digit position, given carry_in:
    - If we condition on input digit being in {1,...,9} (zeroless input)
    - What fraction of these produce a zeroless output?
    - And what's the carry distribution?

    This gives the "conditioned" transfer matrix whose spectral radius
    determines the escape rate.
    """
    print("\n" + "="*70)
    print("FORMULATION C: Conditioned transfer (zeroless -> zeroless)")
    print("="*70)

    # For each (carry_in, input_digit in {1..9}), compute output and carry
    # Then: what fraction of zeroless inputs give zeroless outputs?

    for c_in in [0, 1]:
        total = 0
        zero_out = 0
        nonzero_out = 0
        carry_out_counts = {0: 0, 1: 0}

        print(f"\ncarry_in = {c_in}:")
        for d_in in range(1, 10):  # zeroless input
            val = 2 * d_in + c_in
            d_out = val % 10
            c_out = val // 10
            total += 1
            if d_out == 0:
                zero_out += 1
                print(f"  d_in={d_in}: 2*{d_in}+{c_in}={val} -> d_out={d_out} (ZERO!), c_out={c_out}")
            else:
                nonzero_out += 1
            carry_out_counts[c_out] += 1

        print(f"  Total zeroless inputs: {total}")
        print(f"  Outputs with zero: {zero_out}")
        print(f"  Outputs without zero: {nonzero_out}")
        print(f"  Fraction zeroless output: {nonzero_out/total:.4f}")
        print(f"  Carry distribution: {dict(carry_out_counts)}")

    # Build the conditioned 2x2 matrix
    # M[c_out, c_in] = (# of zeroless inputs d giving zeroless output and this carry transition)
    #                   / (# of zeroless inputs = 9)
    # Actually, let's do it unnormalized first

    M_cond = np.zeros((2, 2))
    for c_in in [0, 1]:
        for d_in in range(1, 10):  # zeroless inputs only
            val = 2 * d_in + c_in
            d_out = val % 10
            c_out = val // 10
            if d_out != 0:  # zeroless output
                M_cond[c_out, c_in] += 1

    print(f"\nConditioned transfer matrix (unnormalized):")
    print(f"  M = {M_cond}")
    eigs = np.linalg.eigvals(M_cond)
    rho = max(abs(eigs))
    print(f"  Eigenvalues: {eigs}")
    print(f"  Spectral radius: {rho:.6f}")
    print(f"  Spectral radius / 9: {rho/9:.6f}")
    print(f"  (If this = 1, then zeroless paths don't decay under conditioning)")
    print(f"  (If this < 1, then zeroless paths decay exponentially)")

    # Now do the NORMALIZED version
    M_norm = np.zeros((2, 2))
    for c_in in [0, 1]:
        col_sum = sum(1 for d_in in range(1, 10)
                      if (2*d_in + c_in) % 10 != 0)
        for d_in in range(1, 10):
            val = 2 * d_in + c_in
            d_out = val % 10
            c_out = val // 10
            if d_out != 0:
                M_norm[c_out, c_in] += 1.0 / 9  # normalize by # zeroless inputs

    print(f"\nNormalized transfer matrix (each column sums to P(output zeroless | carry)):")
    print(f"  M_norm = {M_norm}")
    eigs_norm = np.linalg.eigvals(M_norm)
    rho_norm = max(abs(eigs_norm))
    print(f"  Eigenvalues: {eigs_norm}")
    print(f"  Spectral radius: {rho_norm:.6f}")

    return M_cond, M_norm


# ============================================================================
# FORMULATION D: Multi-digit transfer at scale k
# ============================================================================

def build_multiscale_transfer(k_max=6):
    """
    Build transfer matrices at multiple scales.

    At scale k, we track the full k-digit state: the last k digits and the
    carry propagating out. The transfer matrix acts on (residue mod 10^k, carry)
    states and maps each state to its successor under doubling.

    The "hole" version removes all states where any of the k digits is 0.
    """
    print("\n" + "="*70)
    print("FORMULATION D: Multi-scale transfer matrices")
    print("="*70)

    for k in range(1, k_max + 1):
        mod = 10**k

        # States: (residue mod 10^k, carry_out)
        # But carry_out is determined by: if 2*residue >= 10^k, carry=1, else carry=0
        # Actually for our purposes, the state IS the residue mod 10^k
        # The doubling map is: r -> (2*r) mod 10^k, with carry = (2*r) // 10^k

        # Count zeroless residues
        zeroless_count = 0
        for r in range(mod):
            temp = r
            is_zeroless = True
            for _ in range(k):
                if temp % 10 == 0:
                    is_zeroless = False
                    break
                temp //= 10
            if is_zeroless:
                zeroless_count += 1

        # The doubling map on residues mod 10^k
        # r -> 2r mod 10^k
        # This is a permutation (since gcd(2, 5^k) = 1... wait, 2 divides 10^k)
        # Actually 2r mod 10^k is NOT a permutation because 2 and 10^k share factor 2

        # Better: track which zeroless residues map to zeroless residues under doubling
        zeroless_to_zeroless = 0
        zeroless_residues = set()
        for r in range(mod):
            temp = r
            is_zeroless = True
            for _ in range(k):
                if temp % 10 == 0:
                    is_zeroless = False
                    break
                temp //= 10
            if is_zeroless:
                zeroless_residues.add(r)

        for r in zeroless_residues:
            doubled = (2 * r) % mod
            if doubled in zeroless_residues:
                zeroless_to_zeroless += 1

        fraction = zeroless_to_zeroless / zeroless_count if zeroless_count > 0 else 0

        print(f"k={k}: mod=10^{k}={mod:>10}, zeroless={zeroless_count:>10}, "
              f"zl->zl={zeroless_to_zeroless:>10}, fraction={fraction:.6f}, "
              f"(9/10)^{k}={(0.9)**k:.6f}")

    return None


# ============================================================================
# Main
# ============================================================================

if __name__ == "__main__":
    print("EXPERIMENT 1: TRANSFER OPERATOR WITH HOLE (ESCAPE RATE)")
    print("="*70)
    print()

    # Formulation A: Basic doubling transfer matrix
    T_full, T_hole = build_doubling_transfer_matrix()

    # Formulation B: 5-adic survivor counting
    results_b = build_fiveadic_transfer(k_max=8)

    # Formulation C: Conditioned transfer
    M_cond, M_norm = build_conditioned_transfer()

    # Formulation D: Multi-scale
    build_multiscale_transfer(k_max=5)

    # Summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)
    print()
    print("Formulation A (single-step doubling):")
    print(f"  Spectral radius of T_hole: {max(abs(np.linalg.eigvals(T_hole))):.4f}")
    print(f"  Ratio to T_full: {max(abs(np.linalg.eigvals(T_hole)))/max(abs(np.linalg.eigvals(T_full))):.4f}")
    print()
    print("Formulation C (conditioned transfer):")
    print(f"  Spectral radius of M_cond: {max(abs(np.linalg.eigvals(M_cond))):.4f}")
    print(f"  Ratio to unconditioned (9): {max(abs(np.linalg.eigvals(M_cond)))/9:.4f}")
    print()
    print("Key question: does the conditioned operator have spectral radius < 9?")
    print("If yes: zeroless paths decay exponentially under the carry dynamics.")
    print("If no: the 4.5^k barrier is confirmed at the operator level.")
    print()
    print("NOTE: This single-step analysis may be too coarse. The real question")
    print("is whether the MULTI-STEP transfer (across many digit positions)")
    print("shows decay. That's what Formulations B and D measure.")
