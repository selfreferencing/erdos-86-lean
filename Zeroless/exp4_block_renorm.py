#!/usr/bin/env python3
import sys
sys.set_int_max_str_digits(100000)
"""
EXPERIMENT 4: Block Renormalization

Synthesis motivation: M4-B's "renormalization across digit scales" and "cross-scale
extinction" ideas. Can blocking digits into groups reduce the effective branching
factor below the critical threshold?

At single-digit level, branching factor is 4.5 (supercritical).
At block level B, the branching factor might decrease because carry constraints
across B positions create dependencies.
"""

import numpy as np
import os
import json
from collections import defaultdict
from itertools import product

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


def is_block_zeroless(block_digits):
    """Check if a block of digits has no zeros."""
    return all(d != 0 for d in block_digits)


def test1_block_counting():
    """
    For block sizes B = 1..6, count:
    - Total B-digit patterns (10^B)
    - Zeroless B-digit patterns (9^B)
    - Zeroless patterns reachable from 2^n (i.e., that appear as consecutive B digits in some 2^n)
    - The effective branching factor at block level
    """
    print("=" * 70)
    print("TEST 1: Block-level zeroless counting")
    print("=" * 70)

    max_n = 10000

    for B in range(1, 7):
        total_patterns = 10 ** B
        zeroless_patterns = 9 ** B
        zeroless_fraction = zeroless_patterns / total_patterns

        # Count which B-digit blocks appear in actual powers of 2
        observed_blocks = set()
        observed_zl_blocks = set()

        for n in range(1, max_n + 1):
            s = str(pow(2, n))
            k = len(s)
            # Extract all B-digit blocks (from right, non-overlapping)
            for start in range(0, k - B + 1, B):
                # From the right
                block = s[k - start - B: k - start]
                if len(block) == B:
                    observed_blocks.add(block)
                    if '0' not in block:
                        observed_zl_blocks.add(block)

        print(f"\n  Block size B={B}:")
        print(f"    Total B-digit patterns: {total_patterns}")
        print(f"    Zeroless patterns: {zeroless_patterns} ({zeroless_fraction:.6f})")
        print(f"    Patterns observed in 2^n (n=1..{max_n}): {len(observed_blocks)}")
        print(f"    Zeroless observed: {len(observed_zl_blocks)}")

        if B <= 3:
            # For small B, check if ALL zeroless patterns appear
            missing_zl = zeroless_patterns - len(observed_zl_blocks)
            print(f"    Missing zeroless patterns: {missing_zl}")

        # Effective branching factor at block level
        # At single digit: branching = 4.5 (survivor count grows by 4.5 per digit)
        # At block level B: effective branching per block = 4.5^B
        # But if carry constraints within a block reduce this...
        print(f"    Naive block branching: 4.5^{B} = {4.5**B:.2f}")
        print(f"    Zeroless/total ratio: (9/10)^{B} = {0.9**B:.6f}")


def test2_block_transition_matrix():
    """
    Build a transition matrix for block-level doubling.
    State: a B-digit block. Transition: what block follows when doubling.
    """
    print("\n" + "=" * 70)
    print("TEST 2: Block transition analysis under doubling")
    print("=" * 70)

    for B in [1, 2, 3]:
        print(f"\n  Block size B={B}:")

        # For each B-digit block, compute what doubling produces
        # When we double a number, the block at position j becomes:
        # new_block = (2 * old_value_in_block + carry_in) mod 10^B
        # carry_out = (2 * old_value_in_block + carry_in) // 10^B

        mod = 10 ** B
        # Count: for each (block_val, carry_in) -> (new_block_val, carry_out)
        zl_to_zl = 0
        zl_to_total = 0
        any_to_zl = 0
        total_transitions = 0

        for block_val in range(mod):
            block_str = str(block_val).zfill(B)
            is_zl_in = '0' not in block_str

            for carry_in in [0, 1]:
                doubled = 2 * block_val + carry_in
                new_block = doubled % mod
                carry_out = doubled // mod

                new_str = str(new_block).zfill(B)
                is_zl_out = '0' not in new_str

                total_transitions += 1
                if is_zl_out:
                    any_to_zl += 1
                if is_zl_in:
                    zl_to_total += 1
                    if is_zl_out:
                        zl_to_zl += 1

        p_zl_given_zl = zl_to_zl / zl_to_total if zl_to_total > 0 else 0
        p_zl_any = any_to_zl / total_transitions
        naive_p = 0.9 ** B

        print(f"    P(output zeroless | input zeroless): {p_zl_given_zl:.6f}")
        print(f"    P(output zeroless | any input):      {p_zl_any:.6f}")
        print(f"    Naive (9/10)^{B}:                     {naive_p:.6f}")
        print(f"    Ratio conditioned/naive:              {p_zl_given_zl/naive_p:.4f}")

        # Carry distribution from zeroless blocks
        carry_from_zl = defaultdict(int)
        for block_val in range(mod):
            block_str = str(block_val).zfill(B)
            if '0' in block_str:
                continue
            for carry_in in [0, 1]:
                doubled = 2 * block_val + carry_in
                carry_out = doubled // mod
                carry_from_zl[carry_out] += 1

        total_zl_carry = sum(carry_from_zl.values())
        print(f"    Carry distribution from zeroless blocks:")
        for c in sorted(carry_from_zl.keys()):
            print(f"      carry_out={c}: {carry_from_zl[c]}/{total_zl_carry} = "
                  f"{carry_from_zl[c]/total_zl_carry:.4f}")


def test3_block_level_survivors():
    """
    At block level B, compute the survivor set: which residue classes mod T_k
    give B*k zeroless trailing digits when grouped into B-blocks?

    Compare: is the effective branching at block level lower than 4.5^B?
    """
    print("\n" + "=" * 70)
    print("TEST 3: Block-level survivor counting")
    print("=" * 70)

    for B in [2, 3, 4, 5]:
        print(f"\n  Block size B={B}:")
        print(f"  Survivors with B*k = {B}*k contiguous zeroless trailing digits:")

        for k_blocks in range(1, min(5, 1 + 7 // B)):
            k_digits = B * k_blocks
            mod = 10 ** k_digits
            period = 4 * (5 ** (k_digits - 1))

            if period > 5000000:
                print(f"    k_blocks={k_blocks} (k_digits={k_digits}): period {period} too large, skipping")
                continue

            survivor_count = 0
            for n in range(k_digits, k_digits + period):
                r = pow(2, n, mod)
                s = str(r).zfill(k_digits)
                if '0' not in s:
                    survivor_count += 1

            density = survivor_count / period
            expected_density = (9 / 10) ** k_digits
            naive_block_branching = (4.5 ** B) ** k_blocks

            print(f"    k_blocks={k_blocks} (k_digits={k_digits}): "
                  f"period={period}, survivors={survivor_count}, "
                  f"density={density:.6f}, (9/10)^{k_digits}={expected_density:.6f}")


def test4_block_entropy():
    """
    Compute the entropy of B-digit blocks in powers of 2.
    If blocking creates dependencies, entropy will be less than B * log2(10).
    """
    print("\n" + "=" * 70)
    print("TEST 4: Block entropy analysis")
    print("=" * 70)

    max_n = 5000

    for B in [1, 2, 3, 4, 5]:
        block_counts = defaultdict(int)
        total_blocks = 0

        for n in range(100, max_n + 1):
            s = str(pow(2, n))
            k = len(s)

            # Non-overlapping blocks from the right
            for start in range(0, k - B + 1, B):
                block = s[k - start - B: k - start]
                if len(block) == B:
                    block_counts[block] += 1
                    total_blocks += 1

        # Compute entropy
        probs = np.array([c / total_blocks for c in block_counts.values()])
        entropy = -np.sum(probs * np.log2(probs))
        max_entropy = B * np.log2(10)
        efficiency = entropy / max_entropy

        # Count zeroless blocks
        zl_count = sum(c for b, c in block_counts.items() if '0' not in b)
        zl_frac = zl_count / total_blocks

        print(f"\n  B={B}: {total_blocks} total blocks, {len(block_counts)} unique patterns")
        print(f"    Entropy: {entropy:.4f} bits (max: {max_entropy:.4f}, efficiency: {efficiency:.6f})")
        print(f"    Zeroless fraction: {zl_frac:.6f} (expected: {0.9**B:.6f})")

        # Check: are zeroless blocks equally likely?
        zl_blocks = {b: c for b, c in block_counts.items() if '0' not in b}
        if zl_blocks:
            zl_probs = np.array([c / zl_count for c in zl_blocks.values()])
            zl_entropy = -np.sum(zl_probs * np.log2(zl_probs))
            zl_max_entropy = np.log2(9 ** B)
            zl_efficiency = zl_entropy / zl_max_entropy if zl_max_entropy > 0 else 0
            print(f"    Zeroless block entropy: {zl_entropy:.4f} bits "
                  f"(max: {zl_max_entropy:.4f}, efficiency: {zl_efficiency:.6f})")


def test5_renormalization_branching():
    """
    The key test: at block level B, what is the effective branching factor
    of the survivor tree? If it drops below 1 per block, blocking helps.
    """
    print("\n" + "=" * 70)
    print("TEST 5: Renormalized branching factor")
    print("=" * 70)

    for B in [2, 3, 4, 5]:
        print(f"\n  Block size B={B}:")
        print(f"    Single-digit branching: 4.5")
        print(f"    Naive B-block branching: 4.5^{B} = {4.5**B:.2f}")

        # Compute actual block-level survivor growth
        # At digit level k, survivors = 4 * 4.5^{k-1}
        # At block level k/B, the question is: does the block-level count
        # grow as (4.5^B)^{k/B} or slower?

        # We compute survivor counts at k = B, 2B, 3B, ...
        prev_count = None
        print(f"    {'k_digits':>10}  {'survivors':>12}  {'block_growth':>14}  {'per_digit':>12}")
        print("    " + "-" * 55)

        for m in range(1, min(5, 1 + 8 // B)):
            k = B * m
            period = 4 * (5 ** (k - 1))

            if period > 2000000:
                break

            count = 0
            for n in range(k, k + period):
                r = pow(2, n, period * (2 ** k) if period * (2 ** k) < 10 ** k else 10 ** k)
                # Actually just use 10^k
                r = pow(2, n, 10 ** k)
                s = str(r).zfill(k)
                if '0' not in s:
                    count += 1

            if prev_count is not None and prev_count > 0:
                block_growth = count / prev_count
                per_digit_growth = block_growth ** (1.0 / B)
            else:
                block_growth = float('nan')
                per_digit_growth = float('nan')

            print(f"    {k:10d}  {count:12d}  {block_growth:14.4f}  {per_digit_growth:12.4f}")
            prev_count = count


if __name__ == "__main__":
    print("EXPERIMENT 4: BLOCK RENORMALIZATION")
    print("=" * 70)

    test1_block_counting()
    test2_block_transition_matrix()
    test3_block_level_survivors()
    test4_block_entropy()
    test5_renormalization_branching()

    print(f"\n{'='*70}")
    print("EXPERIMENT 4 COMPLETE")
    print(f"{'='*70}")
