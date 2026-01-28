#!/usr/bin/env python3
"""
EXPERIMENT 3: Triple Constraint (x, 2x, 4x)

Synthesis motivation: Section 8 "3 samples enrichment" -- treat the ~3 exponents
per digit level as a single rigid object. If x, 2x, and 4x must ALL be zeroless,
the carry constraints compound drastically.

Key insight: 2^{n+1} = 2 * 2^n and 2^{n+2} = 4 * 2^n. If 2^n is zeroless and
has k digits, the carry pattern from doubling must be highly constrained. Can it
be constrained enough to force a zero?

Tests:
1. For which n are 2^n, 2^{n+1}, 2^{n+2} ALL zeroless?
2. For which n are 2^n AND 2^{n+1} both zeroless?
3. What is the max suffix depth where triples/pairs survive?
4. For random zeroless numbers x, how often is 2x also zeroless? 4x?
"""

import json
import os
from collections import defaultdict

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


def is_zeroless(n):
    """Check if n has no digit 0 in its decimal expansion."""
    if n == 0:
        return False
    s = str(n)
    return '0' not in s


def zeroless_suffix_depth(n):
    """
    How many trailing digits of n are all nonzero?
    Returns the largest k such that the last k digits are all in {1,...,9}.
    """
    s = str(n)
    depth = 0
    for ch in reversed(s):
        if ch == '0':
            break
        depth += 1
    return depth


def test1_consecutive_zeroless_powers():
    """
    Find all n where 2^n, 2^{n+1}, 2^{n+2} are ALL zeroless.
    Also find pairs where 2^n and 2^{n+1} are both zeroless.
    """
    print("=" * 70)
    print("TEST 1: Consecutive zeroless powers of 2")
    print("=" * 70)

    max_n = 200  # Only need to go past 86
    powers = {}
    for n in range(0, max_n + 1):
        powers[n] = pow(2, n)

    zeroless_ns = []
    for n in range(0, max_n + 1):
        if is_zeroless(powers[n]):
            zeroless_ns.append(n)

    print(f"\nAll zeroless 2^n for n=0..{max_n}:")
    print(f"  {zeroless_ns}")
    print(f"  Count: {len(zeroless_ns)}")
    print(f"  Max n: {max(zeroless_ns)}")

    # Find consecutive pairs
    pairs = []
    for i in range(len(zeroless_ns) - 1):
        if zeroless_ns[i + 1] == zeroless_ns[i] + 1:
            pairs.append((zeroless_ns[i], zeroless_ns[i + 1]))

    print(f"\nConsecutive pairs (2^n and 2^{{n+1}} both zeroless):")
    for a, b in pairs:
        print(f"  n={a},{b}: 2^{a}={powers[a]}, 2^{b}={powers[b]}")
    print(f"  Total pairs: {len(pairs)}")
    if pairs:
        print(f"  Last pair starts at n={pairs[-1][0]}")

    # Find consecutive triples
    triples = []
    for i in range(len(zeroless_ns) - 2):
        if (zeroless_ns[i + 1] == zeroless_ns[i] + 1 and
                zeroless_ns[i + 2] == zeroless_ns[i] + 2):
            triples.append((zeroless_ns[i], zeroless_ns[i + 1], zeroless_ns[i + 2]))

    print(f"\nConsecutive triples (2^n, 2^{{n+1}}, 2^{{n+2}} all zeroless):")
    for a, b, c in triples:
        print(f"  n={a},{b},{c}: 2^{a}={powers[a]}, 2^{b}={powers[b]}, 2^{c}={powers[c]}")
    print(f"  Total triples: {len(triples)}")
    if triples:
        print(f"  Last triple starts at n={triples[-1][0]}")

    # Find quadruples
    quads = []
    for i in range(len(zeroless_ns) - 3):
        if all(zeroless_ns[i + j + 1] == zeroless_ns[i] + j + 1 for j in range(3)):
            quads.append(tuple(zeroless_ns[i + j] for j in range(4)))

    print(f"\nConsecutive quadruples:")
    for q in quads:
        print(f"  n={q}")
    print(f"  Total quadruples: {len(quads)}")

    return zeroless_ns, pairs, triples


def test2_suffix_depth_pairs():
    """
    For each digit count k, check whether any n has 2^n AND 2^{n+1} both
    with k zeroless trailing digits.

    More precisely: check whether there exists n such that:
    - 2^n mod 10^k has all nonzero digits (when written as k digits)
    - 2^{n+1} mod 10^k has all nonzero digits
    """
    print("\n" + "=" * 70)
    print("TEST 2: Paired suffix depth")
    print("=" * 70)
    print("For each k, find n where BOTH 2^n and 2^{n+1} have k nonzero trailing digits")

    max_k = 10  # Go up to 10 digits (period up to 4*5^9 ~ 7.8M)

    for k in range(1, max_k + 1):
        mod = 10 ** k
        period = 4 * (5 ** (k - 1))

        # Check all n in one period (for n >= k, 2^n mod 10^k is periodic with this period)
        pair_count = 0
        examples = []

        for n in range(k, k + period):
            r1 = pow(2, n, mod)
            r2 = pow(2, n + 1, mod)

            # Check if all k digits are nonzero
            s1 = str(r1).zfill(k)
            s2 = str(r2).zfill(k)

            if '0' not in s1 and '0' not in s2:
                pair_count += 1
                if len(examples) < 3:
                    examples.append(n)

        # Expected: if independent, (9/10)^k * (9/10)^k = (9/10)^{2k} fraction of period
        expected = period * (0.9 ** (2 * k))

        print(f"\n  k={k}: period={period}")
        print(f"    Paired survivors: {pair_count}")
        print(f"    Expected (independent): {expected:.1f}")
        print(f"    Ratio actual/expected: {pair_count / expected:.4f}" if expected > 0.01 else
              f"    Expected too small for ratio")
        if examples:
            print(f"    First examples: n={examples}")


def test3_doubling_zeroless_fraction():
    """
    Among all k-digit zeroless numbers, what fraction have 2x also zeroless?
    What fraction have both 2x and 4x zeroless?

    This measures the "carry rigidity" effect directly.
    """
    print("\n" + "=" * 70)
    print("TEST 3: Doubling zeroless numbers")
    print("=" * 70)
    print("For k-digit zeroless numbers x: fraction where 2x, 4x are also zeroless")

    for k in range(1, 8):  # k up to 7 (9^7 ~ 4.8M zeroless numbers)
        lo = 10 ** (k - 1)
        hi = 10 ** k

        total_zl = 0
        double_zl = 0
        quad_zl = 0
        triple_zl = 0  # x, 2x, 4x all zeroless

        # Iterate over all zeroless k-digit numbers
        # For efficiency, generate them directly
        if k <= 6:
            for x in range(lo, hi):
                if not is_zeroless(x):
                    continue
                total_zl += 1
                d = is_zeroless(2 * x)
                q = is_zeroless(4 * x)
                if d:
                    double_zl += 1
                if q:
                    quad_zl += 1
                if d and q:
                    triple_zl += 1
        else:
            # Sample for large k
            import random
            random.seed(42)
            sample_size = 100000
            for _ in range(sample_size):
                digits = [random.randint(1, 9) for _ in range(k)]
                x = int(''.join(str(d) for d in digits))
                total_zl += 1
                d = is_zeroless(2 * x)
                q = is_zeroless(4 * x)
                if d:
                    double_zl += 1
                if q:
                    quad_zl += 1
                if d and q:
                    triple_zl += 1

        frac_double = double_zl / total_zl if total_zl > 0 else 0
        frac_quad = quad_zl / total_zl if total_zl > 0 else 0
        frac_triple = triple_zl / total_zl if total_zl > 0 else 0

        # Expected if digits were independent
        # 2x has k or k+1 digits. For a k-digit zeroless x, 2x has either k or k+1 digits.
        # If k+1 digits, zeroless probability ~ (9/10)^k
        # If k digits, zeroless probability ~ (9/10)^{k-1}
        # Crude expected: (9/10)^k for the double

        method = "exact" if k <= 6 else f"sample({total_zl})"
        print(f"\n  k={k} ({method}, {total_zl} zeroless numbers):")
        print(f"    P(2x zeroless)     = {frac_double:.6f}  (naive: {0.9**(k):.6f})")
        print(f"    P(4x zeroless)     = {frac_quad:.6f}  (naive: {0.9**(k):.6f})")
        print(f"    P(2x AND 4x zl)   = {frac_triple:.6f}  (naive: {0.9**(2*k):.6f})")
        if frac_triple > 0 and 0.9 ** (2 * k) > 0:
            print(f"    Ratio triple/naive = {frac_triple / (0.9**(2*k)):.4f}")


def test4_carry_pattern_analysis():
    """
    When doubling a zeroless number x, analyze the carry pattern.
    Specifically, look at which digit positions produce carries,
    and how this correlates with whether 2x has a zero.
    """
    print("\n" + "=" * 70)
    print("TEST 4: Carry patterns when doubling zeroless numbers")
    print("=" * 70)

    for k in range(2, 7):
        lo = 10 ** (k - 1)
        hi = 10 ** k

        carry_patterns = defaultdict(lambda: [0, 0])  # pattern -> [count_zl, count_not_zl]
        zero_positions = defaultdict(int)  # position -> count of zeros at that position in 2x

        total = 0
        total_with_zero = 0

        for x in range(lo, hi):
            if not is_zeroless(x):
                continue
            total += 1

            # Compute carries when doubling
            digits = [int(c) for c in str(x)][::-1]  # LSB first
            carries = []
            carry = 0
            result_digits = []
            for d in digits:
                s = 2 * d + carry
                result_digits.append(s % 10)
                carry = s // 10
                carries.append(carry)
            if carry > 0:
                result_digits.append(carry)

            doubled = 2 * x
            has_zero = not is_zeroless(doubled)
            if has_zero:
                total_with_zero += 1

            carry_tuple = tuple(carries)
            if has_zero:
                carry_patterns[carry_tuple][1] += 1
            else:
                carry_patterns[carry_tuple][0] += 1

            # Track zero positions in 2x
            if has_zero:
                s = str(doubled)
                for pos, ch in enumerate(s):
                    if ch == '0':
                        zero_positions[len(s) - 1 - pos] += 1  # position from right

        print(f"\n  k={k}: {total} zeroless inputs, {total_with_zero} produce a zero in 2x "
              f"({total_with_zero/total:.4f})")

        # Show most common carry patterns and their zero-production rate
        sorted_patterns = sorted(carry_patterns.items(),
                                 key=lambda x: sum(x[1]), reverse=True)[:5]
        print(f"  Top carry patterns (zl_count, zero_count):")
        for pat, (zl, nzl) in sorted_patterns:
            total_pat = zl + nzl
            print(f"    carries={pat}: {zl} zeroless, {nzl} with zero "
                  f"({nzl/(zl+nzl):.3f} zero rate)")

        if zero_positions:
            print(f"  Zero positions in 2x (from right):")
            for pos in sorted(zero_positions.keys()):
                print(f"    position {pos}: {zero_positions[pos]} times "
                      f"({zero_positions[pos]/total_with_zero:.3f} of zeros)")


def test5_max_depth_paired():
    """
    What is the maximum suffix depth at which a paired constraint survives?

    For each n, compute:
    - depth_single(n) = max k such that last k digits of 2^n are all nonzero
    - depth_paired(n) = max k such that last k digits of BOTH 2^n and 2^{n+1} are all nonzero

    Track the max of depth_paired over all n.
    """
    print("\n" + "=" * 70)
    print("TEST 5: Maximum paired suffix depth")
    print("=" * 70)

    max_n = 10000
    max_single = 0
    max_single_n = 0
    max_paired = 0
    max_paired_n = 0
    max_triple = 0
    max_triple_n = 0

    # We need to compute 2^n for large n. Use Python's arbitrary precision.
    prev_prev = None
    prev_val = None
    prev_depth = 0

    depth_paired_hist = defaultdict(int)
    depth_triple_hist = defaultdict(int)

    for n in range(0, max_n + 1):
        val = pow(2, n)
        depth = zeroless_suffix_depth(val)

        if depth > max_single:
            max_single = depth
            max_single_n = n

        if prev_val is not None:
            paired_depth = min(depth, prev_depth)
            depth_paired_hist[paired_depth] += 1
            if paired_depth > max_paired:
                max_paired = paired_depth
                max_paired_n = n - 1

        if prev_prev is not None and prev_val is not None:
            pp_depth = zeroless_suffix_depth(prev_prev)
            triple_depth = min(pp_depth, prev_depth, depth)
            depth_triple_hist[triple_depth] += 1
            if triple_depth > max_triple:
                max_triple = triple_depth
                max_triple_n = n - 2

        prev_prev = prev_val
        prev_val = val
        prev_depth = depth

    print(f"\n  Range: n = 0..{max_n}")
    print(f"\n  Max single suffix depth: {max_single} at n={max_single_n}")
    print(f"  Max paired suffix depth: {max_paired} at n={max_paired_n}")
    print(f"  Max triple suffix depth: {max_triple} at n={max_triple_n}")

    print(f"\n  Paired suffix depth distribution (depth: count):")
    for d in sorted(depth_paired_hist.keys()):
        if depth_paired_hist[d] > 0:
            print(f"    depth {d}: {depth_paired_hist[d]}")

    print(f"\n  Triple suffix depth distribution (depth: count):")
    for d in sorted(depth_triple_hist.keys()):
        if depth_triple_hist[d] > 0:
            print(f"    depth {d}: {depth_triple_hist[d]}")


def test6_orbit_based_analysis():
    """
    For each n in the 5-adic orbit, check whether n, n+1, n+2 all land in the
    survivor set at each level k. This uses the modular structure directly.
    """
    print("\n" + "=" * 70)
    print("TEST 6: Orbit-based triple survivor analysis")
    print("=" * 70)

    for k in range(1, 9):
        mod = 10 ** k
        period = 4 * (5 ** (k - 1))

        single_survivors = 0
        pair_survivors = 0
        triple_survivors = 0

        for n in range(k, k + period):
            r = pow(2, n, mod)
            s = str(r).zfill(k)
            is_surv = '0' not in s

            if is_surv:
                single_survivors += 1

                # Check n+1
                r1 = pow(2, n + 1, mod)
                s1 = str(r1).zfill(k)
                is_surv1 = '0' not in s1

                if is_surv1:
                    pair_survivors += 1

                    # Check n+2
                    r2 = pow(2, n + 2, mod)
                    s2 = str(r2).zfill(k)
                    is_surv2 = '0' not in s2

                    if is_surv2:
                        triple_survivors += 1

        density_single = single_survivors / period
        density_pair = pair_survivors / period if single_survivors > 0 else 0
        density_triple = triple_survivors / period if pair_survivors > 0 else 0

        # Expected densities if independent
        exp_single = 0.9 ** k
        exp_pair = 0.9 ** (2 * k)
        exp_triple = 0.9 ** (3 * k)

        print(f"\n  k={k}: period={period}")
        print(f"    Single survivors: {single_survivors} (density={density_single:.6f}, "
              f"expected={exp_single:.6f}, ratio={density_single/exp_single:.4f})")
        print(f"    Pair survivors:   {pair_survivors} (density={density_pair:.6f}, "
              f"expected={exp_pair:.6f}, ratio={density_pair/exp_pair:.4f}" if exp_pair > 1e-10 else
              f"    Pair survivors:   {pair_survivors}")
        print(f"    Triple survivors: {triple_survivors} (density={density_triple:.6f}, "
              f"expected={exp_triple:.6f}, ratio={density_triple/exp_triple:.4f}" if exp_triple > 1e-10 else
              f"    Triple survivors: {triple_survivors}")

        # Key ratio: P(pair) / P(single)^2  -- measures correlation
        if single_survivors > 0:
            p_single = single_survivors / period
            p_pair = pair_survivors / period
            correlation = p_pair / (p_single ** 2) if p_single > 0 else 0
            print(f"    Correlation P(pair)/P(single)^2 = {correlation:.4f} "
                  f"(1.0 = independent, >1 = positive corr)")


if __name__ == "__main__":
    print("EXPERIMENT 3: TRIPLE CONSTRAINT (x, 2x, 4x)")
    print("=" * 70)

    results = {}

    zeroless_ns, pairs, triples = test1_consecutive_zeroless_powers()
    results['test1'] = {
        'zeroless_ns': zeroless_ns,
        'pairs': pairs,
        'triples': triples,
        'max_zeroless': max(zeroless_ns) if zeroless_ns else None
    }

    test2_suffix_depth_pairs()
    test3_doubling_zeroless_fraction()
    test4_carry_pattern_analysis()
    test5_max_depth_paired()
    test6_orbit_based_analysis()

    # Save key results
    output_path = os.path.join(DATA_DIR, "exp3_results.json")
    save_results = {
        'zeroless_powers': zeroless_ns,
        'consecutive_pairs': [(a, b) for a, b in pairs],
        'consecutive_triples': [(a, b, c) for a, b, c in triples],
    }
    with open(output_path, 'w') as f:
        json.dump(save_results, f, indent=2)
    print(f"\nResults saved to {output_path}")
