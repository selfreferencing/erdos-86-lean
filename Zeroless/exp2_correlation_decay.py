#!/usr/bin/env python3
"""
EXPERIMENT 2: Carry Correlation Decay

Synthesis motivation: The probabilist's two-step innovation template (Section 12).
Step 1: prove the carry-digit constraint has uniformly short correlation length.

The "doubling with carry" process is a Markov chain on (carry, digit) states.
We measure:
1. Correlation between digits at positions j and j+m in 2^n
2. Dobrushin contraction coefficient of the carry chain
3. Mixing time of the carry Markov chain
4. Whether influence of boundary conditions decays exponentially

For the SPECIFIC initial conditions coming from 2^n (not random), measure
whether correlation decay still holds (probes "deterministic typicality").
"""

import numpy as np
import os
from collections import defaultdict

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")


def test1_carry_markov_chain():
    """
    The carry chain for doubling: state = carry value (0 or 1).
    When doubling a number with digit d and carry_in c:
      2*d + c = new_digit + 10*carry_out

    For d uniform on {0,...,9}:
      carry_out = 1 iff 2*d + c >= 10, i.e., d >= (10-c)/2
      P(carry_out=1 | carry_in=0) = P(d >= 5) = 5/10 = 1/2
      P(carry_out=1 | carry_in=1) = P(d >= 4.5) = P(d >= 5) = 5/10 = 1/2
      Wait: 2*d+1 >= 10 => d >= 4.5 => d >= 5, so P = 5/10 = 1/2

    For d uniform on {1,...,9} (zeroless digits):
      P(carry_out=1 | carry_in=0) = #{d in {1..9}: 2d >= 10} / 9 = #{5,6,7,8,9}/9 = 5/9
      P(carry_out=1 | carry_in=1) = #{d in {1..9}: 2d+1 >= 10} / 9 = #{d: d >= 4.5} = #{5,6,7,8,9}/9 = 5/9

    Interesting: the carry chain is MEMORYLESS for uniform zeroless digits!
    P(carry_out=1) = 5/9 regardless of carry_in.
    """
    print("=" * 70)
    print("TEST 1: Carry Markov chain for doubling")
    print("=" * 70)

    # Build transition matrix for carry chain
    # State: carry value (0 or 1)
    # For each input digit d in {1,...,9} (zeroless), compute carry_out

    print("\nUniform digits {0,...,9}:")
    for c_in in [0, 1]:
        count_1 = sum(1 for d in range(10) if (2 * d + c_in) >= 10)
        print(f"  P(c_out=1 | c_in={c_in}) = {count_1}/10 = {count_1/10:.4f}")

    print("\nZeroless digits {1,...,9}:")
    for c_in in [0, 1]:
        count_1 = sum(1 for d in range(1, 10) if (2 * d + c_in) >= 10)
        print(f"  P(c_out=1 | c_in={c_in}) = {count_1}/9 = {count_1/9:.4f}")

    print("\n  KEY FINDING: For zeroless digits, the carry chain is MEMORYLESS.")
    print("  P(c_out=1) = 5/9 regardless of c_in.")
    print("  This means carries decorrelate INSTANTLY (mixing time = 0).")

    # Now check: what about the OUTPUT digit? Given carry_in, is the output
    # digit distribution the same?
    print("\nOutput digit distribution given carry_in (for zeroless input d in {1,...,9}):")
    for c_in in [0, 1]:
        digit_counts = defaultdict(int)
        for d in range(1, 10):
            out_d = (2 * d + c_in) % 10
            digit_counts[out_d] += 1
        print(f"\n  carry_in={c_in}:")
        for out_d in range(10):
            if digit_counts[out_d] > 0:
                print(f"    output digit {out_d}: {digit_counts[out_d]}/9 = {digit_counts[out_d]/9:.4f}")

    # Now check the CONDITIONED chain: only zeroless outputs
    print("\nConditioned on output != 0:")
    for c_in in [0, 1]:
        digit_counts = defaultdict(int)
        total = 0
        for d in range(1, 10):
            out_d = (2 * d + c_in) % 10
            if out_d != 0:
                digit_counts[out_d] += 1
                total += 1
        print(f"\n  carry_in={c_in}: {total}/9 outputs are nonzero")
        for out_d in sorted(digit_counts.keys()):
            print(f"    output digit {out_d}: {digit_counts[out_d]}/{total} = {digit_counts[out_d]/total:.4f}")


def test2_digit_correlation_in_powers():
    """
    For actual powers of 2, measure correlation between digit d_j and d_{j+m}
    as a function of separation m.

    If digits were independent, correlation would be 0.
    Carry dynamics might create short-range correlations.
    """
    print("\n" + "=" * 70)
    print("TEST 2: Digit-digit correlation in 2^n")
    print("=" * 70)

    max_n = 5000
    max_sep = 50
    # For each separation m, collect pairs (d_j, d_{j+m}) and compute correlation

    pair_sums = defaultdict(lambda: [0.0, 0.0, 0.0, 0.0, 0])  # [sum_x, sum_y, sum_xy, sum_x2, count]

    for n in range(100, max_n + 1):  # Start at 100 to have enough digits
        s = str(pow(2, n))
        digits = [int(c) for c in s]

        for m in range(1, min(max_sep + 1, len(digits))):
            for j in range(len(digits) - m):
                d_j = digits[j]
                d_jm = digits[j + m]
                stats = pair_sums[m]
                stats[0] += d_j
                stats[1] += d_jm
                stats[2] += d_j * d_jm
                stats[3] += d_j * d_j
                stats[4] += 1

    print(f"\nCorrelation between digits at separation m (n=100..{max_n}):")
    print(f"{'m':>4}  {'corr':>10}  {'n_pairs':>10}")
    print("-" * 30)

    correlations = []
    for m in range(1, max_sep + 1):
        stats = pair_sums[m]
        count = stats[4]
        if count == 0:
            continue
        mean_x = stats[0] / count
        mean_y = stats[1] / count
        mean_xy = stats[2] / count
        mean_x2 = stats[3] / count

        var_x = mean_x2 - mean_x ** 2
        cov_xy = mean_xy - mean_x * mean_y

        if var_x > 0:
            corr = cov_xy / var_x  # Using var_x for both since same distribution
        else:
            corr = 0.0

        correlations.append((m, corr))
        if m <= 20 or m % 10 == 0:
            print(f"{m:4d}  {corr:10.6f}  {count:10d}")

    # Check if correlation decays exponentially
    if len(correlations) > 5:
        # Fit log|corr| vs m for m=1..20
        ms = [c[0] for c in correlations[:20] if abs(c[1]) > 1e-10]
        log_corrs = [np.log(abs(c[1])) for c in correlations[:20] if abs(c[1]) > 1e-10]
        if len(ms) > 2:
            fit = np.polyfit(ms, log_corrs, 1)
            decay_rate = -fit[0]
            corr_length = 1.0 / decay_rate if decay_rate > 0 else float('inf')
            print(f"\nExponential fit: |corr| ~ exp(-m/{corr_length:.2f})")
            print(f"  Decay rate: {decay_rate:.4f}")
            print(f"  Correlation length: {corr_length:.2f}")


def test3_conditional_digit_distribution():
    """
    Given digit d at position j, what is the distribution of the digit at position j+1?
    This measures the strength of carry-induced correlations.

    For truly independent digits, P(d_{j+1} = a | d_j = b) = P(d_{j+1} = a) for all a, b.
    """
    print("\n" + "=" * 70)
    print("TEST 3: Conditional digit distributions in 2^n")
    print("=" * 70)

    max_n = 5000
    # transition_counts[d_j][d_{j+1}] counts
    transition_counts = [[0] * 10 for _ in range(10)]
    total_by_digit = [0] * 10

    for n in range(100, max_n + 1):
        s = str(pow(2, n))
        for j in range(len(s) - 1):
            d_j = int(s[j])
            d_j1 = int(s[j + 1])
            transition_counts[d_j][d_j1] += 1
            total_by_digit[d_j] += 1

    print(f"\nTransition probabilities P(d_{{j+1}} | d_j) for 2^n, n=100..{max_n}:")
    print(f"      ", end="")
    for a in range(10):
        print(f"  d+1={a}", end="")
    print()
    print("-" * 80)

    for b in range(10):
        print(f"d={b}:  ", end="")
        for a in range(10):
            if total_by_digit[b] > 0:
                prob = transition_counts[b][a] / total_by_digit[b]
                print(f"  {prob:.4f}", end="")
            else:
                print(f"   ---  ", end="")
        print()

    # Compute max deviation from uniform (1/10 for each digit)
    print(f"\nMax deviation from uniform (1/10) for each conditioning digit:")
    max_dev = 0
    for b in range(10):
        if total_by_digit[b] > 0:
            devs = [abs(transition_counts[b][a] / total_by_digit[b] - 0.1) for a in range(10)]
            md = max(devs)
            if md > max_dev:
                max_dev = md
            print(f"  d={b}: max_dev = {md:.6f}")
    print(f"  Overall max deviation: {max_dev:.6f}")


def test4_correlation_from_right():
    """
    Since carry propagation goes left-to-right in the multiplication,
    correlations might be stronger when measured from the RIGHT (least significant digit).

    Measure correlation between digits at positions j and j+m from the RIGHT.
    """
    print("\n" + "=" * 70)
    print("TEST 4: Digit correlation from the RIGHT (carry direction)")
    print("=" * 70)

    max_n = 5000
    max_sep = 30

    pair_sums = defaultdict(lambda: [0.0, 0.0, 0.0, 0.0, 0])

    for n in range(100, max_n + 1):
        s = str(pow(2, n))
        digits = [int(c) for c in reversed(s)]  # LSB first

        for m in range(1, min(max_sep + 1, len(digits))):
            for j in range(len(digits) - m):
                d_j = digits[j]
                d_jm = digits[j + m]
                stats = pair_sums[m]
                stats[0] += d_j
                stats[1] += d_jm
                stats[2] += d_j * d_jm
                stats[3] += d_j * d_j
                stats[4] += 1

    print(f"\nCorrelation between digits at separation m FROM RIGHT (n=100..{max_n}):")
    print(f"{'m':>4}  {'corr':>10}  {'n_pairs':>10}")
    print("-" * 30)

    for m in range(1, max_sep + 1):
        stats = pair_sums[m]
        count = stats[4]
        if count == 0:
            continue
        mean_x = stats[0] / count
        mean_y = stats[1] / count
        mean_xy = stats[2] / count
        mean_x2 = stats[3] / count

        var_x = mean_x2 - mean_x ** 2
        cov_xy = mean_xy - mean_x * mean_y

        if var_x > 0:
            corr = cov_xy / var_x
        else:
            corr = 0.0

        print(f"{m:4d}  {corr:10.6f}  {count:10d}")


def test5_zeroless_conditioned_correlation():
    """
    Among digits that are all nonzero (the trailing zeroless suffix),
    measure correlation between consecutive digits.

    This directly probes whether the carry constraint induces detectable
    correlations WITHIN the zeroless region.
    """
    print("\n" + "=" * 70)
    print("TEST 5: Correlations within zeroless trailing suffix")
    print("=" * 70)

    max_n = 10000
    max_sep = 20

    pair_sums = defaultdict(lambda: [0.0, 0.0, 0.0, 0.0, 0])

    for n in range(100, max_n + 1):
        s = str(pow(2, n))
        digits_from_right = [int(c) for c in reversed(s)]

        # Find zeroless suffix length
        suffix_len = 0
        for d in digits_from_right:
            if d == 0:
                break
            suffix_len += 1

        if suffix_len < 3:
            continue

        # Measure correlations within the suffix
        suffix = digits_from_right[:suffix_len]
        for m in range(1, min(max_sep + 1, suffix_len)):
            for j in range(suffix_len - m):
                d_j = suffix[j]
                d_jm = suffix[j + m]
                stats = pair_sums[m]
                stats[0] += d_j
                stats[1] += d_jm
                stats[2] += d_j * d_jm
                stats[3] += d_j * d_j
                stats[4] += 1

    print(f"\nCorrelation within zeroless suffix at separation m (n=100..{max_n}):")
    print(f"{'m':>4}  {'corr':>10}  {'n_pairs':>10}")
    print("-" * 30)

    for m in range(1, max_sep + 1):
        stats = pair_sums[m]
        count = stats[4]
        if count == 0:
            continue
        mean_x = stats[0] / count
        mean_y = stats[1] / count
        mean_xy = stats[2] / count
        mean_x2 = stats[3] / count

        var_x = mean_x2 - mean_x ** 2
        cov_xy = mean_xy - mean_x * mean_y

        if var_x > 0:
            corr = cov_xy / var_x
        else:
            corr = 0.0

        print(f"{m:4d}  {corr:10.6f}  {count:10d}")


def test6_dobrushin_coefficient():
    """
    Compute the Dobrushin contraction coefficient for the carry Markov chain.

    For a Markov chain with transition matrix P, the Dobrushin coefficient is:
    delta(P) = (1/2) * max_{i,j} sum_k |P(i,k) - P(j,k)|

    If delta < 1, the chain contracts at rate (1-delta) per step.
    """
    print("\n" + "=" * 70)
    print("TEST 6: Dobrushin contraction coefficient")
    print("=" * 70)

    # Carry chain for uniform digits {0,...,9}
    P_uniform = np.zeros((2, 2))
    for c_in in [0, 1]:
        for d in range(10):
            c_out = 1 if (2 * d + c_in) >= 10 else 0
            P_uniform[c_in][c_out] += 1.0 / 10

    print("Carry chain (uniform digits {0,...,9}):")
    print(f"  P = {P_uniform}")
    delta_uniform = 0.5 * np.max([
        np.sum(np.abs(P_uniform[i] - P_uniform[j]))
        for i in range(2) for j in range(2)
    ])
    print(f"  Dobrushin coefficient: {delta_uniform:.6f}")
    print(f"  Contraction rate: {1 - delta_uniform:.6f}")

    # Carry chain for zeroless digits {1,...,9}
    P_zeroless = np.zeros((2, 2))
    for c_in in [0, 1]:
        for d in range(1, 10):
            c_out = 1 if (2 * d + c_in) >= 10 else 0
            P_zeroless[c_in][c_out] += 1.0 / 9

    print(f"\nCarry chain (zeroless digits {{1,...,9}}):")
    print(f"  P = {P_zeroless}")
    delta_zeroless = 0.5 * np.max([
        np.sum(np.abs(P_zeroless[i] - P_zeroless[j]))
        for i in range(2) for j in range(2)
    ])
    print(f"  Dobrushin coefficient: {delta_zeroless:.6f}")
    print(f"  Contraction rate: {1 - delta_zeroless:.6f}")

    if delta_zeroless == 0:
        print("  >>> Dobrushin coefficient = 0: PERFECT mixing in ONE step!")
        print("  >>> The carry chain is completely memoryless for zeroless digits.")

    # Carry chain conditioned on output being nonzero
    print(f"\nConditioned carry chain (zeroless input AND output):")
    P_cond = np.zeros((2, 2))
    norm = np.zeros(2)
    for c_in in [0, 1]:
        for d in range(1, 10):
            out_d = (2 * d + c_in) % 10
            c_out = (2 * d + c_in) // 10
            if out_d != 0:
                P_cond[c_in][c_out] += 1.0
                norm[c_in] += 1.0
    for c_in in [0, 1]:
        if norm[c_in] > 0:
            P_cond[c_in] /= norm[c_in]

    print(f"  P_cond = {P_cond}")
    print(f"  Normalization (num nonzero outputs): c_in=0: {int(norm[0])}/9, c_in=1: {int(norm[1])}/9")

    delta_cond = 0.5 * np.max([
        np.sum(np.abs(P_cond[i] - P_cond[j]))
        for i in range(2) for j in range(2)
    ])
    print(f"  Dobrushin coefficient: {delta_cond:.6f}")
    print(f"  Contraction rate: {1 - delta_cond:.6f}")

    if delta_cond > 0:
        mixing_time = int(np.ceil(np.log(2) / np.log(1.0 / delta_cond)))
        print(f"  Estimated mixing time: {mixing_time} steps")


def test7_actual_carry_statistics():
    """
    For actual 2^n, compute the carry chain when going from 2^{n-1} to 2^n,
    and check if carries are distributed as the memoryless model predicts.
    """
    print("\n" + "=" * 70)
    print("TEST 7: Actual carry statistics in 2^n")
    print("=" * 70)

    max_n = 5000

    carry_counts = defaultdict(int)
    carry_transitions = defaultdict(lambda: defaultdict(int))
    carry_run_lengths = []

    for n in range(2, max_n + 1):
        prev = pow(2, n - 1)
        digits = [int(c) for c in str(prev)][::-1]  # LSB first

        carry = 0
        prev_carry = None
        run_len = 0

        for d in digits:
            s = 2 * d + carry
            new_carry = s // 10

            carry_counts[new_carry] += 1
            if prev_carry is not None:
                carry_transitions[prev_carry][new_carry] += 1

            if prev_carry is not None and new_carry == prev_carry:
                run_len += 1
            else:
                if run_len > 0:
                    carry_run_lengths.append(run_len)
                run_len = 1

            prev_carry = new_carry
            carry = new_carry

        if run_len > 0:
            carry_run_lengths.append(run_len)

    total_carries = sum(carry_counts.values())
    print(f"\nCarry statistics for doubling 2^{{n-1}} -> 2^n, n=2..{max_n}:")
    print(f"  Total digit positions processed: {total_carries}")
    print(f"  P(carry=0) = {carry_counts[0]/total_carries:.6f} (expected: 4/9 = {4/9:.6f})")
    print(f"  P(carry=1) = {carry_counts[1]/total_carries:.6f} (expected: 5/9 = {5/9:.6f})")

    print(f"\nCarry transition matrix (empirical):")
    for c_from in [0, 1]:
        total_from = sum(carry_transitions[c_from].values())
        if total_from > 0:
            for c_to in [0, 1]:
                prob = carry_transitions[c_from][c_to] / total_from
                print(f"  P(c_out={c_to} | c_in={c_from}) = {prob:.6f}")

    print(f"\nCarry run length statistics:")
    if carry_run_lengths:
        run_arr = np.array(carry_run_lengths)
        print(f"  Mean run length: {run_arr.mean():.4f}")
        print(f"  Max run length: {run_arr.max()}")
        percentiles = [50, 90, 95, 99]
        for p in percentiles:
            print(f"  {p}th percentile: {np.percentile(run_arr, p):.1f}")


if __name__ == "__main__":
    print("EXPERIMENT 2: CARRY CORRELATION DECAY")
    print("=" * 70)

    test1_carry_markov_chain()
    test2_digit_correlation_in_powers()
    test3_conditional_digit_distribution()
    test4_correlation_from_right()
    test5_zeroless_conditioned_correlation()
    test6_dobrushin_coefficient()
    test7_actual_carry_statistics()

    print("\n" + "=" * 70)
    print("EXPERIMENT 2 COMPLETE")
    print("=" * 70)
