#!/usr/bin/env python3
"""
Experiment 38: Carry Automaton for Quasi-Independence of F_m

MOTIVATION:
The APPROACH7 GPT response identified the Parseval/correlation identity (★):

  int_0^1 |R_m(x)|^2 dx = L*(rho_m - rho_m^2)
    + 2 * sum_{h=1}^{L-1} (L-h) * [mu(F_m ∩ (F_m - h*theta)) - rho_m^2]

This collapses the entire infinite Fourier series (including the divergent
high-frequency tail) into O(L_m) overlap measures. Under quasi-independence
(mu(F_m ∩ (F_m - h*theta)) <= (1+eps)*rho_m^2), it gives:

  ||R_m||_2 << sqrt(L_m * rho_m) ~ sqrt(m) * 0.95^m -> 0 exponentially

The APPROACH7 response sketched a "carry automaton" proof of quasi-independence:
  mu(F_m ∩ (F_m - h*theta)) asks how many alpha in [0,1) have
  both d_j(alpha) != 0 and d_j(alpha + h*theta) != 0 for j=1,...,m-1.

Since alpha + h*theta = alpha + h*log10(2), we have
  10^{m-1+alpha+h*theta} = 2^h * 10^{m-1+alpha}
so the digits of 10^{m-1+alpha+h*theta} are (approximately) the digits
of 2^h * x where x = 10^{m-1+alpha}. Multiplication by 2^h in base 10
is a finite-state carry automaton.

This experiment:
A) Builds the carry automaton for multiplication by 2^h in base 10
B) Constructs the transfer matrix counting (d_in, d_out) pairs that are both nonzero
C) Computes the spectral radius as a function of h
D) Predicts overlap ratios and compares to Exp 32 empirical data
E) Tests whether the spectral radius is strictly < 81 (the independent case)
F) Extends to h up to L_m for relevant m values

KEY QUESTIONS:
1. Is the spectral radius of the carry automaton < 81 for all h?
2. Does the predicted overlap match the empirical overlap from Exp 32?
3. How does the spectral radius depend on h?
4. Is there a uniform bound C such that overlap <= C * rho_m^2?
"""

import sys
import os
import json
import math
import time
import numpy as np
from collections import defaultdict

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

theta = math.log10(2)
C_const = 1.0 / theta  # ~ 3.32


# ======================================================================
# PART A: The carry automaton for multiplication by 2^h
# ======================================================================
#
# When we multiply an m-digit number by 2^h in base 10, we process
# digits from least significant to most significant, carrying as we go.
#
# State: the current carry value c
# Input: digit d of the original number (0-9)
# Output: digit d' of the product (0-9), where d' = (2^h * d + c) mod 10
# New carry: c' = floor((2^h * d + c) / 10)
#
# For multiplication by a general multiplier M:
# d' = (M * d + c) mod 10
# c' = floor((M * d + c) / 10)
#
# Wait - this is multiplication by M of a SINGLE DIGIT with carry.
# Actually, for multiplying a multi-digit number by M, we multiply
# each digit by M and propagate carries. But 2^h can be larger than 10.
#
# More precisely: multiplying by M means:
# For each digit d (from least significant):
#   product = M * d + carry_in
#   new_digit = product % 10
#   carry_out = product // 10
#
# But this only works for M a single digit! For M = 2^h > 9, we need
# multi-digit multiplication, which is more complex.
#
# CORRECT APPROACH: The carry automaton for multiplying by M processes
# one digit at a time:
#   carry_out = floor((M * d + carry_in) / 10)
#   output_digit = (M * d + carry_in) % 10
#
# The carry can range from 0 to floor((M * 9 + C_max) / 10).
# For M = 2^h: max carry = floor((2^h * 9) / 10) initially,
# but carries compound. The max carry is floor((M*9 + C)/(10))
# where C is the max carry. So C_max = floor((9*M + C_max)/10),
# giving C_max = floor(9*M/9) = M-1... wait, let me be more careful.
#
# M * d + c ranges from 0 (d=0,c=0) to M*9 + C_max.
# carry_out = floor((M*d + c)/10), so max carry_out = floor((9M + C_max)/10).
# For steady state: C_max = floor((9M + C_max)/10)
# => 10*C_max = 9M + C_max (ignoring floor) => C_max = M - ceil(M/10)...
# Actually: 10C = 9M + C => 9C = 9M => C = M.
# But carry_out = floor((9M + C)/10) < M when C < M.
# Let's just say carry ranges from 0 to M-1. For M = 2^h with h=20,
# carry can be up to ~10^6, which creates a large state space.
# We need a smarter approach.
#
# ALTERNATIVE: Use the CONTINUOUS formulation.
# F_m = {alpha in [0,1) : all digits of floor(10^{m-1+alpha}) are nonzero}
# F_m shifted by h*theta: F_m - h*theta = {alpha : all digits of
#   floor(10^{m-1+alpha+h*theta}) are nonzero}
#
# 10^{m-1+alpha+h*theta} = 10^{m-1+alpha} * 10^{h*theta} = 10^{m-1+alpha} * 2^h
#
# So alpha in F_m ∩ (F_m - h*theta) iff:
#   floor(10^{m-1+alpha}) has all digits nonzero AND
#   floor(10^{m-1+alpha} * 2^h) has all digits nonzero
#
# For a random x in [10^{m-1}, 10^m):
#   x has all m digits nonzero (prob ~ (9/10)^{m-1})
#   AND floor(x * 2^h) has all its digits nonzero
#
# Actually, floor(x * 2^h) has MORE digits than x (about m + h*log10(2) digits).
# We only care about the first m digits (the significand).
#
# SIMPLEST CORRECT APPROACH: Direct computation.
# For each m, enumerate all m-digit zeroless integers, multiply by 2^h,
# check if the result (truncated to its first m significant digits) is zeroless.
# This gives the exact overlap count.
#
# But this is expensive for large m. For m=7, there are 9^6 = 531441 zeroless
# integers. For m=10, there are 9^9 ~ 387 million. Too many.
#
# TRANSFER MATRIX APPROACH (for the carry automaton):
# Process digits from MOST significant to LEAST significant.
# State = (carry_into_next_position, whether_we've_seen_a_zero_in_output)
#
# Actually, the multiplication by 2^h digit-by-digit with carry is the right
# idea, but we need to handle it as a matrix recursion.
#
# For each digit position j (j=1 is most significant):
#   The input digit d_j is in {1,...,9} (zeroless condition on x)
#   The output digit e_j depends on d_j and the carry from position j+1
#   We need e_j in {1,...,9} (zeroless condition on 2^h * x's significand)
#   The carry propagates to position j-1
#
# But the issue is: carries propagate from LEAST significant to MOST significant.
# So we process right to left: j = m, m-1, ..., 1.
#
# State: carry value c (ranges 0 to M-1 for multiplier M=2^h)
# At each position j, input digit d_j in {1,...,9}:
#   product = M * d_j + c
#   output_digit = product % 10
#   carry_out = product // 10
# We need output_digit in {1,...,9} (nonzero)
#
# Transfer matrix T[c_out, c_in] = number of input digits d in {1,...,9}
# such that (M*d + c_in) mod 10 != 0 and floor((M*d + c_in)/10) = c_out.
#
# Wait, we need to track BOTH conditions: input digit nonzero AND output digit
# nonzero. Since input digits are already restricted to {1,...,9}, we just
# need to count how many of these produce nonzero output digit.
#
# Actually, the transfer matrix approach counts the number of m-digit
# strings (d_1,...,d_m) in {1,...,9}^m such that the multiplication
# 2^h * (d_1 d_2 ... d_m) produces all nonzero digits in the first m
# positions of the output. The transfer matrix T_h has size C_max x C_max
# where C_max is the number of possible carry values.

def compute_carry_range(multiplier):
    """Compute the range of possible carry values when multiplying by M.

    At each digit position, product = M * d + carry_in, where d in {0,...,9}.
    carry_out = product // 10.

    The maximum carry grows until it stabilizes. We iterate to find C_max.
    """
    c_max = 0
    for _ in range(100):  # iterate until stable
        new_max = (multiplier * 9 + c_max) // 10
        if new_max == c_max:
            break
        c_max = new_max
    return c_max


def build_transfer_matrix(multiplier, input_digits=range(1, 10)):
    """Build transfer matrix for multiplication by `multiplier` in base 10.

    State = carry value c in {0, 1, ..., c_max}.

    T[c_out, c_in] = number of digits d in input_digits such that:
      (multiplier * d + c_in) mod 10 != 0  (output digit is nonzero)
      floor((multiplier * d + c_in) / 10) = c_out

    Returns T (numpy array) and c_max.
    """
    c_max = compute_carry_range(multiplier)
    n_states = c_max + 1
    T = np.zeros((n_states, n_states), dtype=np.float64)

    for c_in in range(n_states):
        for d in input_digits:
            product = multiplier * d + c_in
            output_digit = product % 10
            c_out = product // 10
            if output_digit != 0 and c_out <= c_max:
                T[c_out, c_in] += 1

    return T, c_max


def build_unrestricted_transfer_matrix(multiplier, input_digits=range(1, 10)):
    """Like build_transfer_matrix but counts ALL transitions (no output restriction).

    T_unr[c_out, c_in] = number of digits d in input_digits such that
      floor((multiplier * d + c_in) / 10) = c_out

    This gives the transfer matrix for counting zeroless inputs WITHOUT
    requiring zeroless outputs. Its spectral radius^m ~ 9^m * rho_m.
    """
    c_max = compute_carry_range(multiplier)
    n_states = c_max + 1
    T = np.zeros((n_states, n_states), dtype=np.float64)

    for c_in in range(n_states):
        for d in input_digits:
            product = multiplier * d + c_in
            c_out = product // 10
            if c_out <= c_max:
                T[c_out, c_in] += 1

    return T, c_max


print("=" * 70)
print("PART A: Carry automaton structure")
print("=" * 70)

for h in [1, 2, 3, 5, 10, 20]:
    M = 2 ** h
    c_max = compute_carry_range(M)
    print(f"  h={h:3d}, M=2^h={M:12d}, carry states: 0..{c_max} ({c_max+1} states)")


# ======================================================================
# PART B: Transfer matrices and spectral radii
# ======================================================================

print("\n" + "=" * 70)
print("PART B: Transfer matrices and spectral radii")
print("=" * 70)

results = {}

for h in range(1, 25):
    M = 2 ** h
    c_max = compute_carry_range(M)

    # Skip if too many states (memory/time)
    if c_max > 2000:
        print(f"  h={h}: M={M}, {c_max+1} carry states -- SKIPPED (too large)")
        continue

    t0 = time.time()

    # Transfer matrix: zeroless input AND zeroless output
    T_both, _ = build_transfer_matrix(M, input_digits=range(1, 10))

    # Transfer matrix: zeroless input only (for comparison)
    T_input, _ = build_unrestricted_transfer_matrix(M, input_digits=range(1, 10))

    # Spectral radii
    eigs_both = np.linalg.eigvals(T_both)
    eigs_input = np.linalg.eigvals(T_input)

    sr_both = np.max(np.abs(eigs_both))
    sr_input = np.max(np.abs(eigs_input))

    # The "independent" prediction: if input and output digits were
    # independent, the overlap measure would be rho_m^2 = (9/10)^{2(m-1)}.
    # The transfer matrix for independent case has spectral radius = 81
    # (9 choices for input * 9 choices for output).
    # Our spectral radius should be <= 81, and strictly < 81 implies QI.

    # Predicted overlap ratio = sr_both / sr_input
    # (The ratio of "both zeroless" to "input zeroless" gives the
    # conditional probability that the output is also zeroless.)

    ratio = sr_both / sr_input if sr_input > 0 else float('nan')

    # The independence prediction: output is zeroless with prob (9/10)^{m-1}
    # independent of input. So overlap = rho_m^2 = (9/10)^{2(m-1)}.
    # The spectral radius ratio sr_both / sr_input should be close to 9/10
    # (one factor of (9/10)^{m-1} comes from sr_input, the other from the
    # conditional probability).

    # Actually: sr_input^m ~ 9^m (number of zeroless m-digit integers up to
    # normalization). sr_both^m ~ overlap count. The ratio sr_both/sr_input
    # should be close to 9/10 if the output digit is independently ~9/10
    # likely to be nonzero.

    elapsed = time.time() - t0

    print(f"  h={h:3d}: sr_both={sr_both:10.4f}, sr_input={sr_input:10.4f}, "
          f"ratio={ratio:.6f}, dim={c_max+1:5d}, {elapsed:.2f}s")

    results[h] = {
        "multiplier": M,
        "carry_states": c_max + 1,
        "spectral_radius_both": float(sr_both),
        "spectral_radius_input": float(sr_input),
        "ratio": float(ratio),
        "top_eigenvalues_both": sorted(np.abs(eigs_both).tolist(), reverse=True)[:5],
        "top_eigenvalues_input": sorted(np.abs(eigs_input).tolist(), reverse=True)[:5],
    }


# ======================================================================
# PART C: Direct overlap computation for small m (validation)
# ======================================================================

print("\n" + "=" * 70)
print("PART C: Direct overlap computation (validation)")
print("=" * 70)

def is_zeroless(x, m):
    """Check if integer x has all m digits nonzero."""
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True


def direct_overlap_count(m, h):
    """Count m-digit zeroless integers n such that 2^h * n also has all
    digits nonzero in its first m significant digits.

    Returns (count_both, count_input, ratio).
    """
    lo = 10 ** (m - 1)
    hi = 10 ** m
    M = 2 ** h

    count_input = 0
    count_both = 0

    for n in range(lo, hi):
        if not is_zeroless(n, m):
            continue
        count_input += 1

        # Compute M * n and check its first m significant digits
        product = M * n
        # Number of digits in product
        d_product = len(str(product))
        # First m significant digits = product // 10^(d_product - m)
        if d_product >= m:
            first_m = product // (10 ** (d_product - m))
        else:
            first_m = product

        if is_zeroless(first_m, m):
            count_both += 1

    ratio = count_both / count_input if count_input > 0 else 0
    return count_both, count_input, ratio


print("\nDirect computation (small m, small h):")
print(f"{'m':>3} {'h':>3} {'count_both':>12} {'count_input':>12} "
      f"{'ratio':>10} {'pred(9/10)^(m-1)':>18}")

direct_results = {}
for m in range(2, 6):  # m=6 has 9^5=59049 zeroless, still fast
    direct_results[m] = {}
    for h in [1, 2, 3, 5, 10]:
        t0 = time.time()
        cb, ci, r = direct_overlap_count(m, h)
        elapsed = time.time() - t0
        pred = 0.9 ** (m - 1)
        print(f"  {m:3d} {h:3d} {cb:12d} {ci:12d} {r:10.6f} {pred:18.6f} "
              f"  ({elapsed:.2f}s)")
        direct_results[m][h] = {
            "count_both": cb,
            "count_input": ci,
            "ratio_direct": r,
            "independence_pred": pred
        }


# ======================================================================
# PART D: Compare transfer matrix predictions to direct computation
# ======================================================================

print("\n" + "=" * 70)
print("PART D: Transfer matrix vs direct comparison")
print("=" * 70)

print("\nTransfer matrix spectral radius predicts overlap count ~ sr_both^m.")
print("Direct count should match sr_both^m (up to boundary effects).\n")

for h in [1, 2, 3, 5, 10]:
    if h not in results:
        continue
    sr = results[h]["spectral_radius_both"]
    sr_inp = results[h]["spectral_radius_input"]

    print(f"h={h}: sr_both={sr:.4f}, sr_input={sr_inp:.4f}")
    for m in range(2, 6):
        if m not in direct_results or h not in direct_results[m]:
            continue
        dd = direct_results[m][h]
        predicted_count = sr ** m  # approximate
        predicted_input = sr_inp ** m
        actual_both = dd["count_both"]
        actual_input = dd["count_input"]

        # The transfer matrix gives asymptotic growth rate.
        # For finite m, boundary effects matter (initial carry = 0).
        # Better comparison: use matrix power with initial state c=0.

        print(f"  m={m}: direct_both={actual_both}, direct_input={actual_input}, "
              f"sr^m={predicted_count:.1f}, sr_inp^m={predicted_input:.1f}")


# ======================================================================
# PART E: Matrix power with initial carry = 0 (exact prediction)
# ======================================================================

print("\n" + "=" * 70)
print("PART E: Exact prediction via matrix power (initial carry = 0)")
print("=" * 70)

for h in [1, 2, 3, 5, 10]:
    if h not in results:
        continue
    M = 2 ** h

    T_both, c_max = build_transfer_matrix(M, input_digits=range(1, 10))
    T_input, _ = build_unrestricted_transfer_matrix(M, input_digits=range(1, 10))

    n_states = c_max + 1

    # Initial state: carry = 0 (we start with the least significant digit)
    v_both = np.zeros(n_states)
    v_both[0] = 1.0
    v_input = np.zeros(n_states)
    v_input[0] = 1.0

    print(f"\nh={h}, M={M}, carry states={n_states}:")
    for m in range(2, 10):
        # Apply transfer matrix m times (m digit positions)
        v_both_m = np.linalg.matrix_power(T_both, m) @ v_both
        v_input_m = np.linalg.matrix_power(T_input, m) @ v_input

        predicted_both = np.sum(v_both_m)
        predicted_input = np.sum(v_input_m)
        ratio_pred = predicted_both / predicted_input if predicted_input > 0 else 0

        # Note: the predicted counts include ALL carry-out values.
        # For the "first m significant digits" interpretation, we need
        # to think about what carry means at the most significant end.
        # The carry at the top represents the extra digits of the product.
        # We don't care about those extra digits being zero or not --
        # we only care about the m digits corresponding to the input.
        # So summing over all final carry states IS correct.

        print(f"  m={m}: pred_both={predicted_both:12.0f}, pred_input={predicted_input:12.0f}, "
              f"ratio={ratio_pred:.6f}")


# ======================================================================
# PART F: Continuous measure overlap via interval computation
# ======================================================================

print("\n" + "=" * 70)
print("PART F: Continuous overlap measure mu(F_m ∩ (F_m - h*theta))")
print("=" * 70)

def enumerate_zeroless_runs(m):
    """Enumerate maximal runs of consecutive zeroless m-digit integers.

    Uses recursive construction: an m-digit zeroless integer has the form
    d * 10^{m-1} + r where d in {1,...,9} and r is an (m-1)-digit zeroless
    integer (with r >= 0, treating (m-1)-digit numbers as potentially
    having leading zeros, except we need all digits nonzero).

    For efficiency, generate digit strings directly.
    """
    if m <= 5:
        # Direct enumeration is fast enough for m <= 5
        lo = 10 ** (m - 1)
        hi = 10 ** m
        run_starts = []
        run_ends = []
        in_run = False
        current_start = 0

        for n in range(lo, hi):
            zl = is_zeroless(n, m)
            if zl and not in_run:
                current_start = n
                in_run = True
            elif not zl and in_run:
                run_starts.append(current_start)
                run_ends.append(n - 1)
                in_run = False

        if in_run:
            run_starts.append(current_start)
            run_ends.append(hi - 1)

        return run_starts, run_ends
    else:
        # For large m, generate runs using the structure:
        # Zeroless m-digit integers: all digits in {1,...,9}
        # A run of consecutive zeroless integers [a, b] means
        # a, a+1, ..., b all have no zero digit.
        #
        # Since m >= 6, there are 9^{m-1} zeroless integers but they're
        # very sparse. Each run has length at most 9 (before hitting a
        # multiple of 10). Actually runs can be longer in the ones digit.
        #
        # Generate all zeroless integers and group into runs.
        # Use itertools.product for digit generation.
        from itertools import product as iprod

        all_zeroless = []
        for digits in iprod(range(1, 10), repeat=m):
            n = 0
            for d in digits:
                n = n * 10 + d
            all_zeroless.append(n)

        all_zeroless.sort()

        run_starts = []
        run_ends = []
        if not all_zeroless:
            return run_starts, run_ends

        current_start = all_zeroless[0]
        prev = all_zeroless[0]

        for n in all_zeroless[1:]:
            if n == prev + 1:
                prev = n
            else:
                run_starts.append(current_start)
                run_ends.append(prev)
                current_start = n
                prev = n

        run_starts.append(current_start)
        run_ends.append(prev)

        return run_starts, run_ends


def continuous_overlap_measure(m, h):
    """Compute mu(F_m ∩ (F_m - h*theta)) using the continuous definition.

    F_m = {alpha in [0,1) : all digits of floor(10^{m-1+alpha}) nonzero}
    F_m - h*theta = {alpha : alpha + h*theta in F_m mod 1}
              = {alpha : all digits of floor(10^{m-1+alpha+h*theta}) nonzero}

    Since 10^{h*theta} = 2^h, this is equivalent to:
    alpha in F_m AND floor(2^h * 10^{m-1+alpha}) has all digits nonzero
    in its first m significant positions.

    We compute this by: for each interval [a_j, b_j) of F_m (in alpha-space),
    compute x = 10^{m-1+alpha}, then 2^h * x, check which sub-intervals
    of [a_j, b_j) also satisfy the shifted condition.

    For small m, we can do this by brute force: enumerate all zeroless runs
    for both F_m and the shifted set, then intersect.
    """
    # F_m intervals in alpha-space
    rs1, re1 = enumerate_zeroless_runs(m)
    alpha_starts_1 = [math.log10(n) - (m - 1) for n in rs1]
    alpha_ends_1 = [math.log10(n + 1) - (m - 1) for n in re1]

    # F_m shifted by h*theta: we need alpha such that alpha + h*theta (mod 1) is in F_m
    # This means alpha is in (F_m - h*theta) mod 1
    # So we shift F_m intervals by -h*theta (mod 1)
    shift = (h * theta) % 1.0
    alpha_starts_2 = [(a - shift) % 1.0 for a in alpha_starts_1]
    alpha_ends_2 = [(b - shift) % 1.0 for b in alpha_ends_1]

    # Handle wrap-around: if start > end, split into [start, 1) and [0, end)
    shifted_intervals = []
    for a, b in zip(alpha_starts_2, alpha_ends_2):
        if a < b:
            shifted_intervals.append((a, b))
        else:
            # Wraps around 0
            shifted_intervals.append((a, 1.0))
            shifted_intervals.append((0.0, b))

    # Original intervals
    orig_intervals = list(zip(alpha_starts_1, alpha_ends_1))

    # Compute intersection measure
    # Sort both lists of intervals, then sweep
    orig_intervals.sort()
    shifted_intervals.sort()

    total_overlap = 0.0
    for a1, b1 in orig_intervals:
        for a2, b2 in shifted_intervals:
            # Intersection of [a1, b1) and [a2, b2)
            lo = max(a1, a2)
            hi = min(b1, b2)
            if hi > lo:
                total_overlap += hi - lo

    return total_overlap


print("\nContinuous overlap measures:")
print(f"{'m':>3} {'h':>3} {'mu(overlap)':>14} {'rho_m^2':>14} {'ratio':>10}")

overlap_results = {}
for m in range(2, 6):  # m <= 5 for tractable interval intersection
    overlap_results[m] = {}
    rho_m = sum(a2 - a1 for a1, a2 in zip(
        [math.log10(n) - (m-1) for n in enumerate_zeroless_runs(m)[0]],
        [math.log10(n+1) - (m-1) for n in enumerate_zeroless_runs(m)[1]]
    ))
    rho_sq = rho_m ** 2

    print(f"\n  m={m}: rho_m={rho_m:.8f}, rho_m^2={rho_sq:.10f}")

    for h in range(0, min(21, int(C_const * m) + 2)):
        t0 = time.time()
        mu_ov = continuous_overlap_measure(m, h)
        elapsed = time.time() - t0
        ratio = mu_ov / rho_sq if rho_sq > 0 else float('nan')

        print(f"  {m:3d} {h:3d} {mu_ov:14.10f} {rho_sq:14.10f} {ratio:10.6f} "
              f"  ({elapsed:.2f}s)")

        overlap_results[m][h] = {
            "mu_overlap": mu_ov,
            "rho_m": rho_m,
            "rho_m_sq": rho_sq,
            "ratio": ratio
        }


# ======================================================================
# PART G: Parseval identity verification
# ======================================================================

print("\n" + "=" * 70)
print("PART G: Parseval identity (★) verification")
print("=" * 70)

print("\nParseval identity:")
print("  int |R_m(x)|^2 dx = L*(rho - rho^2) + 2*sum_{h=1}^{L-1} (L-h)*[mu(overlap) - rho^2]")
print("  Under QI: ||R_m||_2^2 ~ L*rho")

for m in range(2, 6):
    if m not in overlap_results:
        continue

    L_m = math.ceil(m / theta)
    rho_m = overlap_results[m][0]["rho_m"] if 0 in overlap_results[m] else 0.9**(m-1)
    rho_sq = rho_m ** 2

    # Compute the RHS of (★) using the overlap data
    rhs = L_m * (rho_m - rho_sq)
    for h in range(1, L_m):
        if h in overlap_results[m]:
            mu_ov = overlap_results[m][h]["mu_overlap"]
            rhs += 2 * (L_m - h) * (mu_ov - rho_sq)

    # The QI prediction
    qi_pred = L_m * rho_m  # leading term under independence

    # ||R_m||_2 = sqrt(rhs)
    if rhs >= 0:
        norm_R = math.sqrt(rhs)
    else:
        norm_R = -math.sqrt(-rhs)  # negative means anti-correlation

    # For the conjecture, we need |R_m(m*theta)| < 1 - L_m*rho_m.
    # The L2 norm gives average behavior. Chebyshev:
    # P(|R_m| > 1/2) <= 4 * ||R_m||_2^2

    threshold = 1 - L_m * rho_m  # if L_m * rho_m < 1
    chebyshev_bound = 4 * rhs if rhs > 0 else 0

    print(f"\n  m={m}: L_m={L_m}, rho_m={rho_m:.8f}")
    print(f"    RHS of (★) = {rhs:.10f}")
    print(f"    ||R_m||_2 = {norm_R:.8f}")
    print(f"    QI prediction (L*rho) = {qi_pred:.8f}")
    print(f"    sqrt(L*rho) = {math.sqrt(qi_pred):.8f}")
    print(f"    Threshold 1 - L*rho = {threshold:.8f}")
    print(f"    Chebyshev: P(|R_m|>1/2) <= {chebyshev_bound:.8f}")
    print(f"    sum_m Chebyshev ~ sum L_m*rho_m (converges): partial = "
          f"{sum(math.ceil(j/theta) * 0.9**(j-1) for j in range(2, m+1)):.4f}")


# ======================================================================
# PART H: Summary and key ratios
# ======================================================================

print("\n" + "=" * 70)
print("PART H: Summary")
print("=" * 70)

print("\nSpectral radius analysis (from Part B):")
print(f"{'h':>3} {'M=2^h':>12} {'sr_both':>10} {'sr_input':>10} {'ratio':>10} "
      f"{'states':>6}")
for h in sorted(results.keys()):
    r = results[h]
    print(f"  {h:3d} {r['multiplier']:12d} {r['spectral_radius_both']:10.4f} "
          f"{r['spectral_radius_input']:10.4f} {r['ratio']:10.6f} "
          f"{r['carry_states']:6d}")

print("\nOverlap ratio summary (from Part F):")
print("If ratio ~ 1.0, F_m and (F_m - h*theta) are quasi-independent.")
print("If ratio < 1.0, they are negatively correlated (good for proof).")
print("If ratio > 1.0, they are positively correlated (need to bound).")

for m in sorted(overlap_results.keys()):
    if m in overlap_results:
        L_m = math.ceil(m / theta)
        max_ratio = 0
        for h in range(1, L_m):
            if h in overlap_results[m]:
                r = overlap_results[m][h]["ratio"]
                max_ratio = max(max_ratio, r)
        print(f"  m={m}: max ratio over h=1..{L_m-1} is {max_ratio:.6f}")


# Save all results
all_results = {
    "spectral_radii": {str(k): v for k, v in results.items()},
    "direct_counts": {str(m): {str(h): v for h, v in d.items()}
                      for m, d in direct_results.items()},
    "continuous_overlaps": {str(m): {str(h): v for h, v in d.items()}
                           for m, d in overlap_results.items()},
}

with open(os.path.join(DATA_DIR, "exp38_results.json"), "w") as f:
    json.dump(all_results, f, indent=2)

print(f"\nResults saved to {os.path.join(DATA_DIR, 'exp38_results.json')}")
