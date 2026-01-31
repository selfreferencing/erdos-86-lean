"""
Exp 63: Trajectory Dynamics - Why Earlier Termination?

Exp 62 showed killing pairs are UNDER-represented in 2^n (ratio 0.80).
So why does the orbit terminate at 86 instead of 250?

Key insight: The random model assumes independent samples at each length.
But 2^n is a deterministic trajectory where D_{n+1} = Doubling(D_n).

This experiment investigates:
1. The TRAJECTORY of protection status, not just single-point statistics
2. Whether the doubling dynamics create correlated failures
3. The "self-destruction" hypothesis: once unprotected 5s appear frequently,
   they keep appearing
"""

import random


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def double_digits(digits):
    """Double a digit string, return new digits (LSB first)."""
    result = []
    carry = 0
    for d in digits:
        val = 2 * d + carry
        result.append(val % 10)
        carry = val // 10
    if carry > 0:
        result.append(carry)
    return result


def count_unprotected_5s(digits):
    """Count unprotected 5s."""
    count = 0
    if digits[0] == 5:
        count += 1
    for i in range(1, len(digits)):
        if digits[i] == 5 and digits[i-1] in [1, 2, 3, 4]:
            count += 1
    return count


def is_zeroless(digits):
    """Check if zeroless."""
    return 0 not in digits


def count_new_5s_created(digits):
    """Count how many new 5s are created when doubling.
    A 5 is created when 2*d + c ≡ 5 (mod 10), i.e., d ∈ {2,7} with c=1."""
    carry = 0
    new_5s = 0
    for d in digits:
        val = 2 * d + carry
        if val % 10 == 5:
            new_5s += 1
        carry = val // 10
    return new_5s


def main():
    print("=" * 70)
    print("Exp 63: Trajectory Dynamics - Why Earlier Termination?")
    print("=" * 70)

    # Part A: Track trajectory of unprotected 5s
    print("\n" + "=" * 70)
    print("PART A: Trajectory of Unprotected 5s Through Doublings")
    print("=" * 70)

    print("\n  n | digits | #5s | unprot5 | zeroless | new_5s_created")
    print("-" * 65)

    for n in range(0, 101):
        digits = get_digits(n)
        m = len(digits)
        num_5s = sum(1 for d in digits if d == 5)
        unprot = count_unprotected_5s(digits)
        zl = is_zeroless(digits)
        new_5s = count_new_5s_created(digits)

        marker = ""
        if zl:
            marker = " *** ZEROLESS"
        elif unprot > 0 and n > 0:
            prev_digits = get_digits(n-1)
            if is_zeroless(prev_digits):
                marker = " <- terminated from zeroless"

        if n <= 15 or n >= 80 or (zl and n >= 30):
            print(f" {n:3} | {m:6} | {num_5s:3} | {unprot:7} | {str(zl):8} | {new_5s:14}{marker}")

    # Part B: The "5 regeneration" mechanism
    print("\n" + "=" * 70)
    print("PART B: How 5s Are Created (The 2/7 → 5 Rule)")
    print("=" * 70)

    print("\nNew 5s are created from digits 2 or 7 with carry-in 1:")
    print("  2*2 + 1 = 5 (from 2 with carry)")
    print("  2*7 + 1 = 15, output 5 (from 7 with carry)")

    print("\nFor zeroless powers, track source digits of 5s in next power:")

    zeroless_n = [n for n in range(101) if is_zeroless(get_digits(n))]

    for n in zeroless_n[-10:]:  # Last 10 zeroless
        digits = get_digits(n)
        next_digits = get_digits(n+1)

        # Find positions of 5s in next power
        five_positions_next = [i for i, d in enumerate(next_digits) if d == 5]

        # Trace back to source
        sources = []
        carry = 0
        for i, d in enumerate(digits):
            val = 2 * d + carry
            if val % 10 == 5:
                sources.append((i, d, carry))
            carry = val // 10

        print(f"\n  n={n}: 2^{n} → 2^{n+1}")
        print(f"    5s in 2^{n+1} at positions: {five_positions_next}")
        print(f"    Sources: {sources}  (pos, digit, carry)")

    # Part C: The correlation question
    print("\n" + "=" * 70)
    print("PART C: Correlation Between Consecutive Powers")
    print("=" * 70)

    print("\nIf 2^n has k unprotected 5s, what's E[unprotected 5s in 2^{n+1}]?")

    # Group by unprotected 5 count in 2^n
    from collections import defaultdict
    unprot_transitions = defaultdict(list)

    for n in range(1, 200):
        digits_n = get_digits(n)
        digits_n1 = get_digits(n+1)

        unprot_n = count_unprotected_5s(digits_n)
        unprot_n1 = count_unprotected_5s(digits_n1)

        unprot_transitions[unprot_n].append(unprot_n1)

    print("\n  unprot(n) | E[unprot(n+1)] | Count")
    print("-" * 45)
    for k in sorted(unprot_transitions.keys()):
        if k <= 5:
            vals = unprot_transitions[k]
            avg = sum(vals) / len(vals)
            print(f"  {k:9} | {avg:14.2f} | {len(vals)}")

    # Part D: The key question - conditional probability
    print("\n" + "=" * 70)
    print("PART D: P(zeroless | previous was zeroless)")
    print("=" * 70)

    print("\nTrack: given 2^n is zeroless, what's P(2^{n+1} is zeroless)?")

    n_ranges = [(0, 20), (20, 40), (40, 60), (60, 80), (80, 100)]

    for start, end in n_ranges:
        zeroless_count = 0
        transition_count = 0
        for n in range(start, end):
            if is_zeroless(get_digits(n)):
                zeroless_count += 1
                if is_zeroless(get_digits(n+1)):
                    transition_count += 1

        if zeroless_count > 0:
            prob = transition_count / zeroless_count
            print(f"  n ∈ [{start:2}, {end:2}): {transition_count}/{zeroless_count} = {prob:.2f}")

    # Part E: Simulated random walk comparison
    print("\n" + "=" * 70)
    print("PART E: Simulated Random Walk (Random Zeroless Starting Point)")
    print("=" * 70)

    print("\nSimulate: start with random zeroless string, apply doubling.")
    print("Count how many consecutive zeroless steps.")

    random.seed(42)

    def random_zeroless(length):
        return [random.randint(1, 9) for _ in range(length)]

    def simulate_run(start_length):
        """Simulate doubling from a random zeroless start until zero appears."""
        digits = random_zeroless(start_length)
        steps = 0
        while is_zeroless(digits) and steps < 1000:
            digits = double_digits(digits)
            if is_zeroless(digits):
                steps += 1
            else:
                break
        return steps

    print("\n  Start length | Avg run length | Max run | Trials")
    print("-" * 55)

    for start_len in [10, 15, 20, 25, 30]:
        runs = [simulate_run(start_len) for _ in range(1000)]
        avg_run = sum(runs) / len(runs)
        max_run = max(runs)
        print(f"  {start_len:12} | {avg_run:14.2f} | {max_run:7} | 1000")

    # Part F: The critical insight
    print("\n" + "=" * 70)
    print("PART F: Critical Insight - Digit Position Matters")
    print("=" * 70)

    print("\nIn powers of 2, where are 5s located?")
    print("Position as fraction of total digits:\n")

    five_positions_by_range = {
        'early': [],  # n < 30
        'middle': [],  # 30 <= n < 60
        'late': [],  # n >= 60
    }

    for n in range(150):
        digits = get_digits(n)
        m = len(digits)
        for i, d in enumerate(digits):
            if d == 5:
                frac = i / m
                if n < 30:
                    five_positions_by_range['early'].append(frac)
                elif n < 60:
                    five_positions_by_range['middle'].append(frac)
                else:
                    five_positions_by_range['late'].append(frac)

    for label, fracs in five_positions_by_range.items():
        if fracs:
            avg = sum(fracs) / len(fracs)
            print(f"  {label:8}: avg position = {avg:.2f} (0 = LSB, 1 = MSB), count = {len(fracs)}")

    # Part G: Why 86 specifically?
    print("\n" + "=" * 70)
    print("PART G: What's Special About n=86?")
    print("=" * 70)

    for n in range(80, 90):
        digits = get_digits(n)
        m = len(digits)
        zl = is_zeroless(digits)
        unprot = count_unprotected_5s(digits)
        num_5s = sum(1 for d in digits if d == 5)

        # Count "dangerous" patterns: 5 preceded by 1,2,3,4
        dangerous = []
        for i in range(1, len(digits)):
            if digits[i] == 5 and digits[i-1] in [1, 2, 3, 4]:
                dangerous.append((i, digits[i-1]))

        status = "ZEROLESS" if zl else "has zero"
        print(f"  n={n}: {m} digits, {num_5s} 5s, {unprot} unprot, {status}")
        if dangerous:
            print(f"         dangerous patterns: {dangerous}")


if __name__ == "__main__":
    main()
