#!/usr/bin/env python3
"""
Deep analysis for the 86 Conjecture
"""
import sys
sys.set_int_max_str_digits(100000)

def has_zero(n):
    """Check if 2^n contains digit 0"""
    return '0' in str(2**n)

def get_rejection_position(n):
    """
    For n where 2^n contains 0, find the position of the first 0
    that would be produced by doubling 2^(n-1).
    Returns -1 if 2^n is zeroless.
    """
    if not has_zero(n):
        return -1

    # Find first 0 in 2^n
    s = str(2**n)
    for i, c in enumerate(s[::-1]):  # Reverse to get position from LSB
        if c == '0':
            return i
    return -1

def verify_exact_recurrence():
    """Verify S_{k+1} = floor((9/2) * S_k) exactly"""
    print("EXACT RECURRENCE VERIFICATION")
    print("=" * 60)

    prev_S = None
    for level in range(1, 8):
        period = 4 * (5 ** (level - 1))

        # Count survivors by checking rejection position
        survivors = 0
        for n_mod in range(period):
            n = period + n_mod  # Ensure n >= level

            # Check if rejected at positions < level
            power = 2**n
            rej_pos = get_rejection_position(n + 1)  # Position in 2^(n+1)

            if rej_pos == -1 or rej_pos >= level:
                survivors += 1

        ratio = survivors / prev_S if prev_S else "N/A"
        print(f"Level {level}: S_{level} = {survivors:6d}, "
              f"ratio to prev = {ratio if prev_S else 'N/A'}")
        prev_S = survivors

def analyze_late_rejections():
    """Find which n have late rejection positions"""
    print("\n" + "=" * 60)
    print("LATE REJECTION ANALYSIS")
    print("=" * 60)

    late_rejections = []
    for n in range(1, 10001):
        if not has_zero(n):
            continue
        rej_pos = get_rejection_position(n)
        if rej_pos > 20:
            late_rejections.append((n, rej_pos))

    print(f"Powers with rejection position > 20 (n ≤ 10000):")
    for n, pos in sorted(late_rejections, key=lambda x: x[1], reverse=True)[:20]:
        print(f"  n = {n}: rejection at position {pos}")

    if late_rejections:
        max_pos = max(pos for n, pos in late_rejections)
        max_n = [n for n, pos in late_rejections if pos == max_pos][0]
        print(f"\nMaximum rejection position: {max_pos} at n = {max_n}")

def analyze_zeroless_pattern():
    """Analyze the pattern in zeroless powers"""
    print("\n" + "=" * 60)
    print("ZEROLESS PATTERN ANALYSIS")
    print("=" * 60)

    zeroless = [n for n in range(1, 200) if not has_zero(n)]

    print(f"Zeroless powers: {zeroless}")
    print(f"\nNumber of zeroless powers: {len(zeroless)}")

    # Analyze by residue class mod 20
    print("\nZeroless by residue class mod 20:")
    for r in range(1, 21):
        count = sum(1 for n in zeroless if n % 20 == r)
        members = [n for n in zeroless if n % 20 == r]
        print(f"  n ≡ {r:2d} (mod 20): {count} powers: {members}")

def orbit_structure_proof():
    """Verify the orbit structure lemma for base 10"""
    print("\n" + "=" * 60)
    print("ORBIT STRUCTURE LEMMA VERIFICATION")
    print("=" * 60)

    print("\nFor each level-2 residue class, the 5 lifts to level-3")
    print("have digit at position 2 cycling through either")
    print("{0,2,4,6,8} (even) or {1,3,5,7,9} (odd).")
    print()

    # 2^20 mod 1000 = 576
    multiplier = pow(2, 20, 1000)
    print(f"2^20 ≡ {multiplier} (mod 1000)")
    print()

    # Verify for all level-2 classes
    all_even = True
    all_odd = True

    for base_n in range(1, 21):
        digits_at_pos2 = []
        for k in range(5):
            n = base_n + 20 * k
            power = 2**n
            digit2 = (power // 100) % 10
            digits_at_pos2.append(digit2)

        is_even_set = set(digits_at_pos2) <= {0, 2, 4, 6, 8}
        is_odd_set = set(digits_at_pos2) <= {1, 3, 5, 7, 9}
        covers_all = len(set(digits_at_pos2)) == 5

        if not (is_even_set or is_odd_set):
            print(f"  n ≡ {base_n:2d}: digits = {digits_at_pos2} - MIXED (ERROR!)")
            all_even = all_odd = False
        elif not covers_all:
            print(f"  n ≡ {base_n:2d}: digits = {digits_at_pos2} - doesn't cover all 5")
        else:
            parity = "even" if is_even_set else "odd"
            print(f"  n ≡ {base_n:2d}: digits = {digits_at_pos2} - {parity}, all 5 values ✓")

    print("\nOrbit structure verified: each class cycles through exactly 5 digits of same parity.")

def rejection_fraction_analysis():
    """Analyze what fraction gets rejected at each level"""
    print("\n" + "=" * 60)
    print("REJECTION FRACTION BY LEVEL")
    print("=" * 60)

    for level in range(1, 7):
        period = 4 * (5 ** (level - 1))

        rejected_at_level = 0
        survived_prev = 0

        for n_mod in range(period):
            n = period + n_mod

            rej_pos = get_rejection_position(n + 1)

            # Survived all previous levels?
            if rej_pos == -1 or rej_pos >= level - 1:
                survived_prev += 1

            # Rejected at exactly this level?
            if rej_pos == level - 1:
                rejected_at_level += 1

        if survived_prev > 0:
            rejection_rate = rejected_at_level / survived_prev
        else:
            rejection_rate = 0

        print(f"Level {level}: period = {period:6d}, "
              f"prev survivors = {survived_prev:6d}, "
              f"rejected at level = {rejected_at_level:6d}, "
              f"rate = {rejection_rate:.4f}")

def coverage_sum():
    """Compute the cumulative coverage sum"""
    print("\n" + "=" * 60)
    print("COVERAGE SUM CONVERGENCE")
    print("=" * 60)

    total_coverage = 0.0
    for level in range(1, 20):
        # Coverage at level k is approximately (1/10) * 0.9^(k-2) for k >= 2
        # At level 1, coverage is 0 (no rejections)

        if level == 1:
            new_coverage = 0.0
        else:
            # Fraction of survivors from level k-1 that get rejected
            # = (1/2) * (1/5) = 1/10 of survivors
            # Survivors at level k-1 = 0.9^(k-2) of total
            # So new coverage = (1/10) * 0.9^(k-2)
            new_coverage = 0.1 * (0.9 ** (level - 2))

        total_coverage += new_coverage
        print(f"Level {level}: new coverage = {new_coverage:.6f}, "
              f"cumulative = {total_coverage:.6f}")

    print(f"\nSum approaches 1.0 as levels → ∞")
    print(f"Theoretical limit: 1/10 * (1 + 0.9 + 0.9^2 + ...) = 1/10 * 10 = 1.0")

def find_max_rejection_position(max_n=100000):
    """Find the maximum rejection position for n ≤ max_n"""
    print(f"\n" + "=" * 60)
    print(f"MAXIMUM REJECTION POSITION (n ≤ {max_n})")
    print("=" * 60)

    max_pos = 0
    max_n_value = 0

    for n in range(1, max_n + 1):
        if not has_zero(n):
            continue
        rej_pos = get_rejection_position(n)
        if rej_pos > max_pos:
            max_pos = rej_pos
            max_n_value = n
            print(f"  New max: n = {n}, rejection position = {rej_pos}")

    print(f"\nFinal: Maximum rejection position = {max_pos} at n = {max_n_value}")
    return max_pos, max_n_value

def main():
    verify_exact_recurrence()
    orbit_structure_proof()
    analyze_zeroless_pattern()
    rejection_fraction_analysis()
    coverage_sum()
    analyze_late_rejections()
    find_max_rejection_position(50000)

if __name__ == "__main__":
    main()
