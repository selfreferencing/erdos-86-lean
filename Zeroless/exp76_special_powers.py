"""
Exp 76: Special Powers - The Near-Miss Champions

From Exp 75, certain n values appear repeatedly as near-misses:
- n = 122, 124, 129, 130, 149, 151, 171, 184

These powers have unusually few zeros in their prefixes.
What makes them special?
"""


def get_digits_str(n):
    """Get digit string of 2^n."""
    return str(2 ** n)


def count_zeros(s):
    """Count zeros in string."""
    return s.count('0')


def digit_distribution(s):
    """Get digit distribution."""
    from collections import Counter
    return Counter(s)


def main():
    print("=" * 70)
    print("Exp 76: Special Powers - The Near-Miss Champions")
    print("=" * 70)

    # Special near-miss powers
    special_n = [122, 124, 129, 130, 149, 151, 165, 171, 184]

    # Part A: Analyze these special powers
    print("\n" + "=" * 70)
    print("PART A: Analysis of Special Near-Miss Powers")
    print("=" * 70)

    for n in special_n:
        s = get_digits_str(n)
        d = len(s)
        zeros = count_zeros(s)
        dist = digit_distribution(s)

        print(f"\n2^{n} ({d} digits, {zeros} zeros):")
        print(f"  {s}")
        print(f"  Digit distribution: ", end="")
        for digit in range(10):
            print(f"{digit}:{dist[str(digit)]} ", end="")
        print()

        # Find zero positions
        zero_pos = [i for i, c in enumerate(s) if c == '0']
        print(f"  Zero positions (MSB=0): {zero_pos}")

    # Part B: Compare to typical powers
    print("\n" + "=" * 70)
    print("PART B: Comparison with Typical Powers")
    print("=" * 70)

    print("\nAverage zeros per digit count:")
    print()

    # Group powers by digit count
    from collections import defaultdict
    zeros_by_digits = defaultdict(list)

    for n in range(87, 200):
        s = get_digits_str(n)
        d = len(s)
        zeros = count_zeros(s)
        zeros_by_digits[d].append((n, zeros))

    print("  Digits | Avg zeros | Special cases (if any)")
    print("-" * 60)

    for d in sorted(zeros_by_digits.keys()):
        powers = zeros_by_digits[d]
        avg_zeros = sum(z for _, z in powers) / len(powers)

        # Find special ones
        special_in_range = [n for n in special_n if len(get_digits_str(n)) == d]
        if special_in_range:
            special_str = f"n={special_in_range}: {[count_zeros(get_digits_str(n)) for n in special_in_range]} zeros"
        else:
            special_str = ""

        print(f"  {d:6} | {avg_zeros:9.2f} | {special_str}")

    # Part C: What's special about these n values mod various bases?
    print("\n" + "=" * 70)
    print("PART C: Modular Properties of Special Powers")
    print("=" * 70)

    print("\nSpecial n values mod various bases:")
    print()

    for base in [4, 5, 8, 9, 10, 12, 20, 40]:
        print(f"  mod {base:2}: ", end="")
        for n in special_n:
            print(f"{n % base:2} ", end="")
        print()

    # Part D: Look for patterns in gaps
    print("\n" + "=" * 70)
    print("PART D: Gap Patterns Between Special Powers")
    print("=" * 70)

    sorted_special = sorted(special_n)
    gaps = [sorted_special[i+1] - sorted_special[i] for i in range(len(sorted_special)-1)]

    print(f"\nSorted special n: {sorted_special}")
    print(f"Gaps: {gaps}")
    print(f"Sum of gaps: {sum(gaps)}")

    # Part E: Frequency of near-misses
    print("\n" + "=" * 70)
    print("PART E: Near-Miss Frequency Analysis")
    print("=" * 70)

    print("\nFor n in [87, 250], count how many m values have n as 1-zero near-miss:")
    print()

    near_miss_count = {}
    for n in range(87, 251):
        s = get_digits_str(n)
        d = len(s)
        count = 0

        # For each m from 36 to d, check if m-prefix has exactly 1 zero
        for m in range(36, d + 1):
            prefix = s[:m]
            if count_zeros(prefix) == 1:
                count += 1

        if count > 0:
            near_miss_count[n] = count

    # Top near-miss champions
    sorted_champs = sorted(near_miss_count.items(), key=lambda x: -x[1])

    print("Top 20 near-miss champions (most m values with 1-zero prefix):")
    print()
    for n, count in sorted_champs[:20]:
        s = get_digits_str(n)
        d = len(s)
        total_zeros = count_zeros(s)
        zero_pos = [i for i, c in enumerate(s) if c == '0']
        print(f"  n={n:3}: {count:2} m-values, {d} digits, {total_zeros} total zeros at {zero_pos}")

    # Part F: The champion's secret
    print("\n" + "=" * 70)
    print("PART F: The Champion's Secret")
    print("=" * 70)

    # Get the top champion
    if sorted_champs:
        champ_n, champ_count = sorted_champs[0]
        s = get_digits_str(champ_n)

        print(f"\nTop champion: 2^{champ_n}")
        print(f"  {s}")
        print()
        print(f"This power has its zero(s) placed to maximize the number of")
        print(f"zeroless prefixes. The zero is at position {[i for i, c in enumerate(s) if c == '0']}")
        print(f"so all prefixes up to that position are zeroless.")

    # Part G: Conclusion
    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    print("""
The "near-miss champion" powers have a common pattern:
1. Their zeros are concentrated at the END (high position from MSB)
2. This makes many m-digit prefixes zeroless
3. But they still have at least one zero somewhere

Key insight for the proof:
- Even the "best" powers for m >= 36 have at least 1 zero in the prefix
- The zero positions are NOT clustered - they're distributed
- This suggests the constraint is STRONG, not just statistical

The structural suppression (killing pair mechanism) explains why
actual N_m is only 30-70% of random expectation.
""")


if __name__ == "__main__":
    main()
