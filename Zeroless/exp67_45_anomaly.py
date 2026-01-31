"""
Exp 67: The (4,5) Anomaly

From Exp 62: (4,5) has ratio 0.41 - only 41% as frequent as random!
Other killing pairs are 87-98% of random frequency.

Why is (4,5) specifically rare?

The (4,5) pattern requires:
  - Position i-1: d=7 with c=0 → output 4
  - Position i: d ∈ {2,7} with c=1 → output 5
  - c=1 at i requires d_{i-1} ≥ 5, which is satisfied (d_{i-1} = 7)
  - c=0 at i-1 requires d_{i-2} < 5

So (4,5) requires the pattern: (d < 5, 7, {2 or 7}) in three consecutive positions.
"""

from collections import Counter


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def main():
    print("=" * 70)
    print("Exp 67: The (4,5) Anomaly")
    print("=" * 70)

    # Part A: Required three-digit pattern for (4,5)
    print("\n" + "=" * 70)
    print("PART A: Three-Digit Pattern for (4,5)")
    print("=" * 70)

    print("\nFor output (4, 5) at positions (i-1, i):")
    print("  Position i-1: d_{i-1} = 7 with c_{i-1} = 0 → output 4, carry 1")
    print("  Position i: d_i ∈ {2,7} with c_i = 1 → output 5")
    print()
    print("Since c_{i-1} = 0, we need d_{i-2} < 5.")
    print("So the SOURCE pattern in 2^n is: (d_{i-2} < 5, d_{i-1} = 7, d_i ∈ {2,7})")

    # Count this pattern
    pattern_counts = Counter()
    total_triples = 0

    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(2, len(digits)):
            total_triples += 1
            d_minus2 = digits[i-2]
            d_minus1 = digits[i-1]
            d_i = digits[i]

            # Check for (4,5) source pattern
            if d_minus2 < 5 and d_minus1 == 7 and d_i in [2, 7]:
                pattern_counts['45_source'] += 1

            # Also count the general patterns
            pattern_counts[('low', 7, '2or7' if d_i in [2,7] else 'other')] += 1 if d_minus2 < 5 and d_minus1 == 7 else 0

    print(f"\n(4,5) source pattern count: {pattern_counts['45_source']}")
    print(f"Total triples: {total_triples}")
    print(f"Frequency: {pattern_counts['45_source'] / total_triples:.5f}")

    # Part B: Compare all three-digit patterns that produce killing pairs
    print("\n" + "=" * 70)
    print("PART B: Three-Digit Patterns for All Killing Pairs")
    print("=" * 70)

    killing_patterns = {
        '(1,5)': [],  # d_{i-2} ≥ 5, d_{i-1} = 5, d_i ∈ {2,7}
        '(2,5)': [],  # d_{i-2} < 5, d_{i-1} = 6, d_i ∈ {2,7}
        '(3,5)': [],  # d_{i-2} ≥ 5, d_{i-1} = 6, d_i ∈ {2,7}
        '(4,5)': [],  # d_{i-2} < 5, d_{i-1} = 7, d_i ∈ {2,7}
    }

    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(2, len(digits)):
            d_minus2 = digits[i-2]
            d_minus1 = digits[i-1]
            d_i = digits[i]

            if d_i in [2, 7]:  # Required for output 5
                if d_minus1 == 5 and d_minus2 >= 5:  # (1,5) source
                    killing_patterns['(1,5)'].append((n, i, (d_minus2, d_minus1, d_i)))
                elif d_minus1 == 6 and d_minus2 < 5:  # (2,5) source
                    killing_patterns['(2,5)'].append((n, i, (d_minus2, d_minus1, d_i)))
                elif d_minus1 == 6 and d_minus2 >= 5:  # (3,5) source
                    killing_patterns['(3,5)'].append((n, i, (d_minus2, d_minus1, d_i)))
                elif d_minus1 == 7 and d_minus2 < 5:  # (4,5) source
                    killing_patterns['(4,5)'].append((n, i, (d_minus2, d_minus1, d_i)))

    print("\n  Pair | Count | Frequency | Expected (random) | Ratio")
    print("-" * 65)

    for pair, instances in killing_patterns.items():
        count = len(instances)
        freq = count / total_triples
        # Expected under random: P(d_{i-2} condition) × P(d_{i-1}) × P(d_i ∈ {2,7})
        if pair == '(1,5)':
            expected = (5/9) * (1/9) * (2/9)  # d_{i-2} ≥ 5, d_{i-1} = 5, d_i ∈ {2,7}
        elif pair == '(2,5)':
            expected = (4/9) * (1/9) * (2/9)  # d_{i-2} < 5, d_{i-1} = 6
        elif pair == '(3,5)':
            expected = (5/9) * (1/9) * (2/9)  # d_{i-2} ≥ 5, d_{i-1} = 6
        elif pair == '(4,5)':
            expected = (4/9) * (1/9) * (2/9)  # d_{i-2} < 5, d_{i-1} = 7

        ratio = freq / expected if expected > 0 else 0
        print(f"  {pair} | {count:5} | {freq:.5f}   | {expected:.5f}           | {ratio:.2f}")

    # Part C: Check if (low, 7) patterns are rare
    print("\n" + "=" * 70)
    print("PART C: Is (low, 7) Pattern Rare?")
    print("=" * 70)

    low_7_count = 0
    high_7_count = 0

    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            if digits[i] == 7:
                if digits[i-1] < 5:
                    low_7_count += 1
                else:
                    high_7_count += 1

    total_7 = low_7_count + high_7_count
    print(f"\nPatterns ending in 7:")
    print(f"  (low, 7): {low_7_count} ({low_7_count/total_7:.3f})")
    print(f"  (high, 7): {high_7_count} ({high_7_count/total_7:.3f})")
    print(f"  Expected (low): {4/9:.3f}")
    print(f"  Ratio: {(low_7_count/total_7) / (4/9):.2f}")

    # Part D: Check other (low, X) patterns for X ≥ 5
    print("\n" + "=" * 70)
    print("PART D: (low, X) Patterns for X ≥ 5")
    print("=" * 70)

    for X in range(5, 10):
        low_X = 0
        high_X = 0
        for n in range(50, 200):
            digits = get_digits(n)
            for i in range(1, len(digits)):
                if digits[i] == X:
                    if digits[i-1] < 5:
                        low_X += 1
                    else:
                        high_X += 1
        total_X = low_X + high_X
        if total_X > 0:
            ratio = (low_X/total_X) / (4/9)
            print(f"  (low, {X}): {low_X}/{total_X} = {low_X/total_X:.3f}, ratio = {ratio:.2f}")

    # Part E: The key pattern - what precedes 7 in powers of 2?
    print("\n" + "=" * 70)
    print("PART E: What Precedes 7 in Powers of 2?")
    print("=" * 70)

    precedes_7 = Counter()
    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            if digits[i] == 7:
                precedes_7[digits[i-1]] += 1

    total = sum(precedes_7.values())
    print("\n  Digit | Count | Frequency | Expected | Ratio")
    print("-" * 55)
    for d in range(1, 10):
        count = precedes_7[d]
        freq = count / total
        expected = 1/9
        ratio = freq / expected
        marker = " ** LOW **" if d < 5 and ratio < 0.9 else ""
        marker = " ** HIGH **" if d >= 5 and ratio > 1.1 else marker
        print(f"  {d}     | {count:5} | {freq:.4f}    | {expected:.4f}   | {ratio:.2f}{marker}")

    low_total = sum(precedes_7[d] for d in range(1, 5))
    high_total = sum(precedes_7[d] for d in range(5, 10))
    print(f"\n  Sum(1-4): {low_total} ({low_total/total:.3f}), expected: {4/9:.3f}")
    print(f"  Sum(5-9): {high_total} ({high_total/total:.3f}), expected: {5/9:.3f}")
    print(f"  Ratio low: {(low_total/total) / (4/9):.2f}")

    # Part F: The answer!
    print("\n" + "=" * 70)
    print("PART F: THE ANSWER")
    print("=" * 70)

    print("\nWhy is (4,5) rare?")
    print()
    print("The (4,5) killing pair requires d_{i-2} < 5 AND d_{i-1} = 7.")
    print()
    print("From Part E, digits preceding 7 have this distribution:")
    low_ratio = (low_total/total) / (4/9)
    print(f"  - Low digits (1-4) precede 7 with ratio {low_ratio:.2f} vs random")
    print()
    if low_ratio < 0.9:
        print("*** LOW DIGITS RARELY PRECEDE 7 IN POWERS OF 2 ***")
        print()
        print("This explains the (4,5) anomaly!")
        print("Since low digits rarely precede 7, the pattern (low, 7, {2,7}) is rare,")
        print("which makes (4,5) killing pairs rare.")


if __name__ == "__main__":
    main()
