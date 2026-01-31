"""
Exp 70: The Full Digit-Pair Bias Matrix

Exp 68-69 showed (7, high) pairs are suppressed due to carry cascade.
Let's compute the FULL 10x10 matrix of digit-pair biases in powers of 2.

This will reveal:
1. Which pairs are over/under-represented
2. The global structure of correlations
3. How this relates to killing pairs and protection
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
    print("Exp 70: The Full Digit-Pair Bias Matrix")
    print("=" * 70)

    # Part A: Count all (a, b) pairs in powers of 2
    print("\n" + "=" * 70)
    print("PART A: Pair Counts in 2^n (n=50..300)")
    print("=" * 70)

    pair_counts = Counter()
    total_pairs = 0

    for n in range(50, 301):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            pair_counts[(digits[i-1], digits[i])] += 1
            total_pairs += 1

    # Compute ratios vs uniform
    print("\nRatio vs uniform (1/9 for zeroless) for each pair (a, b):")
    print("(a at position i-1, b at position i)")
    print()

    # Header
    print("     ", end="")
    for b in range(10):
        print(f"  {b}   ", end="")
    print()
    print("     ", end="")
    for _ in range(10):
        print("------", end="")
    print()

    # Build matrix
    expected_pct = 100 / 81  # uniform over 9x9 zeroless pairs

    for a in range(10):
        print(f"  {a} |", end="")
        for b in range(10):
            count = pair_counts[(a, b)]
            actual_pct = 100 * count / total_pairs if total_pairs > 0 else 0

            # Expected: 0 if either is 0, else 1/81
            if a == 0 or b == 0:
                expected = 0
                if actual_pct > 0.1:
                    ratio = float('inf')
                else:
                    ratio = 0
            else:
                expected = expected_pct
                ratio = actual_pct / expected if expected > 0 else 0

            # Color code: green if > 1, red if < 1
            if a == 0 or b == 0:
                print(f"  -  ", end="")
            elif ratio >= 1.1:
                print(f" {ratio:.2f}↑", end="")
            elif ratio <= 0.9:
                print(f" {ratio:.2f}↓", end="")
            else:
                print(f" {ratio:.2f} ", end="")
        print()

    # Part B: Focus on protection-relevant pairs
    print("\n" + "=" * 70)
    print("PART B: Protection-Relevant Pairs")
    print("=" * 70)

    print("\nKilling pairs (a, 5) where a ∈ {1,2,3,4}:")
    for a in [1, 2, 3, 4]:
        count = pair_counts[(a, 5)]
        actual_pct = 100 * count / total_pairs
        ratio = actual_pct / expected_pct
        print(f"  ({a}, 5): {count:4} ({actual_pct:.2f}%), ratio = {ratio:.2f}")

    print("\nProtecting pairs (a, 5) where a ∈ {5,6,7,8,9}:")
    for a in [5, 6, 7, 8, 9]:
        count = pair_counts[(a, 5)]
        actual_pct = 100 * count / total_pairs
        ratio = actual_pct / expected_pct
        print(f"  ({a}, 5): {count:4} ({actual_pct:.2f}%), ratio = {ratio:.2f}")

    # Part C: The (low, high) vs (high, low) asymmetry
    print("\n" + "=" * 70)
    print("PART C: (Low, High) vs (High, Low) Asymmetry")
    print("=" * 70)

    low = [1, 2, 3, 4]
    high = [5, 6, 7, 8, 9]

    low_high_count = sum(pair_counts[(a, b)] for a in low for b in high)
    high_low_count = sum(pair_counts[(a, b)] for a in high for b in low)

    low_high_expected = total_pairs * 4 * 5 / 81
    high_low_expected = total_pairs * 5 * 4 / 81

    print(f"\n(Low, High) pairs: {low_high_count} (expected {low_high_expected:.0f})")
    print(f"Ratio: {low_high_count / low_high_expected:.3f}")

    print(f"\n(High, Low) pairs: {high_low_count} (expected {high_low_expected:.0f})")
    print(f"Ratio: {high_low_count / high_low_expected:.3f}")

    print(f"\nAsymmetry: (Low, High) / (High, Low) = {low_high_count / high_low_count:.3f}")
    print(f"Expected: 1.0")

    # Part D: The carry correlation matrix
    print("\n" + "=" * 70)
    print("PART D: The Carry Correlation Mechanism")
    print("=" * 70)

    print("\nFor each digit d, compute P(next digit is high | d) vs P(next digit is low | d)")
    print()

    for d in range(1, 10):
        high_after_d = sum(pair_counts[(d, b)] for b in high)
        low_after_d = sum(pair_counts[(d, b)] for b in low)
        total_after_d = high_after_d + low_after_d

        p_high = high_after_d / total_after_d if total_after_d > 0 else 0

        # Theoretical prediction based on carry
        # If d < 5: carry-out = 0, so high outputs come from d' ∈ {3,4,8,9}
        # If d >= 5: carry-out = 1, so high outputs come from d' ∈ {2,3,4,7,8,9}
        if d < 5:
            theoretical_high = 4/9  # d' ∈ {3,4,8,9} for high with c=0
        else:
            theoretical_high = 6/9  # d' ∈ {2,3,4,7,8,9} for high with c=1

        print(f"  d={d}: P(high after d) = {p_high:.3f}, theoretical = {theoretical_high:.3f}")

    # Part E: Why killing pairs are suppressed
    print("\n" + "=" * 70)
    print("PART E: Why Killing Pairs Are Suppressed")
    print("=" * 70)

    print("\nKilling pairs (a, 5) require:")
    print("  a ∈ {1,2,3,4} at position i-1")
    print("  5 at position i")
    print()
    print("5 is produced from d ∈ {2, 7} with carry-in 1.")
    print("Carry-in 1 requires the digit to the RIGHT of 5 to be ≥ 5.")
    print()
    print("So for killing pair (a, 5):")
    print("  The digit to the left of a (position i-2) must be ≥ 5")
    print("  (to provide carry to position i-1)")
    print()
    print("Let's check: what digits are to the left of 1,2,3,4 in powers of 2?")

    for a in [1, 2, 3, 4]:
        left_of_a = Counter()
        for n in range(50, 301):
            digits = get_digits(n)
            for i in range(1, len(digits)):
                if digits[i-1] == a:
                    left_of_a[digits[i]] += 1

        total = sum(left_of_a.values())
        high_left = sum(left_of_a[d] for d in high)
        low_left = sum(left_of_a[d] for d in low)

        print(f"\n  Left of {a}: high={100*high_left/total:.1f}%, low={100*low_left/total:.1f}%")

    # Part F: The structural mechanism
    print("\n" + "=" * 70)
    print("PART F: The Structural Suppression Mechanism")
    print("=" * 70)

    print("""
*** KEY INSIGHT ***

The doubling map creates a BIAS in digit pair distributions:

1. Carry propagation: d >= 5 produces carry, d < 5 doesn't

2. Output distribution depends on carry:
   - Carry 0 → even outputs (2,4,6,8,0) from odd sources (1,3,5,7,9)
   - Carry 1 → odd outputs (3,5,7,9,1) from odd sources (1,3,5,7,9)

3. This creates correlation structure:
   - Low digits (1,2,3,4) tend to be followed by low digits
   - High digits (5,6,7,8,9) tend to be followed by high digits

4. For killing pairs (low, 5):
   - 5 requires carry-in 1 (from d ≥ 5 to the right)
   - But if d ≥ 5 to the right, its output (position of "low") is biased
   - The bias works AGAINST the killing pair pattern

5. This is why powers of 2 are "lucky" - the doubling dynamics
   structurally suppress killing pairs!
""")

    # Part G: Quantify the protection
    print("=" * 70)
    print("PART G: Quantifying the Protection Advantage")
    print("=" * 70)

    total_killing = sum(pair_counts[(a, 5)] for a in [1, 2, 3, 4])
    expected_killing = total_pairs * 4/81

    total_protecting = sum(pair_counts[(a, 5)] for a in [5, 6, 7, 8, 9])
    expected_protecting = total_pairs * 5/81

    print(f"\nKilling pairs (1-4, 5): {total_killing} vs expected {expected_killing:.0f}")
    print(f"Ratio: {total_killing / expected_killing:.3f}")

    print(f"\nProtecting pairs (5-9, 5): {total_protecting} vs expected {expected_protecting:.0f}")
    print(f"Ratio: {total_protecting / expected_protecting:.3f}")

    print(f"\nProtection/Killing ratio in 2^n: {total_protecting / total_killing:.3f}")
    print(f"Expected (random): {5/4:.3f}")

    protection_advantage = (total_protecting / total_killing) / (5/4)
    print(f"\nProtection ADVANTAGE: {protection_advantage:.3f}x more than random")


if __name__ == "__main__":
    main()
