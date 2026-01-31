"""
Exp 62: Why Does the Orbit Terminate at 86 Instead of 250?

The random model predicts N₀ ≈ 250-260, but the actual cutoff is 86.
This 3× discrepancy suggests the orbit 2^n has non-random structure.

Key questions:
1. How does actual protection rate compare to random prediction?
2. Is the "5X" pattern (X ∈ {1,2,3,4}) over-represented in powers of 2?
3. What digit correlations exist in 2^n that don't exist in random strings?
"""

from collections import Counter
import random


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def count_unprotected_5s(digits):
    """Count unprotected 5s in a digit string (LSB first)."""
    count = 0
    # LSB = 5 is unprotected
    if digits[0] == 5:
        count += 1
    # 5 preceded by low digit is unprotected
    for i in range(1, len(digits)):
        if digits[i] == 5 and digits[i-1] in [1, 2, 3, 4]:
            count += 1
    return count


def count_adjacent_pairs(digits):
    """Count all adjacent digit pairs (d_{i-1}, d_i) for i >= 1."""
    pairs = Counter()
    for i in range(1, len(digits)):
        pairs[(digits[i-1], digits[i])] += 1
    return pairs


def is_zeroless(digits):
    """Check if digit string is zeroless."""
    return 0 not in digits


def random_zeroless_string(length):
    """Generate a random zeroless digit string."""
    return [random.randint(1, 9) for _ in range(length)]


def main():
    print("=" * 70)
    print("Exp 62: Why Does the Orbit Terminate at 86 Instead of 250?")
    print("=" * 70)

    # Part A: Protection rate comparison
    print("\n" + "=" * 70)
    print("PART A: Protection Rate - Actual 2^n vs Random Model")
    print("=" * 70)

    print("\nFor each n, compare actual unprotected 5 count to random expectation.")
    print("\n  n | digits | #5s | unprot5 (actual) | unprot5 (random E) | ratio")
    print("-" * 75)

    # Random model: P(5 at pos i is unprotected) = P(d_{i-1} < 5) = 4/9
    # E[unprotected 5s] = (#5s) * (4/9) + indicator(LSB=5)

    ratios = []
    for n in range(10, 201, 10):
        digits = get_digits(n)
        m = len(digits)
        num_5s = digits.count(5)
        actual_unprot = count_unprotected_5s(digits)

        # Random expectation: each 5 (except LSB) has 4/9 chance of being unprotected
        # LSB=5 is always unprotected
        # But we condition on the actual 5 positions
        lsb_is_5 = 1 if digits[0] == 5 else 0
        other_5s = num_5s - lsb_is_5
        expected_unprot = lsb_is_5 + other_5s * (4/9)

        ratio = actual_unprot / expected_unprot if expected_unprot > 0 else 0
        ratios.append((n, ratio))

        print(f" {n:3} | {m:6} | {num_5s:3} | {actual_unprot:16} | {expected_unprot:18.2f} | {ratio:.2f}")

    # Part B: Adjacent pair distribution
    print("\n" + "=" * 70)
    print("PART B: Adjacent Pair Distribution in 2^n vs Random")
    print("=" * 70)

    # Aggregate pairs from 2^n for n = 50..150
    actual_pairs = Counter()
    total_pairs_actual = 0

    for n in range(50, 151):
        digits = get_digits(n)
        pairs = count_adjacent_pairs(digits)
        for pair, count in pairs.items():
            actual_pairs[pair] += count
            total_pairs_actual += count

    # Focus on the "killing" pairs: (1,5), (2,5), (3,5), (4,5)
    killing_pairs = [(1, 5), (2, 5), (3, 5), (4, 5)]

    print("\nKilling pairs (low, 5) - these create zeros on doubling:")
    print("\n  Pair | Actual count | Actual freq | Random freq | Ratio")
    print("-" * 60)

    # Random expectation: each pair (a, b) with a,b in 1-9 has freq 1/81
    # But we're looking at zeroless strings, so freq = 1/81
    random_freq = 1/81

    for pair in killing_pairs:
        actual_count = actual_pairs[pair]
        actual_freq = actual_count / total_pairs_actual
        ratio = actual_freq / random_freq
        print(f"  {pair} | {actual_count:12} | {actual_freq:.4f}      | {random_freq:.4f}      | {ratio:.2f}")

    # Sum of all killing pairs
    total_killing = sum(actual_pairs[p] for p in killing_pairs)
    total_killing_freq = total_killing / total_pairs_actual
    expected_killing_freq = 4 * random_freq  # 4 killing pairs
    print(f"\n  ALL  | {total_killing:12} | {total_killing_freq:.4f}      | {expected_killing_freq:.4f}      | {total_killing_freq/expected_killing_freq:.2f}")

    # Part C: Full pair distribution heatmap
    print("\n" + "=" * 70)
    print("PART C: Full Adjacent Pair Frequencies (actual/random ratio)")
    print("=" * 70)

    print("\nRatio of actual frequency to random (1/81). Values > 1 are over-represented.")
    print("\n     | ", end="")
    for d2 in range(1, 10):
        print(f"  {d2}  ", end="")
    print("\n" + "-" * 55)

    for d1 in range(1, 10):
        print(f"  {d1}  |", end="")
        for d2 in range(1, 10):
            count = actual_pairs[(d1, d2)]
            freq = count / total_pairs_actual
            ratio = freq / random_freq
            if ratio > 1.2:
                print(f" {ratio:.1f}*", end="")
            elif ratio < 0.8:
                print(f" {ratio:.1f}-", end="")
            else:
                print(f" {ratio:.1f} ", end="")
        print()

    # Part D: The specific "5X" patterns
    print("\n" + "=" * 70)
    print("PART D: The '5 followed by X' Patterns")
    print("=" * 70)

    print("\nFor each X, frequency of '5X' pattern:")
    print("\n  X | Actual freq | Random freq (1/81) | Ratio | Status")
    print("-" * 60)

    for x in range(1, 10):
        pair = (x, 5)  # Note: (d_{i-1}, d_i) so this is "X followed by 5" in MSB→LSB
        # Wait, we want "5 followed by X" which in LSB-first is (X, 5)
        # Actually in LSB-first, d_{i-1} is to the RIGHT of d_i
        # So (d_{i-1}, d_i) = (X, 5) means position i has 5, position i-1 has X
        # i.e., in the number, X is to the right of 5
        count = actual_pairs[(x, 5)]
        freq = count / total_pairs_actual
        ratio = freq / random_freq
        status = "KILLING" if x in [1, 2, 3, 4] else "safe"
        print(f"  {x} | {freq:.4f}      | {random_freq:.4f}             | {ratio:.2f}  | {status}")

    # Part E: Why does the orbit fail earlier?
    print("\n" + "=" * 70)
    print("PART E: Cumulative Analysis - When Does Protection Fail?")
    print("=" * 70)

    # Track cumulative "close calls" - zeroless but with unprotected 5s
    print("\nFor each zeroless 2^n, how many unprotected 5s does it have?")

    zeroless = []
    for n in range(201):
        digits = get_digits(n)
        if is_zeroless(digits):
            unprot = count_unprotected_5s(digits)
            zeroless.append((n, len(digits), unprot))

    print("\n  n | digits | unprot5 | Status")
    print("-" * 45)
    for n, m, unprot in zeroless:
        if n >= 30:
            status = "TERMINATOR" if unprot > 0 else "SURVIVOR"
            print(f" {n:3} | {m:6} | {unprot:7} | {status}")

    # Part F: Monte Carlo comparison
    print("\n" + "=" * 70)
    print("PART F: Monte Carlo - Random Zeroless Strings at Same Lengths")
    print("=" * 70)

    print("\nFor each 2^n length, generate 1000 random zeroless strings.")
    print("Compare protection rate.\n")

    random.seed(42)
    print("  m (digits) | Actual (2^n) | Random avg | Random std | Actual/Random")
    print("-" * 70)

    test_lengths = [10, 15, 20, 25, 26, 30]
    for m in test_lengths:
        # Find n with approximately m digits
        n = int(m / 0.30103)
        actual_digits = get_digits(n)
        actual_m = len(actual_digits)
        actual_unprot = count_unprotected_5s(actual_digits)

        # Generate random strings
        random_unprot = []
        for _ in range(1000):
            rand_digits = random_zeroless_string(actual_m)
            random_unprot.append(count_unprotected_5s(rand_digits))

        avg_rand = sum(random_unprot) / len(random_unprot)
        std_rand = (sum((x - avg_rand)**2 for x in random_unprot) / len(random_unprot)) ** 0.5

        ratio = actual_unprot / avg_rand if avg_rand > 0 else 0
        print(f" {actual_m:11} | {actual_unprot:12} | {avg_rand:10.2f} | {std_rand:10.2f} | {ratio:.2f}")

    # Part G: The critical observation
    print("\n" + "=" * 70)
    print("PART G: Key Insight - Digit Distribution in Powers of 2")
    print("=" * 70)

    # Count digit frequencies in 2^n for various n
    print("\nDigit frequency in 2^n (should be ~1/9 = 0.111 for random):")
    print("\n  Range    |  1    2    3    4    5    6    7    8    9")
    print("-" * 65)

    for start, end in [(50, 100), (100, 150), (150, 200)]:
        digit_counts = Counter()
        total_digits = 0
        for n in range(start, end):
            digits = get_digits(n)
            for d in digits:
                if d != 0:  # Only count zeroless digits for fair comparison
                    digit_counts[d] += 1
                    total_digits += 1

        freqs = [digit_counts[d] / total_digits for d in range(1, 10)]
        freq_str = " ".join(f"{f:.2f}" for f in freqs)
        print(f"  {start}-{end:3}   | {freq_str}")

    print(f"\n  Random   |", " ".join(["0.11"] * 9))


if __name__ == "__main__":
    main()
