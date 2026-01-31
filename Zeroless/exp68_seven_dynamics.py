"""
Exp 68: Why Are (7, high) Patterns Rare?

Key finding from Exp 67: (7, X) pairs with X ≥ 6 are underrepresented.
- (7, 6): 65% of random
- (7, 7): 27% of random
- (7, 8): 60% of random
- (7, 9): 60% of random

Why? Let's trace the doubling dynamics.

7 is produced from:
- d=3 with carry 1: 2*3+1=7, carry-out=0
- d=8 with carry 1: 2*8+1=17, output 7, carry-out=1

The carry-out determines what can appear to the LEFT of 7.
- If 7 came from 3: carry-out=0, so left position receives c=0
- If 7 came from 8: carry-out=1, so left position receives c=1

What digits X appear to the left of 7?
X = (2*d + c) mod 10, where d is the source digit and c is the carry from 7's position.
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


def trace_doubling(digits):
    """
    Trace doubling operation, returning (output_digits, carries).
    """
    result = []
    carries = [0]  # carries[i] = carry entering position i
    carry = 0
    for d in digits:
        val = 2 * d + carry
        result.append(val % 10)
        carry = val // 10
        carries.append(carry)
    if carry > 0:
        result.append(carry)
    return result, carries[:-1]


def main():
    print("=" * 70)
    print("Exp 68: Why Are (7, high) Patterns Rare?")
    print("=" * 70)

    # Part A: Where do 7s come from?
    print("\n" + "=" * 70)
    print("PART A: Source Digits for 7s")
    print("=" * 70)

    print("\n7 is produced from:")
    print("  d=3 with c=1: 2*3+1=7, carry-out=0")
    print("  d=8 with c=1: 2*8+1=17 → output 7, carry-out=1")

    # Count how often 7 comes from 3 vs 8
    source_3 = 0
    source_8 = 0

    for n in range(50, 151):
        prev_digits = get_digits(n - 1)
        curr_digits = get_digits(n)

        # Compute carries for the doubling
        _, carries = trace_doubling(prev_digits)

        for i in range(len(curr_digits)):
            if curr_digits[i] == 7:
                if i < len(prev_digits) and i < len(carries):
                    d = prev_digits[i]
                    c = carries[i]
                    if d == 3 and c == 1:
                        source_3 += 1
                    elif d == 8 and c == 1:
                        source_8 += 1

    total_7s = source_3 + source_8
    print(f"\nIn 2^n for n=50..150:")
    print(f"  7s from d=3: {source_3} ({100*source_3/total_7s:.1f}%)")
    print(f"  7s from d=8: {source_8} ({100*source_8/total_7s:.1f}%)")

    # Part B: What does this mean for (7, X) pairs?
    print("\n" + "=" * 70)
    print("PART B: Carry-Out from 7's Source")
    print("=" * 70)

    print("\nWhen 7 is produced, the carry-out is:")
    print("  From d=3: carry-out = 0 (since 3 < 5)")
    print("  From d=8: carry-out = 1 (since 8 ≥ 5)")
    print()
    print(f"So {100*source_3/total_7s:.1f}% of 7s have carry-out 0")
    print(f"And {100*source_8/total_7s:.1f}% of 7s have carry-out 1")

    # Part C: What digits X can appear after 7?
    print("\n" + "=" * 70)
    print("PART C: What Digits Can Follow 7?")
    print("=" * 70)

    print("\nIf 7 is at position i-1, the digit X at position i is:")
    print("  X = (2*d_i + c) mod 10")
    print("  where d_i is the source digit and c is carry from position i-1")
    print()

    # For each source of 7 and each possible d_i, compute X
    print("If 7 came from d=3 (carry-out=0):")
    for d_i in range(10):
        X = (2 * d_i + 0) % 10
        print(f"  d_i={d_i} → X={X}")

    print("\nIf 7 came from d=8 (carry-out=1):")
    for d_i in range(10):
        X = (2 * d_i + 1) % 10
        print(f"  d_i={d_i} → X={X}")

    # Part D: Which X values are high (≥5)?
    print("\n" + "=" * 70)
    print("PART D: Which Outputs Are High?")
    print("=" * 70)

    print("\nHigh outputs (≥5) from carry=0:")
    high_from_c0 = [d_i for d_i in range(10) if (2*d_i + 0) % 10 >= 5]
    print(f"  d_i ∈ {high_from_c0} → outputs {[(2*d+0)%10 for d in high_from_c0]}")

    print("\nHigh outputs (≥5) from carry=1:")
    high_from_c1 = [d_i for d_i in range(10) if (2*d_i + 1) % 10 >= 5]
    print(f"  d_i ∈ {high_from_c1} → outputs {[(2*d+1)%10 for d in high_from_c1]}")

    print("\n*** KEY INSIGHT ***")
    print(f"From carry=0: {len(high_from_c0)}/10 source digits produce high output")
    print(f"From carry=1: {len(high_from_c1)}/10 source digits produce high output")

    # Part E: Combine with source distribution
    print("\n" + "=" * 70)
    print("PART E: Expected (7, high) Frequency")
    print("=" * 70)

    p_7_from_3 = source_3 / total_7s
    p_7_from_8 = source_8 / total_7s

    # P(high | 7 from 3) = P(d_i produces high with c=0) = 4/9 (if digits uniform)
    # P(high | 7 from 8) = P(d_i produces high with c=1) = 4/9 (if digits uniform)

    # Wait, let me recount
    high_c0 = sum(1 for d in range(1,10) if (2*d + 0) % 10 >= 5)  # exclude 0
    high_c1 = sum(1 for d in range(1,10) if (2*d + 1) % 10 >= 5)  # exclude 0

    print(f"\nFrom carry=0: {high_c0}/9 zeroless source digits produce high output")
    print(f"From carry=1: {high_c1}/9 zeroless source digits produce high output")

    p_high_given_7 = p_7_from_3 * (high_c0/9) + p_7_from_8 * (high_c1/9)

    print(f"\nP(X ≥ 5 | 7 at position i-1) = {p_7_from_3:.3f} * {high_c0}/9 + {p_7_from_8:.3f} * {high_c1}/9")
    print(f"                              = {p_high_given_7:.3f}")
    print(f"Random expectation: 5/9 = {5/9:.3f}")
    print(f"Ratio: {p_high_given_7 / (5/9):.2f}")

    # Part F: But wait - what's the source distribution of d_i?
    print("\n" + "=" * 70)
    print("PART F: Source Distribution After 3 or 8")
    print("=" * 70)

    print("\nThe digit d_i at position i (which produces X after 7) is...")
    print("Let's check what digits follow 3 and 8 in powers of 2.")

    follows_3 = Counter()
    follows_8 = Counter()

    for n in range(50, 151):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            if digits[i-1] == 3:
                follows_3[digits[i]] += 1
            elif digits[i-1] == 8:
                follows_8[digits[i]] += 1

    print("\nDigits following 3:")
    total_3 = sum(follows_3.values())
    for d in range(10):
        count = follows_3[d]
        print(f"  {d}: {count} ({100*count/total_3:.1f}%)")

    print("\nDigits following 8:")
    total_8 = sum(follows_8.values())
    for d in range(10):
        count = follows_8[d]
        print(f"  {d}: {100*count/total_8:.1f}%")

    # Part G: Compute expected high output after 7
    print("\n" + "=" * 70)
    print("PART G: Predicted (7, high) Rate")
    print("=" * 70)

    # When 7 comes from 3, carry-out=0
    # The next position has digit from follows_3 distribution
    # Output is (2*d + 0) mod 10

    p_high_after_3 = 0
    for d in range(1, 10):
        if (2*d + 0) % 10 >= 5:
            p_high_after_3 += follows_3[d] / total_3

    # When 7 comes from 8, carry-out=1
    p_high_after_8 = 0
    for d in range(1, 10):
        if (2*d + 1) % 10 >= 5:
            p_high_after_8 += follows_8[d] / total_8

    print(f"\nP(high output | 7 from 3) = {p_high_after_3:.3f}")
    print(f"P(high output | 7 from 8) = {p_high_after_8:.3f}")

    p_high_after_7 = p_7_from_3 * p_high_after_3 + p_7_from_8 * p_high_after_8
    print(f"\nP(high output after 7) = {p_7_from_3:.3f} * {p_high_after_3:.3f} + {p_7_from_8:.3f} * {p_high_after_8:.3f}")
    print(f"                       = {p_high_after_7:.3f}")
    print(f"Random expectation: {5/9:.3f}")
    print(f"Ratio: {p_high_after_7 / (5/9):.2f}")

    # Part H: Verify against actual data
    print("\n" + "=" * 70)
    print("PART H: Verification Against Actual Data")
    print("=" * 70)

    # Count (7, X) pairs and check high rate
    pairs_7X = Counter()
    for n in range(50, 151):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            if digits[i-1] == 7:
                pairs_7X[digits[i]] += 1

    total_7X = sum(pairs_7X.values())
    high_7X = sum(pairs_7X[d] for d in range(5, 10))

    print(f"\nActual (7, high) pairs: {high_7X}/{total_7X} = {high_7X/total_7X:.3f}")
    print(f"Predicted: {p_high_after_7:.3f}")
    print(f"Random: {5/9:.3f}")


if __name__ == "__main__":
    main()
