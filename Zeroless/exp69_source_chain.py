"""
Exp 69: The Source Chain - Why Digit Correlations Arise

Exp 68 showed (7, high) is rare because:
1. 52.7% of 7s come from d=3 (carry-out 0)
2. Only 4/9 source digits produce high output with carry=0
3. The digit distribution following 3 and 8 is biased

Why is the distribution biased? Let's trace the source chain.

If position i has digit 7, and position i+1 has digit X, then:
- Position i in 2^n came from position i in 2^{n-1} with some digit d_i
- Position i+1 in 2^n came from position i+1 in 2^{n-1} with some digit d_{i+1}
- The carry from i to i+1 depends on d_i

So the pair (7, X) comes from (d_i, d_{i+1}) where:
- 7 = (2*d_i + c_in) mod 10  →  d_i ∈ {3, 8} with c_in=1
- X = (2*d_{i+1} + c_out) mod 10  where c_out = (2*d_i + c_in) // 10

For d_i=3, c_in=1: c_out = 7//10 = 0
For d_i=8, c_in=1: c_out = 17//10 = 1

So we need to understand the PAIR distribution (3, d_{i+1}) and (8, d_{i+1}) in 2^n.
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
    print("Exp 69: The Source Chain - Why Digit Correlations Arise")
    print("=" * 70)

    # Part A: Pair distributions (d_i, d_{i+1}) for d_i ∈ {3, 8}
    print("\n" + "=" * 70)
    print("PART A: Pair Distributions in 2^n")
    print("=" * 70)

    pairs_from_3 = Counter()
    pairs_from_8 = Counter()

    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(len(digits) - 1):
            if digits[i] == 3:
                pairs_from_3[digits[i+1]] += 1
            elif digits[i] == 8:
                pairs_from_8[digits[i+1]] += 1

    print("\nDistribution of (3, d) pairs (d = digit to the LEFT of 3):")
    total_3 = sum(pairs_from_3.values())
    for d in range(10):
        count = pairs_from_3[d]
        pct = 100 * count / total_3
        bar = "*" * int(pct * 2)
        print(f"  (3, {d}): {pct:5.1f}% {bar}")

    print("\nDistribution of (8, d) pairs:")
    total_8 = sum(pairs_from_8.values())
    for d in range(10):
        count = pairs_from_8[d]
        pct = 100 * count / total_8
        bar = "*" * int(pct * 2)
        print(f"  (8, {d}): {pct:5.1f}% {bar}")

    # Part B: What output pairs do these create?
    print("\n" + "=" * 70)
    print("PART B: Output Pairs (7, X) from Source Pairs")
    print("=" * 70)

    print("\nFrom (3, d) with carry-in 1 to position 3:")
    print("  Position 3: 2*3+1=7, carry-out=0")
    print("  Position next: 2*d+0 → output")
    print()
    for d in range(10):
        output = (2 * d + 0) % 10
        pct = 100 * pairs_from_3[d] / total_3
        high = "HIGH" if output >= 5 else "low"
        print(f"  (3, {d}) → (7, {output}) [{high}]: {pct:5.1f}%")

    print("\nFrom (8, d) with carry-in 1 to position 8:")
    print("  Position 8: 2*8+1=17 → 7, carry-out=1")
    print("  Position next: 2*d+1 → output")
    print()
    for d in range(10):
        output = (2 * d + 1) % 10
        pct = 100 * pairs_from_8[d] / total_8
        high = "HIGH" if output >= 5 else "low"
        print(f"  (8, {d}) → (7, {output}) [{high}]: {pct:5.1f}%")

    # Part C: Compute expected (7, high) rate
    print("\n" + "=" * 70)
    print("PART C: Predicted (7, high) Rate from Source Pairs")
    print("=" * 70)

    # P(7 from 3) * P(high | 7 from 3) + P(7 from 8) * P(high | 7 from 8)

    # Count how often 7 comes from 3 vs 8
    seven_from_3 = 0
    seven_from_8 = 0

    for n in range(51, 200):
        prev_digits = get_digits(n-1)
        curr_digits = get_digits(n)

        # Track carries
        carry = 0
        for i in range(len(prev_digits)):
            d = prev_digits[i]
            val = 2 * d + carry
            if i < len(curr_digits) and curr_digits[i] == 7:
                if d == 3 and carry == 1:
                    seven_from_3 += 1
                elif d == 8 and carry == 1:
                    seven_from_8 += 1
            carry = val // 10

    total_7s = seven_from_3 + seven_from_8
    p_7_from_3 = seven_from_3 / total_7s
    p_7_from_8 = seven_from_8 / total_7s

    print(f"\nP(7 from 3) = {p_7_from_3:.3f}")
    print(f"P(7 from 8) = {p_7_from_8:.3f}")

    # P(high | 7 from 3) = sum over d where (2*d+0) mod 10 >= 5 of P(d | 3)
    p_high_given_3 = sum(
        pairs_from_3[d] / total_3
        for d in range(10)
        if (2*d + 0) % 10 >= 5
    )

    # P(high | 7 from 8) = sum over d where (2*d+1) mod 10 >= 5 of P(d | 8)
    p_high_given_8 = sum(
        pairs_from_8[d] / total_8
        for d in range(10)
        if (2*d + 1) % 10 >= 5
    )

    print(f"\nP(high | 7 from 3) = {p_high_given_3:.3f}")
    print(f"P(high | 7 from 8) = {p_high_given_8:.3f}")

    p_high_after_7 = p_7_from_3 * p_high_given_3 + p_7_from_8 * p_high_given_8

    print(f"\nP(high after 7) = {p_7_from_3:.3f} * {p_high_given_3:.3f} + {p_7_from_8:.3f} * {p_high_given_8:.3f}")
    print(f"               = {p_high_after_7:.3f}")
    print(f"Random: 5/9 = {5/9:.3f}")
    print(f"Ratio: {p_high_after_7 / (5/9):.2f}")

    # Part D: The deeper question - why are (3, d) pairs distributed this way?
    print("\n" + "=" * 70)
    print("PART D: Why Is (3, d) Distribution Biased?")
    print("=" * 70)

    print("\nFor (3, d) to appear in 2^n, in 2^{n-1} we need:")
    print("  d_{i-1} such that (2*d_{i-1} + c_{i-1}) mod 10 = 3")
    print("  d_i such that (2*d_i + c_i) mod 10 = d")
    print()
    print("3 is produced from:")
    print("  d=1 with c=1: 2*1+1=3, carry-out=0")
    print("  d=6 with c=1: 2*6+1=13 → 3, carry-out=1")
    print()
    print("So 3 has carry-out 0 (from 1) or carry-out 1 (from 6).")

    # Count how often 3 comes from 1 vs 6
    three_from_1 = 0
    three_from_6 = 0

    for n in range(51, 200):
        prev_digits = get_digits(n-1)
        curr_digits = get_digits(n)

        carry = 0
        for i in range(len(prev_digits)):
            d = prev_digits[i]
            val = 2 * d + carry
            if i < len(curr_digits) and curr_digits[i] == 3:
                if d == 1 and carry == 1:
                    three_from_1 += 1
                elif d == 6 and carry == 1:
                    three_from_6 += 1
            carry = val // 10

    total_3s = three_from_1 + three_from_6
    print(f"\n3s from d=1: {three_from_1} ({100*three_from_1/total_3s:.1f}%)")
    print(f"3s from d=6: {three_from_6} ({100*three_from_6/total_3s:.1f}%)")

    # Part E: The cascade effect
    print("\n" + "=" * 70)
    print("PART E: The Carry Cascade Effect")
    print("=" * 70)

    print("\nEach digit's output depends on the carry from the right.")
    print("The carry is determined by the source digit to the right.")
    print()
    print("This creates a CHAIN of dependencies:")
    print("  d_1 → c_2 → output_2 → c_3 → output_3 → ...")
    print()
    print("The stationary distribution of carries is NOT independent!")
    print("Adjacent positions are correlated through the carry chain.")

    # Part F: The key insight
    print("\n" + "=" * 70)
    print("PART F: Key Insight - Transfer Matrix Structure")
    print("=" * 70)

    print("\nThe joint distribution of (digit, carry) pairs follows a Markov chain.")
    print("State = (d, c) where d is digit and c is carry-in.")
    print("Transition: (d, c) → (d', c') where c' = (2*d+c) >= 10.")
    print()
    print("This is exactly the transfer matrix from APPROACH 50!")
    print("The correlations between adjacent digits come from this chain.")
    print()
    print("For zeroless numbers (d ∈ {1,..,9}):")
    print("  If c=0: outputs are 2,4,6,8,0,2,4,6,8 for d=1,..,9")
    print("  If c=1: outputs are 3,5,7,9,1,3,5,7,9 for d=1,..,9")
    print()
    print("The (7, high) suppression comes from:")
    print("  1. 7 requires c=1 to be produced (from d=3 or d=8)")
    print("  2. The carry-out from d=3 is 0, from d=8 is 1")
    print("  3. 52.7% of 7s come from d=3, so 52.7% have c_out=0")
    print("  4. With c_out=0, only 4/9 zeroless digits produce high output")
    print()
    print("This is a STRUCTURAL bias, not random fluctuation!")

    # Part G: Verify with direct computation
    print("\n" + "=" * 70)
    print("PART G: Direct Verification of (7, X) Distribution")
    print("=" * 70)

    pairs_7X = Counter()
    total_7_pairs = 0

    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            if digits[i-1] == 7:
                pairs_7X[digits[i]] += 1
                total_7_pairs += 1

    print("\nActual (7, X) distribution in 2^n for n=50..199:")
    for X in range(10):
        count = pairs_7X[X]
        pct = 100 * count / total_7_pairs if total_7_pairs > 0 else 0
        high = "HIGH" if X >= 5 else "low"
        expected = 100 / 9 if X != 0 else 0  # uniform over 1-9
        bar = "*" * int(pct * 2)
        print(f"  (7, {X}): {pct:5.1f}% (expected {expected:4.1f}%) [{high}] {bar}")

    actual_high = sum(pairs_7X[X] for X in range(5, 10))
    print(f"\nActual (7, high): {100*actual_high/total_7_pairs:.1f}%")
    print(f"Expected (random): {100*5/9:.1f}%")
    print(f"Predicted (model): {100*p_high_after_7:.1f}%")


if __name__ == "__main__":
    main()
