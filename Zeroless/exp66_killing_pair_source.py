"""
Exp 66: Where Do Killing Pairs Come From?

Exp 62 showed killing pairs are 20% less frequent in 2^n than random.
Exp 65 showed new 5s come from 2 or 7 with carry.

Key question: Why are (1,5), (2,5), (3,5), (4,5) patterns rare in 2^n?

For a killing pair (X,5) at positions (i-1, i) in 2^{n+1}:
- Position i has 5, from d_i ∈ {2,7} with c_i = 1
- Position i-1 has X ∈ {1,2,3,4}, from some d_{i-1} with some c_{i-1}

Let's trace exactly what configurations produce each killing pair.
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
    print("Exp 66: Where Do Killing Pairs Come From?")
    print("=" * 70)

    # Part A: What source patterns produce each killing pair?
    print("\n" + "=" * 70)
    print("PART A: Source Patterns for Killing Pairs")
    print("=" * 70)

    print("\nFor (X, 5) at positions (i-1, i) in the OUTPUT:")
    print("  - Position i: d ∈ {2,7} with carry 1 → output 5")
    print("  - Position i-1: d with carry c → output X")
    print("  - Carry at i = 1 requires d_{i-1} ≥ 5")
    print()

    # For each killing pair, find all source patterns
    for X in [1, 2, 3, 4]:
        print(f"\n{'='*50}")
        print(f"Killing pair ({X}, 5):")
        print(f"{'='*50}")

        sources = []
        for d_prev in range(5, 10):  # d_{i-1} ≥ 5 required for carry
            for c_prev in [0, 1]:
                output = (2 * d_prev + c_prev) % 10
                if output == X:
                    sources.append((d_prev, c_prev))
                    print(f"  d_{'{i-1}'} = {d_prev}, c_{'{i-1}'} = {c_prev} → output {X}")

        if not sources:
            print("  NO SOURCE PATTERNS! This pair cannot appear.")

    # Part B: Count source patterns in actual powers of 2
    print("\n" + "=" * 70)
    print("PART B: Frequency of Source Patterns in 2^n")
    print("=" * 70)

    # For each potential source of a killing pair, count occurrences
    # A killing pair (X, 5) requires:
    #   d_{i-1} ∈ source_for_X AND d_{i-1} ≥ 5
    #   d_i ∈ {2, 7}

    print("\nCount (d_{i-1}, d_i) pairs where d_{i-1} ≥ 5 and d_i ∈ {2,7}:")

    source_pairs = Counter()
    total_pairs = 0

    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            if digits[i] in [2, 7] and digits[i-1] >= 5:
                source_pairs[(digits[i-1], digits[i])] += 1
            total_pairs += 1

    print("\n  (d_{i-1}, d_i) | Count | Fraction | Output at i-1 (c=0) | Output at i-1 (c=1)")
    print("-" * 85)

    for d_prev in range(5, 10):
        for d_curr in [2, 7]:
            count = source_pairs[(d_prev, d_curr)]
            frac = count / total_pairs if total_pairs > 0 else 0
            out_c0 = (2 * d_prev) % 10
            out_c1 = (2 * d_prev + 1) % 10
            print(f"  ({d_prev}, {d_curr})       | {count:5} | {frac:.4f}   | {out_c0:19} | {out_c1}")

    # Part C: The carry distribution matters!
    print("\n" + "=" * 70)
    print("PART C: Carry Distribution at Source Positions")
    print("=" * 70)

    print("\nKey: Whether the output is a killing digit (1,2,3,4) depends on carry!")
    print("For d_{i-1} ∈ {5,6,7,8,9}:")
    print()
    for d in range(5, 10):
        out_c0 = (2 * d) % 10
        out_c1 = (2 * d + 1) % 10
        killing_c0 = "KILL" if out_c0 in [1, 2, 3, 4] else "safe"
        killing_c1 = "KILL" if out_c1 in [1, 2, 3, 4] else "safe"
        print(f"  d={d}: c=0 → {out_c0} ({killing_c0}), c=1 → {out_c1} ({killing_c1})")

    print("\n\n*** CRITICAL OBSERVATION ***")
    print("Killing outputs from high digits:")
    print("  - d=5, c=1 → 1 (KILL)")
    print("  - d=6, c=0 → 2 (KILL)")
    print("  - d=6, c=1 → 3 (KILL)")
    print("  - d=7, c=0 → 4 (KILL)")
    print("\nSafe outputs from high digits:")
    print("  - d=7, c=1 → 5 (safe)")
    print("  - d=8, c=0 → 6 (safe)")
    print("  - d=8, c=1 → 7 (safe)")
    print("  - d=9, c=0 → 8 (safe)")
    print("  - d=9, c=1 → 9 (safe)")
    print("  - d=5, c=0 → 0 (creates zero, not relevant)")

    # Part D: Carry statistics at positions with high digits
    print("\n" + "=" * 70)
    print("PART D: Carry Statistics at High-Digit Positions")
    print("=" * 70)

    print("\nFor each high digit d, what's P(carry = 1)?")

    carry_stats = {d: {'c0': 0, 'c1': 0} for d in range(5, 10)}

    for n in range(50, 200):
        digits = get_digits(n)
        carry = 0
        for i, d in enumerate(digits):
            if d >= 5:
                if carry == 0:
                    carry_stats[d]['c0'] += 1
                else:
                    carry_stats[d]['c1'] += 1
            val = 2 * d + carry
            carry = val // 10

    print("\n  d | Count(c=0) | Count(c=1) | P(c=1) | Output(c=0) | Output(c=1) | P(killing output)")
    print("-" * 90)

    for d in range(5, 10):
        c0 = carry_stats[d]['c0']
        c1 = carry_stats[d]['c1']
        total = c0 + c1
        p_c1 = c1 / total if total > 0 else 0
        out_c0 = (2 * d) % 10
        out_c1 = (2 * d + 1) % 10
        # P(killing) = P(c=0)*I(out_c0 killing) + P(c=1)*I(out_c1 killing)
        killing_c0 = 1 if out_c0 in [1, 2, 3, 4] else 0
        killing_c1 = 1 if out_c1 in [1, 2, 3, 4] else 0
        p_killing = (1 - p_c1) * killing_c0 + p_c1 * killing_c1
        print(f"  {d} | {c0:10} | {c1:10} | {p_c1:.3f}  | {out_c0:11} | {out_c1:11} | {p_killing:.3f}")

    # Part E: The bias mechanism
    print("\n" + "=" * 70)
    print("PART E: The Bias Mechanism")
    print("=" * 70)

    print("\n*** KEY INSIGHT ***")
    print()
    print("Killing pairs require HIGH digits (5-9) to produce LOW outputs (1-4).")
    print("This happens when:")
    print("  - d=5 with c=1 → 1")
    print("  - d=6 with c=0 or c=1 → 2 or 3")
    print("  - d=7 with c=0 → 4")
    print()
    print("Safe outputs happen when:")
    print("  - d=7 with c=1 → 5")
    print("  - d=8, d=9 with any carry → 6,7,8,9")
    print()
    print("The question is: what's P(carry = 1) at positions where d ∈ {5,6,7}?")
    print()
    print("From the stationary distribution, P(carry = 1) = 5/9 ≈ 0.556")
    print("This is because carry-out = 1 iff d ≥ 5, and P(d ≥ 5) = 5/9.")
    print()
    print("So for d=5: P(killing output) = P(c=1) = 5/9")
    print("For d=6: P(killing output) = 1 (both c=0 and c=1 produce killing)")
    print("For d=7: P(killing output) = P(c=0) = 4/9")
    print("For d=8, d=9: P(killing output) = 0")

    # Part F: Expected killing pair rate
    print("\n" + "=" * 70)
    print("PART F: Expected Killing Pair Rate")
    print("=" * 70)

    print("\nA killing pair (X, 5) requires:")
    print("  1. Position i has d_i ∈ {2, 7}")
    print("  2. Position i-1 has d_{i-1} ≥ 5 (for carry)")
    print("  3. Output at i-1 is in {1,2,3,4}")
    print()

    # Random model calculation
    p_2or7 = 2/9  # P(d_i ∈ {2,7})
    p_high = 5/9  # P(d_{i-1} ≥ 5)

    # P(output ∈ {1,2,3,4} | d_{i-1} ≥ 5)
    # Sum over d=5,6,7,8,9 of P(d) * P(killing | d)
    p_killing_given_high = (
        (1/5) * (5/9) +  # d=5: kills when c=1
        (1/5) * 1 +      # d=6: always kills
        (1/5) * (4/9) +  # d=7: kills when c=0
        (1/5) * 0 +      # d=8: never kills
        (1/5) * 0        # d=9: never kills
    )

    p_killing_pair = p_2or7 * p_high * p_killing_given_high

    print(f"Random model:")
    print(f"  P(d_i ∈ {{2,7}}) = {p_2or7:.4f}")
    print(f"  P(d_{{i-1}} ≥ 5) = {p_high:.4f}")
    print(f"  P(killing output | d_{{i-1}} ≥ 5) = {p_killing_given_high:.4f}")
    print(f"  P(killing pair) = {p_killing_pair:.4f}")
    print()
    print(f"Expected killing pairs per {1000} adjacent pairs: {1000 * p_killing_pair:.1f}")

    # Actual rate from Exp 62: 0.0395 (all 4 killing pairs)
    print(f"\nActual rate from Exp 62: 0.0395")
    print(f"Ratio: {0.0395 / p_killing_pair:.2f}")


if __name__ == "__main__":
    main()
