"""
Exp 86: Transition Statistics from ONLY Zeroless Powers

Hypothesis: The 22% killing suppression from Exp 62-71 might only appear
when we condition on actually-zeroless powers (n ≤ 86), not the general
population of pairs within powers that happen to have zeros elsewhere.

This experiment computes transition statistics ONLY from powers 2^n
that are completely zeroless.
"""

import sys
sys.set_int_max_str_digits(50000)
from collections import Counter


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def is_zeroless(n):
    """Check if 2^n has no zero digits."""
    power = 2 ** n
    while power > 0:
        if power % 10 == 0:
            return False
        power //= 10
    return True


def main():
    print("=" * 70)
    print("Exp 86: Transition Statistics from ONLY Zeroless Powers")
    print("=" * 70)

    # Find all zeroless powers
    zeroless_powers = []
    for n in range(1, 200):
        if is_zeroless(n):
            zeroless_powers.append(n)

    print(f"\nZeroless powers found: {len(zeroless_powers)}")
    print(f"Range: n = {min(zeroless_powers)} to {max(zeroless_powers)}")
    print(f"Powers: {zeroless_powers[:20]}... (showing first 20)")

    if max(zeroless_powers) == 86:
        print("\n*** Confirmed: Last zeroless power is 2^86 ***")

    low_digits = {1, 2, 3, 4}
    high_digits = {5, 6, 7, 8, 9}

    # Count pairs and 3-grams from ONLY zeroless powers
    pair_counts = Counter()
    N0 = Counter()  # 3-grams with low predecessor
    N1 = Counter()  # 3-grams with high predecessor

    total_pairs = 0
    total_triples = 0

    for n in zeroless_powers:
        digits = get_digits(n)

        # Pairs
        for i in range(1, len(digits)):
            a, b = digits[i-1], digits[i]
            pair_counts[(a, b)] += 1
            total_pairs += 1

        # Triples
        for i in range(2, len(digits)):
            x, a, b = digits[i-2], digits[i-1], digits[i]
            total_triples += 1
            if x in low_digits:
                N0[(a, b)] += 1
            else:
                N1[(a, b)] += 1

    print(f"\nTotal pairs from zeroless powers: {total_pairs}")
    print(f"Total triples from zeroless powers: {total_triples}")
    print(f"  From low predecessor (carry=0): {sum(N0.values())}")
    print(f"  From high predecessor (carry=1): {sum(N1.values())}")

    # Build marginal 9x9 transition matrix
    print("\n" + "=" * 70)
    print("MARGINAL 9×9 TRANSITION MATRIX (from zeroless powers only)")
    print("=" * 70)

    Q = {}
    for a in range(1, 10):
        row_sum = sum(pair_counts[(a, b)] for b in range(1, 10))
        Q[a] = {}
        for b in range(1, 10):
            Q[a][b] = pair_counts[(a, b)] / row_sum if row_sum > 0 else 0

    print("\n       ", end="")
    for b in range(1, 10):
        print(f"   {b}    ", end="")
    print()
    for a in range(1, 10):
        print(f"  {a} |", end="")
        for b in range(1, 10):
            print(f" {Q[a][b]:.4f}", end="")
        print()

    # Killing pairs analysis
    print("\n" + "=" * 70)
    print("KILLING PAIRS ANALYSIS (Zeroless Powers Only)")
    print("=" * 70)

    # Marginal digit distribution
    digit_counts = Counter()
    for a in range(1, 10):
        digit_counts[a] = sum(pair_counts[(a, b)] for b in range(1, 10))

    total_digits = sum(digit_counts.values())
    pi = {d: digit_counts[d] / total_digits for d in range(1, 10)}

    print("\nMarginal digit distribution π[d]:")
    for d in range(1, 10):
        print(f"  π[{d}] = {pi[d]:.4f}  (uniform = {1/9:.4f}, diff = {pi[d] - 1/9:+.4f})")

    # Killing mass
    print("\nKilling pairs (a, 5) with a ∈ {1,2,3,4}:")
    killing_mass = 0
    for a in [1, 2, 3, 4]:
        pair_prob = pi[a] * Q[a][5]
        killing_mass += pair_prob
        print(f"  π[{a}]·Q[{a}][5] = {pi[a]:.4f} × {Q[a][5]:.4f} = {pair_prob:.6f}")

    print(f"\n  Total killing mass: {killing_mass:.6f}")
    print(f"  Baseline (4/81): {4/81:.6f}")
    print(f"  *** Suppression ratio: {killing_mass / (4/81):.3f} ***")

    # Protecting mass
    print("\nProtecting pairs (a, 5) with a ∈ {5,6,7,8,9}:")
    protecting_mass = 0
    for a in [5, 6, 7, 8, 9]:
        pair_prob = pi[a] * Q[a][5]
        protecting_mass += pair_prob
        print(f"  π[{a}]·Q[{a}][5] = {pi[a]:.4f} × {Q[a][5]:.4f} = {pair_prob:.6f}")

    print(f"\n  Total protecting mass: {protecting_mass:.6f}")
    print(f"  Baseline (5/81): {5/81:.6f}")
    print(f"  Enhancement ratio: {protecting_mass / (5/81):.3f}")

    # Now do conditional analysis
    print("\n" + "=" * 70)
    print("CARRY-CONDITIONED ANALYSIS (Zeroless Powers Only)")
    print("=" * 70)

    if sum(N0.values()) > 0 and sum(N1.values()) > 0:
        # Build Q^(0) and Q^(1)
        Q0 = {}
        Q1 = {}
        for a in range(1, 10):
            row_sum_0 = sum(N0[(a, b)] for b in range(1, 10))
            row_sum_1 = sum(N1[(a, b)] for b in range(1, 10))
            Q0[a] = {}
            Q1[a] = {}
            for b in range(1, 10):
                Q0[a][b] = N0[(a, b)] / row_sum_0 if row_sum_0 > 0 else 0
                Q1[a][b] = N1[(a, b)] / row_sum_1 if row_sum_1 > 0 else 0

        print("\nQ^(0)[a,5] vs Q^(1)[a,5] for killing sources:")
        print("\n  a  | Q^(0)[a,5] | Q^(1)[a,5] | Ratio Q0/Q1")
        print("-" * 50)
        for a in [1, 2, 3, 4]:
            q0 = Q0[a][5]
            q1 = Q1[a][5]
            ratio = q0 / q1 if q1 > 0 else float('inf')
            print(f"  {a}  |   {q0:.4f}   |   {q1:.4f}   |   {ratio:.3f}")

        # Killing mass by carry
        pi_0 = {}
        pi_1 = {}
        total_c0 = sum(N0.values())
        total_c1 = sum(N1.values())
        for a in range(1, 10):
            pi_0[a] = sum(N0[(a, b)] for b in range(1, 10)) / total_c0
            pi_1[a] = sum(N1[(a, b)] for b in range(1, 10)) / total_c1

        killing_c0 = sum(pi_0[a] * Q0[a][5] for a in [1, 2, 3, 4])
        killing_c1 = sum(pi_1[a] * Q1[a][5] for a in [1, 2, 3, 4])

        print(f"\nKilling transition mass:")
        print(f"  Under carry=0: {killing_c0:.6f} (ratio to baseline: {killing_c0 / (4/81):.3f})")
        print(f"  Under carry=1: {killing_c1:.6f} (ratio to baseline: {killing_c1 / (4/81):.3f})")

    # Compare with Exp 82 (general population)
    print("\n" + "=" * 70)
    print("COMPARISON: Zeroless-Only vs General Population")
    print("=" * 70)

    print("""
                        | Zeroless Only | General (Exp 82) | 52A Prediction
    --------------------|---------------|------------------|---------------
    Killing suppression |     ???       |      0.981       |    0.78
    """)

    print(f"    Killing suppression |     {killing_mass / (4/81):.3f}       |      0.981       |    0.78")

    if killing_mass / (4/81) < 0.85:
        print("\n*** FINDING: Zeroless powers DO show stronger killing suppression! ***")
    else:
        print("\n*** FINDING: Zeroless powers do NOT show stronger killing suppression. ***")

    # Raw counts for reference
    print("\n" + "=" * 70)
    print("RAW PAIR COUNTS (for reference)")
    print("=" * 70)

    print("\n       ", end="")
    for b in range(1, 10):
        print(f"  {b}  ", end="")
    print()
    for a in range(1, 10):
        print(f"  {a} |", end="")
        for b in range(1, 10):
            print(f" {pair_counts[(a, b)]:3d} ", end="")
        print()


if __name__ == "__main__":
    main()
