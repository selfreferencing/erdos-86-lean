"""
Exp 82: Export Full Pair Matrix for GPT

Extract the actual 9x9 pair counts (zeroless digits only) for building
the explicit 18-state Markov transition matrix.
"""

from collections import Counter
import json


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
    print("Exp 82: Export Full Pair Matrix for GPT")
    print("=" * 70)

    # Count all (a, b) pairs in powers of 2 (zeroless only)
    pair_counts = Counter()
    total_pairs = 0

    # Use larger range for better statistics
    for n in range(50, 500):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            a, b = digits[i-1], digits[i]
            if a != 0 and b != 0:  # Only zeroless pairs
                pair_counts[(a, b)] += 1
                total_pairs += 1

    print(f"\nTotal zeroless pairs counted: {total_pairs}")
    print(f"Range: n = 50 to 499")

    # Build 9x9 matrix (digits 1-9)
    print("\n" + "=" * 70)
    print("RAW COUNTS (9x9 matrix, rows=a, cols=b)")
    print("=" * 70)

    # Header
    print("\n      ", end="")
    for b in range(1, 10):
        print(f"   {b}   ", end="")
    print()

    matrix = {}
    for a in range(1, 10):
        print(f"  {a} |", end="")
        matrix[a] = {}
        for b in range(1, 10):
            count = pair_counts[(a, b)]
            matrix[a][b] = count
            print(f" {count:5} ", end="")
        print()

    # Row sums (for transition probabilities)
    print("\n" + "=" * 70)
    print("ROW SUMS (total transitions from each digit)")
    print("=" * 70)

    row_sums = {}
    for a in range(1, 10):
        row_sums[a] = sum(matrix[a][b] for b in range(1, 10))
        print(f"  From digit {a}: {row_sums[a]}")

    # Transition probabilities Q[a][b] = P(next=b | current=a)
    print("\n" + "=" * 70)
    print("TRANSITION PROBABILITIES Q[a][b] = P(next=b | current=a)")
    print("=" * 70)

    print("\n       ", end="")
    for b in range(1, 10):
        print(f"   {b}    ", end="")
    print()

    Q = {}
    for a in range(1, 10):
        print(f"  {a} |", end="")
        Q[a] = {}
        for b in range(1, 10):
            prob = matrix[a][b] / row_sums[a] if row_sums[a] > 0 else 0
            Q[a][b] = prob
            print(f" {prob:.4f} ", end="")
        print()

    # Marginal digit distribution
    print("\n" + "=" * 70)
    print("MARGINAL DIGIT DISTRIBUTION π[d]")
    print("=" * 70)

    digit_counts = Counter()
    for a in range(1, 10):
        for b in range(1, 10):
            digit_counts[a] += matrix[a][b]  # Count as "from" digit

    total_digits = sum(digit_counts.values())
    pi = {}
    for d in range(1, 10):
        pi[d] = digit_counts[d] / total_digits
        print(f"  π[{d}] = {pi[d]:.4f}")

    # Stationary pair distribution
    print("\n" + "=" * 70)
    print("STATIONARY PAIR DISTRIBUTION π[a]·Q[a][b]")
    print("=" * 70)

    print("\nKilling pairs (a, 5) where a ∈ {1,2,3,4}:")
    killing_mass = 0
    for a in [1, 2, 3, 4]:
        pair_prob = pi[a] * Q[a][5]
        killing_mass += pair_prob
        print(f"  π[{a}]·Q[{a}][5] = {pi[a]:.4f} × {Q[a][5]:.4f} = {pair_prob:.6f}")
    print(f"  Total killing mass: {killing_mass:.6f}")
    print(f"  Baseline (4/81): {4/81:.6f}")
    print(f"  Ratio: {killing_mass / (4/81):.3f}")

    print("\nProtecting pairs (a, 5) where a ∈ {5,6,7,8,9}:")
    protecting_mass = 0
    for a in [5, 6, 7, 8, 9]:
        pair_prob = pi[a] * Q[a][5]
        protecting_mass += pair_prob
        print(f"  π[{a}]·Q[{a}][5] = {pi[a]:.4f} × {Q[a][5]:.4f} = {pair_prob:.6f}")
    print(f"  Total protecting mass: {protecting_mass:.6f}")
    print(f"  Baseline (5/81): {5/81:.6f}")
    print(f"  Ratio: {protecting_mass / (5/81):.3f}")

    # Export for GPT
    print("\n" + "=" * 70)
    print("EXPORT FOR GPT (copy-paste ready)")
    print("=" * 70)

    print("\n# 9x9 Transition Matrix Q[a][b] = P(next=b | current=a)")
    print("# Rows: current digit a (1-9), Columns: next digit b (1-9)")
    print("Q = {")
    for a in range(1, 10):
        row = [f"{Q[a][b]:.5f}" for b in range(1, 10)]
        print(f"    {a}: [{', '.join(row)}],")
    print("}")

    print("\n# Marginal distribution π[d]")
    print("pi = {")
    for d in range(1, 10):
        print(f"    {d}: {pi[d]:.5f},")
    print("}")

    # Also compute the second eigenvalue for correlation length
    print("\n" + "=" * 70)
    print("HIGH/LOW TRANSITION MATRIX (for correlation length)")
    print("=" * 70)

    # Aggregate to 2x2: low (1-4) vs high (5-9)
    low = [1, 2, 3, 4]
    high = [5, 6, 7, 8, 9]

    # P(high | low), P(low | low), etc.
    low_to_low = sum(matrix[a][b] for a in low for b in low)
    low_to_high = sum(matrix[a][b] for a in low for b in high)
    high_to_low = sum(matrix[a][b] for a in high for b in low)
    high_to_high = sum(matrix[a][b] for a in high for b in high)

    low_total = low_to_low + low_to_high
    high_total = high_to_low + high_to_high

    p_LL = low_to_low / low_total
    p_LH = low_to_high / low_total
    p_HL = high_to_low / high_total
    p_HH = high_to_high / high_total

    print(f"\n  P(L→L) = {p_LL:.4f}    P(L→H) = {p_LH:.4f}")
    print(f"  P(H→L) = {p_HL:.4f}    P(H→H) = {p_HH:.4f}")

    # Second eigenvalue
    lambda2 = p_LL + p_HH - 1  # = 1 - p_LH - p_HL for 2x2 stochastic
    print(f"\n  Second eigenvalue λ₂ = {lambda2:.4f}")
    print(f"  |λ₂| = {abs(lambda2):.4f}")
    print(f"  Correlation length ≈ {-1/abs(lambda2) if lambda2 != 0 else float('inf'):.2f} digits")


if __name__ == "__main__":
    main()
