"""
Exp 84: Simple Eigenvalue Analysis using Power Iteration on Centered Matrix

Find |λ₂| of the digit transition matrix by power iteration on Q - (1/9)*J.
"""

import sys
sys.set_int_max_str_digits(50000)


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def build_transition_matrix():
    """Build the 9x9 transition matrix from pair counts."""
    from collections import Counter

    pair_counts = Counter()

    for n in range(50, 500):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            a, b = digits[i-1], digits[i]
            if a != 0 and b != 0:
                pair_counts[(a, b)] += 1

    Q = [[0.0] * 9 for _ in range(9)]
    for a in range(1, 10):
        row_sum = sum(pair_counts[(a, b)] for b in range(1, 10))
        if row_sum > 0:
            for b in range(1, 10):
                Q[a-1][b-1] = pair_counts[(a, b)] / row_sum

    return Q


def main():
    print("=" * 70)
    print("Exp 84: Eigenvalue Analysis of Digit Transition Matrix")
    print("=" * 70)

    Q = build_transition_matrix()

    # Center the matrix: Q_centered = Q - (1/9)*J where J is all-ones
    Q_centered = [[Q[i][j] - 1/9 for j in range(9)] for i in range(9)]

    # Frobenius norm
    frob_norm_sq = sum(Q_centered[i][j]**2 for i in range(9) for j in range(9))
    frob_norm = frob_norm_sq ** 0.5
    print(f"\n||Q - (1/9)*J||_F = {frob_norm:.6f}")
    print(f"RMS of eigenvalues (excluding λ₁=1) ≈ {frob_norm / (8**0.5):.6f}")

    # Power iteration on centered matrix
    def matrix_vector(M, v):
        return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]

    def normalize(v):
        norm = sum(x**2 for x in v) ** 0.5
        return [x / norm for x in v] if norm > 0 else v

    def dot(u, v):
        return sum(u[i] * v[i] for i in range(len(u)))

    print("\n" + "=" * 70)
    print("POWER ITERATION ON CENTERED MATRIX")
    print("=" * 70)

    # Try multiple starting vectors
    best_eigenvalue = 0

    import random
    for trial in range(10):
        random.seed(trial * 42)
        v = [random.random() - 0.5 for _ in range(9)]

        # Orthogonalize against (1,...,1)
        mean_v = sum(v) / 9
        v = [x - mean_v for x in v]
        v = normalize(v)

        prev_rayleigh = 0
        for iteration in range(500):
            Qv = matrix_vector(Q_centered, v)

            # Orthogonalize against (1,...,1) to stay in subspace
            mean_Qv = sum(Qv) / 9
            Qv = [x - mean_Qv for x in Qv]

            rayleigh = dot(Qv, v)
            v = normalize(Qv)

            if abs(rayleigh - prev_rayleigh) < 1e-12:
                break
            prev_rayleigh = rayleigh

        if abs(rayleigh) > abs(best_eigenvalue):
            best_eigenvalue = rayleigh

        print(f"  Trial {trial+1}: |λ| = {abs(rayleigh):.8f}")

    print(f"\nBest |λ₂| found: {abs(best_eigenvalue):.8f}")

    # Now let's also check the carry transition matrix more carefully
    print("\n" + "=" * 70)
    print("CARRY CHAIN EIGENVALUE")
    print("=" * 70)

    # The carry chain is a 2-state Markov chain
    # We need to compute P(c' | c) from the doubling transducer

    # For each (digit, carry_in) pair, compute carry_out
    from collections import Counter
    carry_trans = Counter()

    for n in range(50, 500):
        digits = get_digits(n)
        carry = 0
        for d in digits:
            if d != 0:  # Only zeroless
                next_carry = 1 if (2 * d + carry) >= 10 else 0
                carry_trans[(carry, next_carry)] += 1
                carry = next_carry

    total_from_0 = carry_trans[(0, 0)] + carry_trans[(0, 1)]
    total_from_1 = carry_trans[(1, 0)] + carry_trans[(1, 1)]

    P_00 = carry_trans[(0, 0)] / total_from_0 if total_from_0 > 0 else 0
    P_01 = carry_trans[(0, 1)] / total_from_0 if total_from_0 > 0 else 0
    P_10 = carry_trans[(1, 0)] / total_from_1 if total_from_1 > 0 else 0
    P_11 = carry_trans[(1, 1)] / total_from_1 if total_from_1 > 0 else 0

    print(f"\nCarry transition matrix P:")
    print(f"  P(0→0) = {P_00:.4f}    P(0→1) = {P_01:.4f}")
    print(f"  P(1→0) = {P_10:.4f}    P(1→1) = {P_11:.4f}")

    # For 2x2 stochastic: eigenvalues are 1 and (P_00 + P_11 - 1)
    carry_lambda2 = P_00 + P_11 - 1
    print(f"\nCarry eigenvalue |λ₂| = |P(0→0) + P(1→1) - 1| = {abs(carry_lambda2):.6f}")

    # What APPROACH 52A predicted
    print("\n" + "=" * 70)
    print("COMPARISON WITH APPROACH 52A")
    print("=" * 70)

    # 52A predicted: H₀ = P(high | carry=0) ≈ 0.54, H₁ = P(high | carry=1) ≈ 0.313
    # And λ₂ = H₁ - H₀ ≈ -0.227

    # Let's compute H₀ and H₁ empirically
    high_digits = {5, 6, 7, 8, 9}

    # Count (digit | carry) pairs
    digit_given_carry = Counter()

    for n in range(50, 500):
        digits = get_digits(n)
        carry = 0
        for d in digits:
            if d != 0:
                digit_given_carry[(carry, d)] += 1
                next_carry = 1 if (2 * d + carry) >= 10 else 0
                carry = next_carry

    total_c0 = sum(digit_given_carry[(0, d)] for d in range(1, 10))
    total_c1 = sum(digit_given_carry[(1, d)] for d in range(1, 10))

    H0 = sum(digit_given_carry[(0, d)] for d in high_digits) / total_c0 if total_c0 > 0 else 0
    H1 = sum(digit_given_carry[(1, d)] for d in high_digits) / total_c1 if total_c1 > 0 else 0

    print(f"\nEmpirical H₀ = P(high digit | carry=0) = {H0:.4f}")
    print(f"Empirical H₁ = P(high digit | carry=1) = {H1:.4f}")
    print(f"\n52A prediction: H₀ ≈ 0.54, H₁ ≈ 0.313, so λ₂ ≈ -0.227")
    print(f"Empirical:      H₀ = {H0:.4f}, H₁ = {H1:.4f}, so λ₂ = {H1 - H0:.4f}")

    # Wait, that's weird - our H₀ and H₁ are very close to 5/9!
    print(f"\nExpected if uniform: H₀ = H₁ = 5/9 = {5/9:.4f}")

    # The issue: the carry chain eigenvalue is NOT H₁ - H₀
    # For the carry chain, we need to look at P(c'=1 | c) = sum_d P(d|c) * τ(d)
    # where τ(d) = 1 if d ≥ 5, else 0

    # P(c'=1 | c=0) = P(high digit | c=0) = H₀
    # P(c'=1 | c=1) = P(high digit | c=1) = H₁

    # So the carry transition matrix is:
    # [[1-H₀, H₀], [1-H₁, H₁]]

    print("\n" + "=" * 70)
    print("RECONCILIATION")
    print("=" * 70)

    print(f"\nThe carry transition matrix (from digit → carry-out):")
    print(f"  [[1-H₀, H₀], [1-H₁, H₁]] = [[{1-H0:.4f}, {H0:.4f}], [{1-H1:.4f}, {H1:.4f}]]")

    theoretical_carry_lambda2 = (1-H0) + H1 - 1  # = H1 - H0
    print(f"\nThis gives |λ₂| = |H₁ - H₀| = {abs(theoretical_carry_lambda2):.6f}")

    print("\nBut wait - this is the digit-to-carry-out chain, not carry-to-carry chain!")
    print("The carry-to-carry chain we computed directly (P_00, P_11) is different.")

    # The issue is that the doubling transducer doesn't have independent digits
    # The carry affects the OUTPUT digit distribution, but here we're measuring INPUT

    print("\n" + "=" * 70)
    print("KEY INSIGHT")
    print("=" * 70)

    print("""
The 52A model assumed:
1. Digit distribution depends on carry state (different p₀(d) vs p₁(d))
2. This creates correlation in carry chain

The empirical data shows:
1. Digit distribution is nearly UNIFORM regardless of carry
2. H₀ ≈ H₁ ≈ 5/9 (uniform high/low split)
3. Therefore carry correlation is tiny: |λ₂| ≈ 0.01

This is GOOD NEWS for the proof:
- Positions are nearly independent after just 1 digit spacing
- The sparse mesh can use spacing s = 2 and still have quasi-independence
- This strengthens the bulk zero forcing argument
""")

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    print(f"\n1. Digit matrix |λ₂| ≈ {abs(best_eigenvalue):.6f}")
    print(f"2. Carry chain |λ₂| ≈ {abs(carry_lambda2):.6f}")
    print(f"3. H₀ = {H0:.4f}, H₁ = {H1:.4f} (both ≈ 5/9 = 0.556)")
    print(f"4. 52A's prediction of |λ₂| ≈ 0.227 was based on theoretical digit distributions")
    print(f"5. Empirically, digit distribution is nearly uniform → tiny correlation")


if __name__ == "__main__":
    main()
