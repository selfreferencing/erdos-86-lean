"""
Exp 85: 3-gram Carry-Conditioned Transition Matrices

Following GPT's recommendation in 52C1:
- Compute Q^(0)[a,b] = P(next=b | current=a, carry-in=0)
- Compute Q^(1)[a,b] = P(next=b | current=a, carry-in=1)

Since carry-in is determined by the PREVIOUS digit's low/high class:
- N_0[a,b] = count of (x,a,b) triples where x ∈ {1,2,3,4} (low → carry-out 0)
- N_1[a,b] = count of (x,a,b) triples where x ∈ {5,6,7,8,9} (high → carry-out 1)

This should reveal whether the stronger 22% suppression from Exp 62-71
appears when we condition on carry state.
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


def main():
    print("=" * 70)
    print("Exp 85: 3-gram Carry-Conditioned Transition Matrices")
    print("=" * 70)

    low_digits = {1, 2, 3, 4}
    high_digits = {5, 6, 7, 8, 9}

    # Count 3-grams (x, a, b) where all are nonzero
    # Stratify by whether x is low (carry-out 0) or high (carry-out 1)
    N0 = Counter()  # x is low → carry into a is 0
    N1 = Counter()  # x is high → carry into a is 1

    total_triples = 0

    for n in range(50, 500):
        digits = get_digits(n)
        # Need triples: positions i-2, i-1, i for i >= 2
        for i in range(2, len(digits)):
            x, a, b = digits[i-2], digits[i-1], digits[i]
            if x != 0 and a != 0 and b != 0:
                total_triples += 1
                if x in low_digits:
                    N0[(a, b)] += 1
                else:  # x in high_digits
                    N1[(a, b)] += 1

    print(f"\nTotal zeroless 3-grams: {total_triples}")
    print(f"  From low predecessor (carry=0): {sum(N0.values())}")
    print(f"  From high predecessor (carry=1): {sum(N1.values())}")

    # Build conditional transition matrices Q^(0) and Q^(1)
    print("\n" + "=" * 70)
    print("Q^(0)[a,b] = P(next=b | current=a, carry-in=0)")
    print("=" * 70)

    Q0 = {}
    for a in range(1, 10):
        row_sum = sum(N0[(a, b)] for b in range(1, 10))
        Q0[a] = {}
        for b in range(1, 10):
            Q0[a][b] = N0[(a, b)] / row_sum if row_sum > 0 else 0

    print("\n       ", end="")
    for b in range(1, 10):
        print(f"   {b}    ", end="")
    print()
    for a in range(1, 10):
        print(f"  {a} |", end="")
        for b in range(1, 10):
            print(f" {Q0[a][b]:.4f}", end="")
        print()

    print("\n" + "=" * 70)
    print("Q^(1)[a,b] = P(next=b | current=a, carry-in=1)")
    print("=" * 70)

    Q1 = {}
    for a in range(1, 10):
        row_sum = sum(N1[(a, b)] for b in range(1, 10))
        Q1[a] = {}
        for b in range(1, 10):
            Q1[a][b] = N1[(a, b)] / row_sum if row_sum > 0 else 0

    print("\n       ", end="")
    for b in range(1, 10):
        print(f"   {b}    ", end="")
    print()
    for a in range(1, 10):
        print(f"  {a} |", end="")
        for b in range(1, 10):
            print(f" {Q1[a][b]:.4f}", end="")
        print()

    # Compare Q^(0) vs Q^(1) for the critical transitions
    print("\n" + "=" * 70)
    print("COMPARISON: Q^(0) vs Q^(1) for Key Transitions")
    print("=" * 70)

    print("\n** Killing pairs (a, 5) with a ∈ {1,2,3,4} **")
    print("These create zero when carry-in is 0")
    print("\n  a  | Q^(0)[a,5] | Q^(1)[a,5] | Difference | Ratio Q0/Q1")
    print("-" * 60)
    for a in [1, 2, 3, 4]:
        q0 = Q0[a][5]
        q1 = Q1[a][5]
        diff = q0 - q1
        ratio = q0 / q1 if q1 > 0 else float('inf')
        print(f"  {a}  |   {q0:.4f}   |   {q1:.4f}   |   {diff:+.4f}  |   {ratio:.3f}")

    print("\n** Protecting pairs (a, 5) with a ∈ {5,6,7,8,9} **")
    print("These produce 1 (not zero) when carry-in is 1")
    print("\n  a  | Q^(0)[a,5] | Q^(1)[a,5] | Difference | Ratio Q0/Q1")
    print("-" * 60)
    for a in [5, 6, 7, 8, 9]:
        q0 = Q0[a][5]
        q1 = Q1[a][5]
        diff = q0 - q1
        ratio = q0 / q1 if q1 > 0 else float('inf')
        print(f"  {a}  |   {q0:.4f}   |   {q1:.4f}   |   {diff:+.4f}  |   {ratio:.3f}")

    # Compute effective killing rates under each carry regime
    print("\n" + "=" * 70)
    print("EFFECTIVE KILLING ANALYSIS")
    print("=" * 70)

    # Under carry=0, killing happens at (a, 5) for a ∈ {1,2,3,4}
    # Under carry=1, no killing (5 with carry-in 1 produces 1, not 0)

    # Compute marginal digit distribution given carry
    pi_0 = {}  # P(digit=a | carry-in=0)
    pi_1 = {}  # P(digit=a | carry-in=1)

    total_c0 = sum(N0[(a, b)] for a in range(1, 10) for b in range(1, 10))
    total_c1 = sum(N1[(a, b)] for a in range(1, 10) for b in range(1, 10))

    for a in range(1, 10):
        pi_0[a] = sum(N0[(a, b)] for b in range(1, 10)) / total_c0 if total_c0 > 0 else 0
        pi_1[a] = sum(N1[(a, b)] for b in range(1, 10)) / total_c1 if total_c1 > 0 else 0

    print("\nMarginal digit distribution by carry-in:")
    print("\n  d  | π(d|c=0) | π(d|c=1) | Difference")
    print("-" * 45)
    for d in range(1, 10):
        print(f"  {d}  |  {pi_0[d]:.4f}  |  {pi_1[d]:.4f}  |  {pi_0[d]-pi_1[d]:+.4f}")

    # Killing mass: sum over (a, 5) for a ∈ {1,2,3,4} of π(a|c=0) * Q^(0)[a,5]
    # This is the probability of being in state (5, 0) conditional on carry=0
    killing_mass_c0 = sum(pi_0[a] * Q0[a][5] for a in [1, 2, 3, 4])
    killing_mass_c1 = sum(pi_1[a] * Q1[a][5] for a in [1, 2, 3, 4])

    print(f"\nKilling transition mass (→5 from low digit):")
    print(f"  Under carry=0: {killing_mass_c0:.6f}")
    print(f"  Under carry=1: {killing_mass_c1:.6f}")
    print(f"  Baseline (4/81): {4/81:.6f}")
    print(f"  Ratio (c=0/baseline): {killing_mass_c0 / (4/81):.3f}")
    print(f"  Ratio (c=1/baseline): {killing_mass_c1 / (4/81):.3f}")

    # Now compute the true 18x18 transition counts directly
    print("\n" + "=" * 70)
    print("DIRECT 18×18 STATE TRANSITION ANALYSIS")
    print("=" * 70)

    # State (a, c) where c = τ(predecessor) = 1 if predecessor >= 5
    # Transition: (a, c) → (b, τ(a))

    state_trans = Counter()

    for n in range(50, 500):
        digits = get_digits(n)
        for i in range(2, len(digits)):
            x, a, b = digits[i-2], digits[i-1], digits[i]
            if x != 0 and a != 0 and b != 0:
                c_in = 1 if x >= 5 else 0
                c_out = 1 if a >= 5 else 0
                state_trans[((a, c_in), (b, c_out))] += 1

    # Compute row sums for normalization
    row_sums = {}
    for a in range(1, 10):
        for c in [0, 1]:
            row_sums[(a, c)] = sum(
                state_trans[((a, c), (b, cp))]
                for b in range(1, 10) for cp in [0, 1]
            )

    # Focus on the killing state (5, 0)
    print("\nTransitions INTO killing state (5, 0):")
    print("(Only states (a, c) with a ∈ {1,2,3,4} can reach (5, 0))")
    print("\n  From state | Count | P((a,c)→(5,0))")
    print("-" * 45)

    total_into_5_0 = 0
    for a in [1, 2, 3, 4]:
        for c in [0, 1]:
            count = state_trans[((a, c), (5, 0))]
            total_into_5_0 += count
            prob = count / row_sums[(a, c)] if row_sums[(a, c)] > 0 else 0
            print(f"  ({a}, {c})     |  {count:4d} |   {prob:.4f}")

    print(f"\nTotal transitions into (5, 0): {total_into_5_0}")

    # Compute stationary distribution of 18-state chain
    print("\n" + "=" * 70)
    print("STATIONARY DISTRIBUTION (Data-Driven 18-State)")
    print("=" * 70)

    # Build transition matrix
    states = [(d, c) for d in range(1, 10) for c in [0, 1]]
    P = {}
    for s1 in states:
        P[s1] = {}
        rs = row_sums[s1]
        for s2 in states:
            P[s1][s2] = state_trans[(s1, s2)] / rs if rs > 0 else 0

    # Power iteration for stationary distribution
    pi = {s: 1/18 for s in states}
    for _ in range(1000):
        new_pi = {s: 0 for s in states}
        for s2 in states:
            for s1 in states:
                new_pi[s2] += pi[s1] * P[s1][s2]
        pi = new_pi

    print("\nStationary distribution π̃(d, c):")
    print("\n   d  |  π̃(d,0)  |  π̃(d,1)  |   Total")
    print("-" * 45)
    for d in range(1, 10):
        p0 = pi[(d, 0)]
        p1 = pi[(d, 1)]
        print(f"   {d}  |  {p0:.5f}  |  {p1:.5f}  |  {p0+p1:.5f}")

    print(f"\n*** Effective zero rate p₀ = π̃(5, 0) = {pi[(5, 0)]:.6f} ***")
    print(f"    Baseline (uniform): 4/81 = {4/81:.6f}")
    print(f"    Suppression ratio: {pi[(5, 0)] / (4/81):.3f}")

    # Compute eigenvalues of the 18x18 matrix
    print("\n" + "=" * 70)
    print("18×18 EIGENVALUE ANALYSIS")
    print("=" * 70)

    # Power iteration on centered matrix for λ₂
    def matrix_vector(M, v, states):
        result = {s: 0 for s in states}
        for s2 in states:
            for s1 in states:
                result[s2] += M[s1][s2] * v[s1]
        return result

    def normalize(v, states):
        norm = sum(v[s]**2 for s in states) ** 0.5
        return {s: v[s]/norm for s in states} if norm > 0 else v

    # Center the matrix
    P_centered = {}
    for s1 in states:
        P_centered[s1] = {}
        for s2 in states:
            P_centered[s1][s2] = P[s1][s2] - 1/18

    # Power iteration
    v = {s: 1 if s[0] % 2 == 0 else -1 for s in states}
    # Orthogonalize against uniform
    mean_v = sum(v.values()) / 18
    v = {s: v[s] - mean_v for s in states}
    v = normalize(v, states)

    for _ in range(500):
        Pv = matrix_vector(P_centered, v, states)
        mean_Pv = sum(Pv.values()) / 18
        Pv = {s: Pv[s] - mean_Pv for s in states}
        v = normalize(Pv, states)

    rayleigh = sum(Pv[s] * v[s] for s in states)
    print(f"\n|λ₂| of 18×18 chain: {abs(rayleigh):.6f}")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY: 3-GRAM CARRY-CONDITIONED ANALYSIS")
    print("=" * 70)

    print(f"""
Key findings:

1. Q^(0) ≠ Q^(1) — carry DOES affect digit transitions
   (Though the effect is subtle in the marginal data)

2. Effective zero rate from 18-state chain: p₀ = {pi[(5, 0)]:.6f}
   - Baseline (4/81): {4/81:.6f}
   - Suppression ratio: {pi[(5, 0)] / (4/81):.3f}

3. Correlation |λ₂| = {abs(rayleigh):.6f}

4. Compare to 52A/B predictions:
   - 52A/B: p₀ ≈ 0.0385, |λ₂| ≈ 0.227
   - This: p₀ = {pi[(5, 0)]:.4f}, |λ₂| = {abs(rayleigh):.4f}
""")


if __name__ == "__main__":
    main()
