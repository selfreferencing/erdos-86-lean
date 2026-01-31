"""
Exp 72: The N_m = 0 Transition

Key question: Why does N_m = 0 for all m >= 27?

N_m = #{j in [0, L_m) : 2^{m+j} has zeroless m-digit prefix}

where L_m ≈ 3.32m is the range where the m-digit prefix changes.

This experiment investigates:
1. The exact values of N_m for m = 1..50
2. The transition point where N_m → 0
3. Near-misses: j values that ALMOST work
4. Structural patterns in the failures
"""

from collections import Counter
import math


def get_digits(n):
    """Get digits of 2^n (LSB first, so index 0 = units digit)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def get_m_digit_prefix(n, m):
    """Get the m most significant digits of 2^n."""
    digits = get_digits(n)
    if len(digits) < m:
        return digits[::-1]  # Return all digits if fewer than m
    return digits[-m:][::-1]  # MSB first for prefix


def is_zeroless(digits):
    """Check if digit list is zeroless."""
    return 0 not in digits


def count_zeros_in_prefix(n, m):
    """Count zeros in the m-digit prefix of 2^n."""
    prefix = get_m_digit_prefix(n, m)
    return sum(1 for d in prefix if d == 0)


def main():
    print("=" * 70)
    print("Exp 72: The N_m = 0 Transition")
    print("=" * 70)

    # Part A: Compute N_m for m = 1..50
    print("\n" + "=" * 70)
    print("PART A: N_m Values")
    print("=" * 70)

    print("\nN_m = #{j ∈ [0, L_m) : 2^{m+j} has zeroless m-digit prefix}")
    print()

    log10_2 = math.log10(2)

    print("  m  | L_m | N_m | Density | Witnesses")
    print("-" * 70)

    N_m_values = {}
    witness_j = {}

    for m in range(1, 51):
        # L_m = ceil(m / log10(2)) ≈ 3.32m
        L_m = math.ceil(m / log10_2)

        # Count j in [0, L_m) where m+j gives zeroless m-prefix
        witnesses = []
        for j in range(L_m):
            n = m + j
            prefix = get_m_digit_prefix(n, m)
            if len(prefix) >= m and is_zeroless(prefix):
                witnesses.append(j)

        N_m = len(witnesses)
        N_m_values[m] = N_m
        witness_j[m] = witnesses

        density = N_m / L_m if L_m > 0 else 0

        # Show witnesses for small N_m
        if N_m <= 10:
            witness_str = str(witnesses) if witnesses else "[]"
        else:
            witness_str = f"{witnesses[:5]}... ({N_m} total)"

        print(f" {m:3} | {L_m:3} | {N_m:3} | {density:.3f}   | {witness_str}")

    # Part B: Identify transition point
    print("\n" + "=" * 70)
    print("PART B: Transition Analysis")
    print("=" * 70)

    first_zero = None
    last_nonzero = None
    for m in range(1, 51):
        if N_m_values[m] == 0 and first_zero is None:
            first_zero = m
        if N_m_values[m] > 0:
            last_nonzero = m

    print(f"\nFirst m with N_m = 0: m = {first_zero}")
    print(f"Last m with N_m > 0: m = {last_nonzero}")

    # Check for sporadic non-zero values after first zero
    sporadic = [m for m in range(first_zero, 51) if N_m_values[m] > 0]
    if sporadic:
        print(f"Sporadic N_m > 0 after first zero: {sporadic}")

    # Part C: Near-misses for m >= 27
    print("\n" + "=" * 70)
    print("PART C: Near-Misses for m >= 27")
    print("=" * 70)

    print("\nFor m with N_m = 0, find j values with fewest zeros in prefix:")
    print()

    for m in range(27, 41):
        L_m = math.ceil(m / log10_2)

        best_j = None
        best_zeros = m  # Maximum possible zeros

        zero_counts = Counter()

        for j in range(L_m):
            n = m + j
            num_zeros = count_zeros_in_prefix(n, m)
            zero_counts[num_zeros] += 1
            if num_zeros < best_zeros:
                best_zeros = num_zeros
                best_j = j

        print(f"  m={m}: L_m={L_m}, best_j={best_j} with {best_zeros} zeros")
        print(f"         Zero distribution: {dict(sorted(zero_counts.items()))}")

    # Part D: What's special about m = 27?
    print("\n" + "=" * 70)
    print("PART D: Analysis of m = 26 vs m = 27")
    print("=" * 70)

    for m in [26, 27]:
        L_m = math.ceil(m / log10_2)
        print(f"\n  m = {m}, L_m = {L_m}")

        for j in range(L_m):
            n = m + j
            prefix = get_m_digit_prefix(n, m)
            num_zeros = sum(1 for d in prefix if d == 0)
            zeroless = "ZEROLESS" if num_zeros == 0 else f"{num_zeros} zeros"

            if num_zeros <= 2:  # Show near-misses
                zero_positions = [i for i, d in enumerate(prefix) if d == 0]
                print(f"    j={j:2}, n={n:3}: {zeroless}, zeros at positions {zero_positions}")

    # Part E: The decay of N_m
    print("\n" + "=" * 70)
    print("PART E: Decay Pattern of N_m")
    print("=" * 70)

    print("\nCompare N_m to theoretical predictions:")
    print()
    print("  m  | N_m | L_m*ρ^m | Ratio")
    print("-" * 45)

    rho = 0.9  # (9/10)^m expected zeroless rate per position

    for m in range(1, 31):
        L_m = math.ceil(m / log10_2)
        expected = L_m * (rho ** m)
        N_m = N_m_values[m]
        ratio = N_m / expected if expected > 0.001 else float('inf')
        print(f" {m:3} | {N_m:3} | {expected:7.3f} | {ratio:5.2f}")

    # Part F: The structural impossibility
    print("\n" + "=" * 70)
    print("PART F: Structural Analysis")
    print("=" * 70)

    print("\nFor large m, why does EVERY j in [0, L_m) fail?")
    print()

    # For m = 30, analyze WHERE zeros appear
    m = 30
    L_m = math.ceil(m / log10_2)

    print(f"m = {m}, L_m = {L_m}")
    print("\nPosition distribution of zeros in m-digit prefixes:")

    position_zeros = Counter()
    for j in range(L_m):
        n = m + j
        prefix = get_m_digit_prefix(n, m)
        for i, d in enumerate(prefix):
            if d == 0:
                position_zeros[i] += 1

    print("\n  Position | # times has zero | Fraction")
    print("-" * 45)
    for pos in range(m):
        count = position_zeros[pos]
        frac = count / L_m
        bar = "*" * int(frac * 50)
        print(f"  {pos:8} | {count:16} | {frac:.3f} {bar}")

    # Part G: Conclusion
    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    print(f"""
Key findings:

1. N_m > 0 for m ∈ {{1,...,{last_nonzero}}} with sporadic values: {sporadic if sporadic else 'none'}

2. N_m = 0 for all m >= {first_zero if not sporadic else max(sporadic) + 1}

3. The transition is SHARP: once N_m = 0, it stays 0 (except sporadic)

4. Near-misses: For m >= 27, the best j values have 1-2 zeros
   This is NOT close to zeroless - the constraint is STRONGLY violated

5. The structural reason: As m grows, EVERY j in [0, L_m) produces
   at least one zero in the m-digit prefix. The probability of
   avoiding all m positions having a zero becomes vanishingly small.

For the proof: We need to show that for m >= M_0, no j can satisfy
the zeroless constraint. This is the danger cylinder approach.
""")


if __name__ == "__main__":
    main()
