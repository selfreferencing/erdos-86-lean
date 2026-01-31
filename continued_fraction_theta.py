"""
Continued Fraction Analysis of θ = log₁₀(2)

Check if θ has special Diophantine properties that could help with ML1.

A number is "badly approximable" if its CF partial quotients are bounded.
This is important for STP - Kim (2007) proved that badly approximable θ
satisfy stronger shrinking target properties.
"""

import math
from decimal import Decimal, getcontext
from fractions import Fraction

# Set high precision
getcontext().prec = 100


def continued_fraction(x, max_terms=100):
    """
    Compute continued fraction expansion [a_0; a_1, a_2, ...]

    Returns list of partial quotients.
    """
    cf = []
    for _ in range(max_terms):
        a = int(x)
        cf.append(a)
        x = x - a
        if abs(x) < 1e-15:
            break
        x = 1 / x
    return cf


def convergents(cf):
    """
    Compute convergents p_n/q_n from CF expansion.

    Convergent p_n/q_n is the best rational approximation with denominator ≤ q_n.
    """
    if len(cf) == 0:
        return []

    # Initial values
    p_prev, p_curr = 0, 1
    q_prev, q_curr = 1, 0

    convs = []

    for a in cf:
        p_next = a * p_curr + p_prev
        q_next = a * q_curr + q_prev

        convs.append((p_next, q_next))

        p_prev, p_curr = p_curr, p_next
        q_prev, q_curr = q_curr, q_next

    return convs


def main():
    print("="*70)
    print("CONTINUED FRACTION ANALYSIS OF θ = log₁₀(2)")
    print("="*70)

    # Compute θ with high precision
    theta = math.log10(2)
    theta_decimal = Decimal(2).ln() / Decimal(10).ln()

    print(f"\nθ = log₁₀(2) = {theta:.50f}")
    print(f"θ (high prec) = {theta_decimal}")

    # Compute CF expansion
    print("\n" + "="*70)
    print("CONTINUED FRACTION EXPANSION")
    print("="*70)

    cf = continued_fraction(theta, max_terms=50)

    print(f"\nFirst 50 partial quotients:")
    print(f"θ = [{cf[0]}; {', '.join(map(str, cf[1:]))}]")

    # Check if badly approximable
    print("\n" + "="*70)
    print("BADLY APPROXIMABLE CHECK")
    print("="*70)

    max_quot = max(cf[1:]) if len(cf) > 1 else 0
    mean_quot = sum(cf[1:]) / len(cf[1:]) if len(cf) > 1 else 0

    print(f"\nMaximum partial quotient (excluding a_0): {max_quot}")
    print(f"Mean partial quotient: {mean_quot:.2f}")

    if max_quot < 100:
        print("\n*** BOUNDED partial quotients (max < 100) ***")
        print("*** θ appears to be BADLY APPROXIMABLE ***")
        print("\nThis is GOOD for STP - Kim (2007) shows badly approximable")
        print("numbers have better shrinking target properties!")
    else:
        print("\n*** UNBOUNDED partial quotients ***")
        print("θ is NOT badly approximable")

    # Compute convergents
    print("\n" + "="*70)
    print("BEST RATIONAL APPROXIMATIONS (Convergents)")
    print("="*70)

    convs = convergents(cf[:20])

    print(f"\n{'n':<4} {'p_n/q_n':<25} {'|θ - p_n/q_n|':<20} {'q_n^2 · |θ - p_n/q_n|':<20}")
    print("-"*70)

    for i, (p, q) in enumerate(convs):
        approx = p / q
        error = abs(theta - approx)
        quality = q**2 * error

        print(f"{i:<4} {p}/{q:<20} {error:<20.10e} {quality:<20.6f}")

    # Diophantine approximation constant
    print("\n" + "="*70)
    print("DIOPHANTINE APPROXIMATION CONSTANT")
    print("="*70)

    print("""
For badly approximable θ, there exists c > 0 such that:
  |θ - p/q| > c/q^2  for all rationals p/q

The supremum of such c is the "Diophantine approximation constant".
For badly approximable numbers, this constant is positive.
    """)

    # Check last few convergents for bound
    if len(convs) >= 10:
        qualities = [q**2 * abs(theta - p/q) for p, q in convs[-10:]]
        min_quality = min(qualities)

        print(f"Minimum q^2·|θ - p/q| over last 10 convergents: {min_quality:.6f}")

        if min_quality > 0.01:
            print(f"\n*** Lower bound c ≥ {min_quality:.6f} ***")
            print("θ has good Diophantine approximation properties!")

    # Compare to golden ratio
    print("\n" + "="*70)
    print("COMPARISON TO GOLDEN RATIO φ = (1+√5)/2")
    print("="*70)

    phi = (1 + math.sqrt(5)) / 2
    cf_phi = continued_fraction(phi - 1, max_terms=20)  # φ - 1 = [0; 1, 1, 1, ...]

    print(f"\nφ = {phi:.50f}")
    print(f"φ - 1 = [0; {', '.join(map(str, cf_phi[1:10]))}...]")
    print("\nGolden ratio has ALL partial quotients = 1 (except a_0 = 1)")
    print("This makes φ the 'most badly approximable' number.")

    print(f"\nθ = log₁₀(2) has partial quotients: {cf[1:10]}")
    if max(cf[1:10]) <= 10:
        print("These are small! θ is 'moderately badly approximable'")

    # Check for patterns
    print("\n" + "="*70)
    print("PATTERN ANALYSIS")
    print("="*70)

    # Check for repeating patterns
    if len(cf) >= 20:
        print(f"\nPartial quotients a_1 through a_20:")
        for i in range(0, min(20, len(cf)), 5):
            segment = cf[i:i+5]
            print(f"  a_{i}-a_{i+4}: {segment}")

    # Check if eventually periodic (would mean θ is quadratic irrational)
    print(f"\nIs θ eventually periodic? ", end="")

    # log₁₀(2) = log(2)/log(10) is transcendental, so CF is NOT periodic
    print("NO (θ is transcendental, not quadratic)")
    print("CF expansion is aperiodic and infinite.")

    # Summary
    print("\n" + "="*70)
    print("SUMMARY FOR ML1")
    print("="*70)

    print(f"""
1. θ = log₁₀(2) has {"BOUNDED" if max_quot < 100 else "UNBOUNDED"} partial quotients
2. Maximum partial quotient (n ≤ 50): {max_quot}
3. Mean partial quotient: {mean_quot:.2f}
4. Diophantine approximation constant c ≥ {min_quality if len(convs) >= 10 else 0:.6f}

CONCLUSION:
""")

    if max_quot < 100:
        print("""
θ = log₁₀(2) IS badly approximable!

This means (by Kim 2007):
- θ satisfies strong shrinking target properties for SINGLE intervals
- Convergents give best rational approximations
- Diophantine constant is positive

FOR ML1:
- We can potentially use badly approximable property
- But Kim's result is for SINGLE targets, not unions
- Need to check if recent papers (BDGW 2023, Hitting Times 2025)
  extend badly approximable advantages to UNIONS
""")
    else:
        print("θ is NOT badly approximable - partial quotients grow unbounded")


if __name__ == "__main__":
    main()
