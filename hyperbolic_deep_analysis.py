#!/usr/bin/env python3
"""
Deep Follow-up Analysis on Hyperbolic Completion
=================================================

Key findings from the first pass that need deeper investigation:

1. gcd(X, s) > 1 for ALL 750 certs -- X always shares a factor with s = p+δ
2. s = p+δ is NEVER squarefree -- the winning δ always makes p+δ composite with a square factor
3. b*c/s is often a "nice" ratio (0.25, 1.00, 1.25, 2.00, 4.00, 5.00, ...)
4. Section 6 showed coprime divisors MISS the target -- valid X shares factors with 4δ
5. b values cluster at small numbers (10, 8, 12 account for 63%)

This suggests the actual mechanism is:
    X = (some factor of s) * (something structured)
and the solution exists because s = p+δ can be chosen to have rich factorization.
"""

import csv
import math
from collections import defaultdict, Counter
from math import gcd


def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    if n < 9:
        return True
    if n % 3 == 0:
        return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def factorize(n):
    """Return prime factorization as dict {prime: exponent}."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def read_witnesses(csvfile):
    witnesses = []
    with open(csvfile) as f:
        reader = csv.DictReader(f)
        for row in reader:
            witnesses.append((
                int(row['p']),
                int(row['offset']),
                int(row['b']),
                int(row['c'])
            ))
    return witnesses


def deep_gcd_analysis(witnesses):
    """Why is gcd(X, s) always > 1?

    X = 4δb - s, s = p + δ.
    gcd(X, s) = gcd(4δb - s, s) = gcd(4δb, s) since gcd(a-s, s) = gcd(a, s).
    So gcd(X, s) = gcd(4δb, p+δ).

    For this to be > 1, we need some prime q | gcd(4δb, p+δ).
    Since p is prime:
      - q | 4: then 2 | (p+δ). Since p is odd (sorry-region p ≡ 1 mod 24),
        we need δ odd, i.e., δ ≡ 3 mod 4, so δ is odd. p odd + δ odd = even!
        So 2 | (p+δ) ALWAYS. And 2 | 4δb. So gcd ≥ 2 always.

    But s = p+δ is always even (p odd, δ odd), so s/2 is always an integer.
    Is gcd(X, s) always ≥ 4? Let's check.
    """
    print("=" * 70)
    print("DEEP ANALYSIS 1: Why gcd(X, s) > 1 always")
    print("=" * 70)
    print()
    print("  Key identity: gcd(X, s) = gcd(4δb, p+δ)")
    print("  Since p ≡ 1 mod 24 (odd) and δ ≡ 3 mod 4 (odd):")
    print("  s = p + δ is ALWAYS EVEN, and 2 | 4δb, so gcd ≥ 2 trivially.")
    print()

    gcd_values = Counter()
    gcd_over_2 = Counter()
    s_div_4 = Counter()

    for p, delta, b, c in witnesses:
        s = p + delta
        X = 4 * delta * b - s
        g = gcd(X, s)
        gcd_values[g] += 1
        gcd_over_2[g // 2] += 1

        # Is s ≡ 0 mod 4?
        s_div_4[s % 4 == 0] += 1

    print(f"  s ≡ 0 mod 4: {s_div_4[True]}/{len(witnesses)}")
    print(f"  s ≡ 2 mod 4: {s_div_4[False]}/{len(witnesses)}")
    print()

    # Actually s = p + δ. p ≡ 1 mod 24, δ ≡ 3 mod 4.
    # s mod 4 = (1 + 3) mod 4 = 0. So s ≡ 0 mod 4 ALWAYS!
    print("  Theoretical: p ≡ 1 mod 4, δ ≡ 3 mod 4 => s ≡ 0 mod 4 always")
    print("  So s/4 = A is always an integer (this is the A from Bridge.lean)")
    print()

    # Check: what is gcd(X, s) / 4?
    gcd_div_4 = Counter()
    for p, delta, b, c in witnesses:
        s = p + delta
        X = 4 * delta * b - s
        g = gcd(X, s)
        gcd_div_4[g % 4 == 0] += 1

    print(f"  gcd(X, s) divisible by 4: {gcd_div_4[True]}/{len(witnesses)}")
    print()

    # What is the actual distribution of gcd(X, s)?
    print("  Distribution of gcd(X, s) (top 15):")
    for g, count in sorted(gcd_values.items(), key=lambda x: -x[1])[:15]:
        print(f"    gcd={g:>8d}: {count} times")


def factorization_pattern(witnesses):
    """Analyze the factorization of s = p + δ and how X relates to it."""
    print()
    print("=" * 70)
    print("DEEP ANALYSIS 2: Factorization of s = p + δ")
    print("=" * 70)

    print()
    print("  s = p + δ factorizations and X as product of s's prime factors:")
    print()

    # For each cert, factor s and express X in terms of s's factors
    x_is_power_of_s_primes = 0
    x_divides_s = 0

    for p, delta, b, c in witnesses[:30]:
        s = p + delta
        X = 4 * delta * b - s
        Y = 4 * delta * c - s

        s_factors = factorize(s)
        x_factors = factorize(X) if X > 0 else {}
        y_factors = factorize(Y) if Y > 0 else {}

        # Check if X's prime factors are a subset of s's
        x_primes = set(x_factors.keys())
        s_primes = set(s_factors.keys())
        x_subset = x_primes.issubset(s_primes)

        if x_subset:
            x_is_power_of_s_primes += 1
        if s % X == 0 and X > 0:
            x_divides_s += 1

        s_str = " * ".join(f"{p_}^{e}" if e > 1 else str(p_)
                          for p_, e in sorted(s_factors.items()))
        x_str = " * ".join(f"{p_}^{e}" if e > 1 else str(p_)
                          for p_, e in sorted(x_factors.items())) if x_factors else "?"

        print(f"  p={p:>7d}: s={s:>8d} = {s_str}")
        print(f"           X={X:>8d} = {x_str}  "
              f"{'⊆s_primes ✓' if x_subset else '⊄s_primes ✗'}  "
              f"{'X|s ✓' if s % X == 0 and X > 0 else ''}")
        print()

    # Count globally
    subset_count = 0
    for p, delta, b, c in witnesses:
        s = p + delta
        X = 4 * delta * b - s
        if X <= 0:
            continue
        x_primes = set(factorize(X).keys())
        s_primes = set(factorize(s).keys())
        if x_primes.issubset(s_primes):
            subset_count += 1

    print(f"  X's prime factors ⊆ s's prime factors: {subset_count}/{len(witnesses)}")
    print("  (This is automatic since X | s² and s² has the same prime factors as s)")


def bc_ratio_analysis(witnesses):
    """Analyze b*c/s ratios more carefully.

    b*c = (X+s)(Y+s) / (4δ)²
        = (XY + s(X+Y) + s²) / (16δ²)
        = (s² + s(X+Y) + s²) / (16δ²)
        = s(2s + X + Y) / (16δ²)

    So b*c/s = (2s + X + Y) / (16δ²)

    Since XY = s², if we set X = s²/t, Y = t for some divisor t:
    X + Y = s²/t + t = (s² + t²)/t

    b*c/s = (2s + (s² + t²)/t) / (16δ²) = (2st + s² + t²) / (16δ²t) = (s + t)² / (16δ²t)

    For b*c/s to be a nice fraction, (s+t)² must be nicely related to 16δ²t.
    """
    print()
    print("=" * 70)
    print("DEEP ANALYSIS 3: b*c/s Ratio Structure")
    print("=" * 70)

    print()
    print("  b*c/s = (s + Y)² / (16δ²Y) where Y is the 'other' divisor")
    print()

    ratio_patterns = Counter()
    for p, delta, b, c in witnesses:
        s = p + delta
        ratio = (b * c) / s
        # Check if ratio is n/4 for small n
        ratio_times_4 = round(ratio * 4)
        if abs(ratio * 4 - ratio_times_4) < 0.001:
            ratio_patterns[f"{ratio_times_4}/4"] += 1
        else:
            ratio_patterns["other"] += 1

    print("  b*c/s as multiples of 1/4 (top 15):")
    for pat, count in sorted(ratio_patterns.items(), key=lambda x: -x[1])[:15]:
        print(f"    {pat:>10s}: {count} times")

    # Check if b*c*4/s is always a perfect square times something
    print()
    print("  Checking if 4*b*c/s = ((s + Y)/(4δ√Y))² ...")
    print("  Actually: 4bc/s = (2s + X + Y)/(4δ²)")
    print()

    # A = s/4, so 4δ² = 4δ², and s = 4A.
    # 4bc/s = (2s + X + Y)/(4δ²) = (8A + X + Y)/(4δ²)
    # From the ED2 identity: A*(4bc - b - c) = p*bc
    # So 4bc - b - c = p*bc/A. And b + c = (X + Y + 2s)/(4δ) = (X + Y + 8A)/(4δ)
    # 4bc = 4bc/s * s = ... this is getting circular.

    # Just print the actual values of 4bc/s for a sample
    print("  4*b*c/s values (first 20):")
    for p, delta, b, c in witnesses[:20]:
        s = p + delta
        val = 4 * b * c / s
        val_exact = 4 * b * c * 1.0 / s
        is_int = (4 * b * c) % s == 0
        print(f"    p={p:>7d}: 4bc/s = {val_exact:.4f}  {'(integer)' if is_int else ''}")


def small_b_analysis(witnesses):
    """Why are b values so small? b = (X + s)/(4δ).

    Small b means X + s ≈ 4δ*b, so X ≈ 4δb - s.
    If b is small (say b=10), then X = 40δ - s = 40δ - p - δ = 39δ - p.
    For X > 0: δ > p/39.
    For Y = s²/X > 0: automatic since X > 0 and s > 0.

    So with b=10: we need δ ≡ 3 mod 4 with δ > p/39, and
    (39δ - p) | (p+δ)².

    This is a divisibility condition: (39δ - p) | (p+δ)².
    """
    print()
    print("=" * 70)
    print("DEEP ANALYSIS 4: Small b Values and Divisibility Conditions")
    print("=" * 70)

    for b_target in [8, 10, 12]:
        certs_with_b = [(p, delta, b, c) for p, delta, b, c in witnesses if b == b_target]
        print(f"\n  b = {b_target}: {len(certs_with_b)} certificates")

        # For b fixed, X = (4b-1)*δ - p (since X = 4δb - s = 4δb - p - δ = (4b-1)δ - p)
        coeff = 4 * b_target - 1
        print(f"    X = {coeff}δ - p")
        print(f"    Need: ({coeff}δ - p) | (p+δ)²")
        print()

        # For each cert, verify this
        for p, delta, b, c in certs_with_b[:5]:
            s = p + delta
            X = coeff * delta - p
            X_actual = 4 * delta * b - s
            assert X == X_actual, f"Mismatch: {X} vs {X_actual}"
            assert (s * s) % X == 0
            quotient = s * s // X
            Y = quotient

            # What is the relationship between X and s?
            g = gcd(X, s)
            print(f"    p={p:>7d}, δ={delta:>4d}: X={X:>8d}, s²/X={Y:>10d}, "
                  f"gcd(X,s)={g}, X/gcd={X//g}, s/gcd={s//g}")

    # NEW INSIGHT: For fixed b, the problem reduces to finding δ ≡ 3 mod 4
    # such that ((4b-1)δ - p) | (p+δ)².
    # Let's expand: (p+δ)² = p² + 2pδ + δ²
    # And (4b-1)δ - p divides this.
    # Set D = (4b-1)δ - p. Then δ = (D + p)/(4b-1).
    # (p + δ)² = (p + (D+p)/(4b-1))² = ((4b-1)p + D + p)²/(4b-1)²
    #          = (4bp + D)²/(4b-1)²
    # For D | (4bp + D)²/(4b-1)²:
    # D | (4bp + D)² (since D, (4b-1)² might share factors but let's be generous)
    # D | (4bp)² (since D | (4bp+D) implies D | 4bp, wait no...)
    # Actually: (4bp + D)² = (4bp)² + 2(4bp)D + D²
    # D | (4bp + D)² iff D | (4bp)²
    # So the condition is: D | (4bp)² = 16b²p²

    print()
    print("  KEY INSIGHT: For fixed b, setting D = (4b-1)δ - p:")
    print("  The condition D | (p+δ)² simplifies to D | (4bp)²")
    print("  Proof: (p+δ) = (4bp + D)/(4b-1), so")
    print("  (p+δ)² = (4bp+D)²/(4b-1)²")
    print("  D | (p+δ)² iff (4b-1)²·D | (4bp+D)²")
    print("  Since (4bp+D)² ≡ (4bp)² mod D, this gives D | (4bp)²/(gcd stuff)")
    print()

    # VERIFY this insight: does D | 16b²p² for all certificates?
    print("  Verifying D | (4bp)² = 16b²p² for all certificates:")
    all_divide = True
    fail_count = 0
    for p, delta, b, c in witnesses:
        D = (4 * b - 1) * delta - p
        target = 16 * b * b * p * p
        if target % D != 0:
            all_divide = False
            fail_count += 1
            if fail_count <= 5:
                print(f"    FAIL: p={p}, b={b}, D={D}, 16b²p²={target}, "
                      f"16b²p² mod D = {target % D}")

    if all_divide:
        print(f"    D | 16b²p² for ALL {len(witnesses)} certificates  ✓")
    else:
        print(f"    FAILS: {fail_count}/{len(witnesses)}")

    # If D | 16b²p², then D is a divisor of 16b²p².
    # Since p is prime, divisors of 16b²p² = 2⁴ · b² · p².
    # D = (4b-1)δ - p, and we need δ ≡ 3 mod 4.
    # So δ = (D + p)/(4b-1), and we need (D+p)/(4b-1) to be a positive integer ≡ 3 mod 4.

    # This is a FINITE search: enumerate divisors of 16b²p², filter by congruence.
    print()
    print("  If D | 16b²p², we can enumerate ALL solutions for each (p, b):")
    print("  For each divisor d of 16b²p²:")
    print("    δ = (d + p)/(4b - 1)")
    print("    Check: δ is a positive integer, δ ≡ 3 mod 4")


def divisor_of_16b2p2_verification(witnesses):
    """Verify and explore the D | 16b²p² relationship more carefully."""
    print()
    print("=" * 70)
    print("DEEP ANALYSIS 5: Complete Solution via D | 16b²p²")
    print("=" * 70)

    # For a sample of primes, enumerate ALL (b, δ) solutions
    print()
    print("  For each prime, find ALL solutions via divisor enumeration:")
    print()

    for p, delta_cert, b_cert, c_cert in witnesses[:10]:
        solutions = []

        for b in range(1, 50):  # Try small b values
            coeff = 4 * b - 1
            target = 16 * b * b * p * p

            # Find divisors of target
            for D in range(1, min(target + 1, 100000)):
                if target % D != 0:
                    continue
                # δ = (D + p) / coeff
                if (D + p) % coeff != 0:
                    continue
                delta = (D + p) // coeff
                if delta <= 0:
                    continue
                if delta % 4 != 3:
                    continue

                # Verify the original equation
                s = p + delta
                X = coeff * delta - p  # = D
                assert X == D
                if (s * s) % D != 0:
                    continue
                Y = s * s // D
                if (Y + s) % (4 * delta) != 0:
                    continue
                c = (Y + s) // (4 * delta)
                if c <= 0:
                    continue

                # Verify original Type II equation
                lhs = (p + delta) * (b + c)
                rhs = 4 * delta * b * c
                if lhs == rhs:
                    solutions.append((delta, b, c))

        found_cert = any(d == delta_cert and bb == b_cert for d, bb, _ in solutions)
        print(f"  p={p:>7d}: {len(solutions)} solutions found "
              f"(cert δ={delta_cert},b={b_cert} "
              f"{'found ✓' if found_cert else 'NOT found ✗'})")
        for delta, b, c in solutions[:5]:
            marker = " <-- CERT" if delta == delta_cert and b == b_cert else ""
            print(f"    δ={delta:>5d}, b={b:>4d}, c={c:>8d}{marker}")
        if len(solutions) > 5:
            print(f"    ... and {len(solutions) - 5} more")


def main():
    csvfile = "/Users/kvallie2/Desktop/esc_stage8/witnesses_1000000.csv"
    print("Deep Hyperbolic Completion Analysis")
    print("=" * 70)

    witnesses = read_witnesses(csvfile)
    print(f"Loaded {len(witnesses)} certificates")
    print()

    deep_gcd_analysis(witnesses)
    factorization_pattern(witnesses)
    bc_ratio_analysis(witnesses)
    small_b_analysis(witnesses)
    divisor_of_16b2p2_verification(witnesses)

    print()
    print("=" * 70)
    print("DEEP ANALYSIS COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    main()
