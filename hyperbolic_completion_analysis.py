#!/usr/bin/env python3
"""
Hyperbolic Completion Analysis for Erdős-Straus Conjecture
==========================================================

Tests the key reformulation from Gemini L4:

Starting from the Type II equation:
    (p + δ)(b + c) = 4δbc,  δ ≡ 3 (mod 4)

Multiply by 4δ and complete the product:
    (4δb - (p+δ))(4δc - (p+δ)) = (p+δ)²

Setting X = 4δb - (p+δ), Y = 4δc - (p+δ):
    XY = (p+δ)²
    b = (X + (p+δ))/(4δ)
    c = (Y + (p+δ))/(4δ)

So the problem reduces to:
    Find δ ≡ 3 (mod 4) and a POSITIVE divisor X of (p+δ)² such that:
    (1) X ≡ -(p+δ) (mod 4δ)           [so 4δ | X + (p+δ), giving integer b]
    (2) (p+δ)²/X ≡ -(p+δ) (mod 4δ)   [so 4δ | Y + (p+δ), giving integer c]

This script:
1. Verifies the reformulation on all 750 certificates
2. Analyzes divisor patterns in (p+δ)²
3. Tests the "reversal argument": for how many δ does a valid divisor exist?
4. Looks for algebraic invariants in the certificate data (L3 neural synthesis idea)
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
    witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for a in witnesses:
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


def divisors(n):
    """Return all positive divisors of n."""
    divs = []
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            divs.append(i)
            if i != n // i:
                divs.append(n // i)
    return sorted(divs)


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


def verify_hyperbolic_completion(witnesses):
    """Verify XY = (p+δ)² for all certificates."""
    print("=" * 70)
    print("SECTION 1: Verify Hyperbolic Completion on All Certificates")
    print("=" * 70)

    all_ok = True
    x_data = []

    for p, delta, b, c in witnesses:
        s = p + delta  # s = p + δ
        X = 4 * delta * b - s
        Y = 4 * delta * c - s

        # Check XY = s²
        if X * Y != s * s:
            print(f"  FAIL: p={p}, δ={delta}, b={b}, c={c}: XY={X*Y} != s²={s*s}")
            all_ok = False
            continue

        # Check X > 0 and Y > 0
        if X <= 0 or Y <= 0:
            print(f"  WARN: p={p}, δ={delta}: X={X}, Y={Y} (non-positive)")

        # Check divisibility
        if (X + s) % (4 * delta) != 0:
            print(f"  FAIL: 4δ does not divide X+s for p={p}")
            all_ok = False
        if (Y + s) % (4 * delta) != 0:
            print(f"  FAIL: 4δ does not divide Y+s for p={p}")
            all_ok = False

        # Record data
        x_data.append({
            'p': p, 'delta': delta, 'b': b, 'c': c,
            's': s, 'X': X, 'Y': Y,
            'X_over_s': X / s if s != 0 else None,
            'gcd_X_s': gcd(X, s),
        })

    if all_ok:
        print(f"  ALL {len(witnesses)} certificates verify XY = (p+δ)²  ✓")
    else:
        print("  SOME FAILURES")

    return x_data


def analyze_divisor_structure(x_data):
    """Analyze patterns in how X relates to (p+δ)²."""
    print()
    print("=" * 70)
    print("SECTION 2: Divisor Structure Analysis")
    print("=" * 70)

    # How does X relate to s = p+δ?
    # Since XY = s², X is always a divisor of s²
    # X = s²/Y, and we need X ≡ -s mod 4δ

    # Classify: is X a divisor of s itself, or only of s²?
    divides_s_count = 0
    only_s2_count = 0
    x_eq_s_count = 0

    gcd_distribution = Counter()
    x_mod_s = Counter()

    for d in x_data:
        X, s = d['X'], d['s']
        g = gcd(X, s)
        gcd_distribution[g == s] += 1

        if s % X == 0:
            divides_s_count += 1
        elif (s * s) % X == 0:
            only_s2_count += 1

        if X == s:
            x_eq_s_count += 1

        # What is X mod s?
        x_mod_s[X % s] += 1

    print(f"  X divides s (not just s²): {divides_s_count}/{len(x_data)}")
    print(f"  X = s (trivial case b=c):  {x_eq_s_count}/{len(x_data)}")
    print(f"  X divides only s²:         {only_s2_count}/{len(x_data)}")

    # Analyze the ratio X/s
    print()
    print("  X/s ratio distribution (first 20):")
    ratios = [(d['X'] / d['s'], d['p']) for d in x_data[:20]]
    for ratio, p in ratios:
        print(f"    p={p:>7d}: X/s = {ratio:.6f}")

    # What fraction of s² divisors satisfy the congruence?
    print()
    print("  Congruence hit rate (sample of first 20 primes):")
    for d in x_data[:20]:
        p, delta, s = d['p'], d['delta'], d['s']
        s2 = s * s
        divs = divisors(s2)
        hits = [dv for dv in divs if (dv + s) % (4 * delta) == 0
                and (s2 // dv + s) % (4 * delta) == 0]
        print(f"    p={p:>7d}, δ={delta:>4d}, s={s:>7d}: "
              f"{len(divs):>5d} divisors of s², {len(hits):>3d} valid "
              f"({100*len(hits)/len(divs):.1f}%)")


def reversal_analysis(witnesses, max_p=10000):
    """Test the reversal argument: how many δ ≡ 3 mod 4 work for each prime?

    If ESC fails for some p, then for ALL δ ≡ 3 mod 4, (p+δ)² has NO divisor
    in the required residue class. The reversal argument says this is
    impossible by divisor equidistribution.
    """
    print()
    print("=" * 70)
    print("SECTION 3: Reversal Argument - Valid δ Count per Prime")
    print("=" * 70)

    # Get sorry-region primes up to max_p
    sorry_primes = [d['p'] for d in [{'p': p} for p, _, _, _ in witnesses] if d['p'] <= max_p]
    if not sorry_primes:
        # Generate some sorry-region primes
        sorry_primes = [p for p, delta, b, c in witnesses if p <= max_p]

    if not sorry_primes:
        print("  No primes in range. Generating from scratch...")
        sorry_primes = [p for p in range(1000, max_p, 2) if is_prime(p)
                        and p % 24 == 1 and p % 7 in {1, 2, 4}
                        and p % 5 in {1, 4}][:30]

    print(f"  Testing {len(sorry_primes)} primes up to {max_p}")
    print()

    delta_limit = 200  # Test δ from 3 to this limit

    for p in sorry_primes[:15]:
        valid_deltas = []
        total_tested = 0

        for delta in range(3, delta_limit + 1, 4):  # δ ≡ 3 mod 4
            total_tested += 1
            s = p + delta
            s2 = s * s

            # Check if any divisor of s² satisfies both congruences
            found = False
            for dv in divisors(s2):
                if (dv + s) % (4 * delta) == 0:
                    quot = s2 // dv
                    if (quot + s) % (4 * delta) == 0:
                        b_val = (dv + s) // (4 * delta)
                        c_val = (quot + s) // (4 * delta)
                        if b_val > 0 and c_val > 0:
                            valid_deltas.append((delta, b_val, c_val))
                            found = True
                            break

        print(f"  p={p:>7d}: {len(valid_deltas):>3d}/{total_tested} deltas work "
              f"({100*len(valid_deltas)/total_tested:.1f}%) "
              f"- first δ={valid_deltas[0][0] if valid_deltas else 'NONE'}")


def congruence_class_analysis(x_data):
    """Analyze what residue class the valid divisor X falls in mod 4δ.

    The key question: X ≡ -(p+δ) ≡ -s mod 4δ.
    Since s = p + δ, we have -s mod 4δ = 4δ - s mod 4δ = 3δ - p mod 4δ.
    """
    print()
    print("=" * 70)
    print("SECTION 4: Residue Class Analysis")
    print("=" * 70)

    print("  Checking X ≡ -s (mod 4δ) for all certificates:")
    target_residues = []

    for d in x_data[:30]:
        p, delta, X, s = d['p'], d['delta'], d['X'], d['s']
        mod_4d = 4 * delta
        target = (-s) % mod_4d
        actual = X % mod_4d

        match = "✓" if actual == target else "✗"
        target_residues.append(target)

        if d == x_data[0] or actual != target:
            print(f"    p={p:>7d}, δ={delta:>4d}: X≡{actual} mod {mod_4d}, "
                  f"target={target} {match}")

    # Simplify the target residue
    print()
    print("  Target residue -s mod 4δ = -(p+δ) mod 4δ:")
    print("  Since δ ≡ 3 mod 4, let δ = 4k+3:")
    print("    -s mod 4δ = -(p + 4k+3) mod 4(4k+3)")
    print("    = 4(4k+3) - p - 4k - 3 mod 4(4k+3)")
    print("    = 16k + 12 - p - 4k - 3 mod 4(4k+3)")
    print("    = 12k + 9 - p mod 4(4k+3)")
    print("    = 3(4k+3) - p mod 4δ")
    print("    = 3δ - p mod 4δ")

    # Verify this simplification
    all_match = True
    for d in x_data:
        p, delta, X = d['p'], d['delta'], d['X']
        target1 = (-d['s']) % (4 * delta)
        target2 = (3 * delta - p) % (4 * delta)
        if target1 != target2:
            print(f"    MISMATCH at p={p}: {target1} vs {target2}")
            all_match = False
    if all_match:
        print(f"  Verified: -s ≡ 3δ - p (mod 4δ) for all {len(x_data)} certs  ✓")


def algebraic_invariant_search(x_data):
    """L3 Neural Invariant Synthesis idea:
    Search certificate data for algebraic relationships.

    Look for patterns like:
    - Is b always related to p mod something?
    - Does X factor in a predictable way?
    - Are there common factors between X and p, δ, s?
    """
    print()
    print("=" * 70)
    print("SECTION 5: Algebraic Invariant Search (L3 Neural Synthesis)")
    print("=" * 70)

    # Pattern 1: b values
    b_values = Counter()
    for d in x_data:
        b_values[d['b']] += 1

    print("  Most common b values:")
    for b, count in b_values.most_common(10):
        print(f"    b={b:>6d}: appears {count} times ({100*count/len(x_data):.1f}%)")

    # Pattern 2: gcd(X, s) - is X always coprime to s?
    print()
    gcd_vals = Counter()
    for d in x_data:
        g = gcd(d['X'], d['s'])
        gcd_vals[g > 1] += 1

    print(f"  gcd(X, s) > 1: {gcd_vals[True]}/{len(x_data)}")
    print(f"  gcd(X, s) = 1: {gcd_vals[False]}/{len(x_data)}")

    # Pattern 3: Is s = p + δ always squarefree? (Relates to divisor count)
    print()
    squarefree_count = 0
    for d in x_data[:100]:
        s = d['s']
        is_sqfree = True
        for pr in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
            if s % (pr * pr) == 0:
                is_sqfree = False
                break
        if is_sqfree:
            squarefree_count += 1
    print(f"  s = p+δ squarefree (first 100): {squarefree_count}/100")

    # Pattern 4: What is A = (p + δ)/4 for each certificate?
    # From Bridge.lean: δ = 4A - p, so A = (p + δ)/4
    print()
    print("  A = (p+δ)/4 analysis:")
    a_prime_count = 0
    for d in x_data[:50]:
        s = d['s']
        if s % 4 != 0:
            print(f"    WARNING: s = {s} not divisible by 4 (p={d['p']}, δ={d['delta']})")
            continue
        A = s // 4
        a_is_prime = is_prime(A)
        if a_is_prime:
            a_prime_count += 1

    print(f"  A is prime (first 50): {a_prime_count}/50")

    # Pattern 5: Relationship between δ and p
    print()
    print("  δ/p ratio (first 20):")
    for d in x_data[:20]:
        ratio = d['delta'] / d['p']
        print(f"    p={d['p']:>7d}, δ={d['delta']:>4d}: δ/p = {ratio:.6f}, "
              f"δ mod p = {d['delta'] % d['p']}")

    # Pattern 6: b*c product and its relation to s
    print()
    print("  b*c vs s relationship (first 20):")
    for d in x_data[:20]:
        bc = d['b'] * d['c']
        s = d['s']
        print(f"    p={d['p']:>7d}: b*c={bc:>10d}, s={s:>7d}, "
              f"b*c/s={bc/s:.2f}, b*c mod s={bc % s}")


def subgroup_confinement_test(witnesses, max_p=5000):
    """L4 Section 3: Test whether the target residue class -(p+δ) mod 4δ
    falls in a multiplicative subgroup that divisors of (p+δ)² avoid.

    For (p+δ)² to have a divisor X ≡ -(p+δ) mod 4δ, we need the
    image of divisors in (Z/4δZ)* to hit -s mod 4δ.

    If s = p+δ has a specific factorization pattern, the divisors of s²
    might be confined to a subgroup of (Z/4δZ)*.
    """
    print()
    print("=" * 70)
    print("SECTION 6: Subgroup Confinement Test (L4 Section 3)")
    print("=" * 70)

    for p, delta, b, c in witnesses[:10]:
        s = p + delta
        s2 = s * s
        mod_4d = 4 * delta
        target = (-s) % mod_4d

        divs = divisors(s2)
        # Get residues of divisors mod 4δ
        residues = set()
        for dv in divs:
            if gcd(dv, mod_4d) == 1:  # Only coprime residues
                residues.add(dv % mod_4d)

        # What fraction of (Z/4δZ)* do the divisors hit?
        # Euler's totient
        units = set()
        for i in range(mod_4d):
            if gcd(i, mod_4d) == 1:
                units.add(i)

        hit_rate = len(residues) / len(units) if units else 0
        target_hit = target in residues

        print(f"  p={p:>7d}, δ={delta:>4d}: s²={s2}, {len(divs)} divisors, "
              f"{len(residues)}/{len(units)} residue classes hit ({hit_rate:.1%}), "
              f"target {target} {'HIT ✓' if target_hit else 'MISS ✗'}")


def main():
    csvfile = "/Users/kvallie2/Desktop/esc_stage8/witnesses_1000000.csv"
    print("Hyperbolic Completion Analysis for ESC")
    print("=" * 70)
    print(f"Reading witnesses from {csvfile}...")

    witnesses = read_witnesses(csvfile)
    print(f"Loaded {len(witnesses)} certificates")
    print()

    # Section 1: Verify the reformulation
    x_data = verify_hyperbolic_completion(witnesses)

    # Section 2: Divisor structure
    analyze_divisor_structure(x_data)

    # Section 3: Reversal argument
    reversal_analysis(witnesses, max_p=10000)

    # Section 4: Residue class analysis
    congruence_class_analysis(x_data)

    # Section 5: Algebraic invariant search
    algebraic_invariant_search(x_data)

    # Section 6: Subgroup confinement
    subgroup_confinement_test(witnesses)

    print()
    print("=" * 70)
    print("ANALYSIS COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    main()
