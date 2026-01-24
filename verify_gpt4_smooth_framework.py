#!/usr/bin/env python3
"""
Verify GPT4's smooth number framework for Type II witnesses.

Key claims to verify:
1. Coprimality: gcd(x_k, m_k) = 1 for all valid k
2. Size constraint removal: if d | x² and d ≡ -x (mod m), then x²/d also ≡ -x (mod m)
3. The "one large prime" framework: d = q^e · t with t | s²
4. Sufficient conditions S1 and S2
"""

from math import gcd, isqrt
from collections import defaultdict

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
M_K = {k: 4*k + 3 for k in K13}

FAILURES = [
    10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
    34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
    46936849, 48991849
]

def factor(n):
    """Return list of (prime, exponent) pairs."""
    factors = []
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            e = 0
            while temp % d == 0:
                e += 1
                temp //= d
            factors.append((d, e))
        d += 1
    if temp > 1:
        factors.append((temp, 1))
    return factors

def x_k(p, k):
    m = M_K[k]
    return (p + m) // 4

def smooth_part(n, B=29):
    """Return (smooth_part, cofactor) where smooth_part is B-smooth."""
    s = 1
    L = n
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]:
        if p > B:
            break
        while L % p == 0:
            s *= p
            L //= p
    return s, L

def divisors_of_square(n):
    """Return all divisors of n²."""
    facts = factor(n)
    # Divisors of n² have exponents 0 to 2*e for each prime p^e
    divs = [1]
    for p, e in facts:
        new_divs = []
        for d in divs:
            power = 1
            for i in range(2*e + 1):
                new_divs.append(d * power)
                power *= p
        divs = new_divs
    return sorted(divs)

def divisor_residue_set(n, m):
    """Return set of residues mod m of divisors of n²."""
    if gcd(n, m) > 1:
        return None  # Not coprime
    divs = divisors_of_square(n)
    return set(d % m for d in divs)

def subgroup_generated(primes, m):
    """Generate multiplicative subgroup of (Z/mZ)* from given primes."""
    H = {1}
    for p in primes:
        if gcd(p, m) > 1:
            continue
        r = p % m
        new = set()
        for h in H:
            power = 1
            for _ in range(m):  # Order divides phi(m) < m
                new.add((h * power) % m)
                power = (power * r) % m
                if power == 1:
                    break
        H.update(new)
    return H

def verify_coprimality():
    """Verify gcd(x_k, m_k) = 1 for all failures and all k in K13."""
    print("=" * 70)
    print("VERIFYING COPRIMALITY: gcd(x_k, m_k) = 1")
    print("=" * 70)

    all_coprime = True
    for p in FAILURES:
        for k in K13:
            xk = x_k(p, k)
            mk = M_K[k]
            g = gcd(xk, mk)
            if g != 1:
                print(f"  FAIL: p={p}, k={k}, gcd({xk}, {mk}) = {g}")
                all_coprime = False

    if all_coprime:
        print("  ✓ All gcd(x_k, m_k) = 1 verified")
    return all_coprime

def verify_size_constraint_removal():
    """Verify: if d ≡ -x (mod m), then x²/d ≡ -x (mod m) too."""
    print("\n" + "=" * 70)
    print("VERIFYING SIZE CONSTRAINT REMOVAL")
    print("=" * 70)

    # Test on a few examples
    test_cases = [(101, 7), (1009, 23), (10007, 47)]

    all_pass = True
    for x, m in test_cases:
        if gcd(x, m) != 1:
            continue
        target = (-x) % m
        x_sq = x * x

        for d in divisors_of_square(x):
            if d > x_sq:
                continue
            d_res = d % m
            if d_res == target:
                d_prime = x_sq // d
                d_prime_res = d_prime % m
                if d_prime_res != target:
                    print(f"  FAIL: x={x}, m={m}, d={d}, d'={d_prime}")
                    print(f"    d ≡ {d_res}, d' ≡ {d_prime_res}, target = {target}")
                    all_pass = False

    if all_pass:
        print("  ✓ Size constraint removal verified on test cases")
        print("  (Both d and x²/d satisfy d ≡ -x when one does)")
    return all_pass

def analyze_one_large_prime_framework():
    """
    For each failure p and each k, analyze the "one large prime" structure.
    x_k = q * s where s is 29-smooth and q > 29 (if exists).
    """
    print("\n" + "=" * 70)
    print("ANALYZING 'ONE LARGE PRIME' FRAMEWORK")
    print("=" * 70)

    for p in FAILURES[:3]:  # Just first 3 for brevity
        print(f"\np = {p}")
        print("-" * 50)

        for k in K13[:5]:  # Just first 5 k values
            xk = x_k(p, k)
            mk = M_K[k]
            s, L = smooth_part(xk, 29)
            facts = factor(xk)
            large_primes = [(q, e) for q, e in facts if q > 29]

            target = (-xk) % mk

            # Check if it's "one large prime to first power"
            is_simple = len(large_primes) == 1 and large_primes[0][1] == 1

            if large_primes:
                q = large_primes[0][0]
                q_inv = pow(q, -1, mk) if gcd(q, mk) == 1 else None

                # The three targets from GPT4's framework
                # e=1: t ≡ -s (mod m)
                # e=2: t ≡ -s * q^{-1} (mod m)
                # e=0: t ≡ -s * q (mod m)

                target_e1 = (-s) % mk
                target_e2 = ((-s) * q_inv) % mk if q_inv else None
                target_e0 = ((-s) * q) % mk

                # Get divisor residue set of s²
                s_div_residues = divisor_residue_set(s, mk) if gcd(s, mk) == 1 else set()

                # Check which targets are hit
                e1_works = target_e1 in s_div_residues
                e2_works = target_e2 in s_div_residues if target_e2 else False
                e0_works = target_e0 in s_div_residues

                witness_exists = e0_works or e1_works or e2_works

                print(f"  k={k}: x={xk}, m={mk}")
                print(f"    s={s} (29-smooth), L={L} (cofactor)")
                print(f"    Large primes: {large_primes}")
                print(f"    Target: {target}, e0={target_e0}, e1={target_e1}, e2={target_e2}")
                print(f"    |Div(s²) mod m| = {len(s_div_residues)}")
                print(f"    e0={e0_works}, e1={e1_works}, e2={e2_works} → witness={witness_exists}")

def classify_bad_patterns():
    """
    For each m_k, classify which 29-smooth s values are "bad"
    (meaning none of -s, -s*q, -s*q^{-1} can be hit by divisors of s²
    for any q not in H(s)).
    """
    print("\n" + "=" * 70)
    print("CLASSIFYING 'BAD PATTERNS' FOR EACH m_k")
    print("=" * 70)

    for k in K13:
        mk = M_K[k]
        G_size = sum(1 for a in range(1, mk) if gcd(a, mk) == 1)  # phi(m_k)

        print(f"\nk={k}, m_k={mk}, |G| = φ({mk}) = {G_size}")

        # For small m_k, enumerate all possible smooth patterns
        # A "pattern" is which small primes divide s
        small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        small_primes = [p for p in small_primes if gcd(p, mk) == 1]

        # Check: is -1 always reachable?
        neg1 = (-1) % mk

        # H = subgroup generated by all small primes coprime to m_k
        H_full = subgroup_generated(small_primes, mk)

        # Index of H_full in G
        index = G_size // len(H_full) if len(H_full) > 0 else float('inf')

        neg1_in_H = neg1 in H_full

        print(f"  Small primes coprime to {mk}: {small_primes}")
        print(f"  H (subgroup from all small primes): size {len(H_full)}, index {index}")
        print(f"  -1 ∈ H: {neg1_in_H}")

        if neg1_in_H:
            print(f"  ✓ Since -1 ∈ H, for any 29-smooth s, -s ∈ H, so e=1 always works!")
        elif index <= 3:
            print(f"  ✓ Index ≤ 3, so S2 condition can apply with any q ∉ H")
        else:
            print(f"  ⚠ Need to check specific patterns more carefully")

def test_sufficient_conditions_on_failures():
    """
    Test GPT4's sufficient conditions (S1) and (S2) on the 14 failures.
    """
    print("\n" + "=" * 70)
    print("TESTING SUFFICIENT CONDITIONS ON 14 FAILURES")
    print("=" * 70)

    for p in FAILURES:
        print(f"\np = {p}")

        any_k_works = False

        for k in K13:
            xk = x_k(p, k)
            mk = M_K[k]
            target = (-xk) % mk

            s, L = smooth_part(xk, 29)
            large_primes = [(q, e) for q, e in factor(xk) if q > 29]

            if not large_primes:
                # x_k is 29-smooth - check directly
                div_res = divisor_residue_set(xk, mk)
                if div_res and target in div_res:
                    print(f"  k={k}: x_k={xk} is 29-smooth, target {target} ∈ Div(x²) ✓")
                    any_k_works = True
                continue

            # Has large prime(s)
            q, e_q = large_primes[0]

            if gcd(q, mk) > 1:
                continue  # Skip if q shares factor with m_k

            q_inv = pow(q, -1, mk)

            # Three targets
            target_e0 = ((-s) * q) % mk
            target_e1 = (-s) % mk
            target_e2 = ((-s) * q_inv) % mk

            # Check if any is hit by divisors of s²
            if gcd(s, mk) == 1:
                s_div_res = divisor_residue_set(s, mk)

                e0_works = target_e0 in s_div_res
                e1_works = target_e1 in s_div_res
                e2_works = target_e2 in s_div_res

                if e0_works or e1_works or e2_works:
                    which = []
                    if e0_works: which.append("e=0")
                    if e1_works: which.append("e=1")
                    if e2_works: which.append("e=2")
                    # But wait - we need e ≤ 2*e_q
                    # If e_q = 1, we can use e ∈ {0,1,2}
                    # If e_q > 1, we have more options
                    print(f"  k={k}: x_k={xk}=q^{e_q}·s where q={q}, s={s}")
                    print(f"    Targets: e0={target_e0}, e1={target_e1}, e2={target_e2}")
                    print(f"    Works: {which}")
                    any_k_works = True

        if not any_k_works:
            print(f"  ⚠ No k in K13 gives witness via smooth framework")

if __name__ == "__main__":
    verify_coprimality()
    verify_size_constraint_removal()
    classify_bad_patterns()
    analyze_one_large_prime_framework()
    test_sufficient_conditions_on_failures()
