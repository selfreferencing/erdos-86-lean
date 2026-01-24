#!/usr/bin/env python3
"""
Verify the hierarchical certificate is correct by testing specific primes
from each level of the certificate.
"""

from math import gcd

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

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

def factor(n):
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                e += 1
                n //= d
            factors.append((d, e))
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append((n, 1))
    return factors

def divisors_of_square(n):
    facts = factor(n)
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

def find_witness(p, k):
    """Find a Type II witness d for p at k."""
    m_k = 4 * k + 3
    if (p + m_k) % 4 != 0:
        return None
    x_k = (p + m_k) // 4
    if gcd(x_k, m_k) > 1:
        return None
    target = (-x_k) % m_k
    divs = divisors_of_square(x_k)
    for d in divs:
        if d % m_k == target:
            return (k, d, x_k, m_k)
    return None

def verify_prime(p):
    """Verify p is covered by K_COMPLETE and report the certificate path."""
    r = p % 840
    s = p % 11
    t = p % 23

    resistant = [1, 121, 169, 289, 361, 529]

    # Find which k covers this prime
    for k in K_COMPLETE:
        result = find_witness(p, k)
        if result:
            k_used, d, x_k, m_k = result

            if r not in resistant:
                level = 1
            elif s in [7, 8, 10] or (s in [2, 6] and r != 361):
                level = 2
            else:
                level = 3

            return {
                'p': p,
                'r': r,
                's': s,
                't': t,
                'level': level,
                'k': k_used,
                'd': d,
                'm_k': m_k,
                'x_k': x_k
            }

    return None  # Should never happen

def main():
    print("=" * 70)
    print("CERTIFICATE VERIFICATION")
    print("=" * 70)

    # Test cases from each level
    test_primes = {
        # Level 1: Non-resistant classes
        'Level 1 (non-resistant)': [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97],

        # Level 2: Resistant classes with universal sub-class coverage
        # r in {1, 121, 169, 289, 361, 529}, s in {7, 8, 10}
        'Level 2 (s=7 mod 11)': [5881, 8521, 26209, 1129, 4561, 15649],
        'Level 2 (s=8 mod 11)': [26881, 1801, 1009, 12889, 25561, 8929],
        'Level 2 (s=10 mod 11)': [4201, 6841, 15289, 8689, 39841, 4729],

        # Level 3: Resistant classes with level 3 refinement
        # These are primes from the "uncovered" sub-classes
        'Level 3 (r=1)': [9241, 2521, 14281, 7561, 47041, 3361, 20161],
        'Level 3 (r=121)': [21121, 14401, 7681, 19441, 12721, 41281],
        'Level 3 (r=169)': [29569, 53089, 55609, 2689, 3529],
        'Level 3 (r=289)': [13729, 46489, 12049, 33049, 33889],
        'Level 3 (r=361)': [54121, 49921, 33961, 8761, 20521, 9601],
        'Level 3 (r=529)': [9769, 5569, 8089, 38329, 48409],
    }

    all_passed = True

    for category, primes in test_primes.items():
        print(f"\n{category}:")
        print("-" * 60)

        for p in primes:
            if not is_prime(p):
                print(f"  {p} is not prime, skipping")
                continue

            result = verify_prime(p)

            if result:
                print(f"  p={p:>8}: Level {result['level']}, k={result['k']}, d={result['d']}, "
                      f"(r={result['r']}, s={result['s']}, t={result['t']})")
            else:
                print(f"  p={p:>8}: *** UNCOVERED ***")
                all_passed = False

    print("\n" + "=" * 70)
    if all_passed:
        print("*** ALL TEST PRIMES VERIFIED ***")
    else:
        print("*** SOME PRIMES FAILED ***")
    print("=" * 70)

    # Additional verification: random primes from resistant classes
    print("\nAdditional verification: Large primes from resistant classes")
    print("-" * 70)

    resistant = [1, 121, 169, 289, 361, 529]
    for r in resistant:
        # Find a large prime in this class
        p = r + 840 * 1000
        while not is_prime(p) or p % 4 != 1:
            p += 840

        result = verify_prime(p)
        if result:
            print(f"  r={r:>3}: p={p:>10}, Level {result['level']}, k={result['k']}, d={result['d']}")
        else:
            print(f"  r={r:>3}: p={p:>10} *** UNCOVERED ***")
            all_passed = False

    print("\n" + "=" * 70)
    print("CERTIFICATE STATUS: " + ("VERIFIED" if all_passed else "FAILED"))
    print("=" * 70)

if __name__ == "__main__":
    main()
