#!/usr/bin/env python3
"""
Verify Gemini's REVISED Quadratic Residue theory for K13 failures.

NEW CLAIM: The 14 failures are primes p where (p/q) = 1 (Legendre symbol)
for all prime factors q of the moduli m_k in K13.

And the rescue keys k=31, 39, 41 work because they introduce NEW primes
(127, 53, 167) where the failures are NOT universal QRs.
"""

from math import gcd, isqrt

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
M_K = {k: 4*k + 3 for k in K13}

# Rescue keys
RESCUE = [31, 39, 41]
M_RESCUE = {k: 4*k + 3 for k in RESCUE}  # 127, 159=3×53, 167

FAILURES = [
    10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
    34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
    46936849, 48991849
]

def legendre_symbol(a, p):
    """Compute Legendre symbol (a/p) for odd prime p."""
    if p == 2:
        return 1 if a % 2 == 1 else 0
    a = a % p
    if a == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return -1 if result == p - 1 else result

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, isqrt(n) + 1, 2):
        if n % i == 0: return False
    return True

def prime_factors(n):
    """Return set of prime factors of n."""
    factors = set()
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            factors.add(d)
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return factors

def get_k13_prime_factors():
    """Get all prime factors of m_k for k in K13."""
    all_factors = set()
    for k in K13:
        mk = M_K[k]
        all_factors.update(prime_factors(mk))
    return sorted(all_factors)

def get_rescue_prime_factors():
    """Get NEW prime factors introduced by rescue keys."""
    k13_factors = set()
    for k in K13:
        k13_factors.update(prime_factors(M_K[k]))

    rescue_factors = set()
    for k in RESCUE:
        rescue_factors.update(prime_factors(M_RESCUE[k]))

    new_factors = rescue_factors - k13_factors
    return sorted(new_factors)

def main():
    print("VERIFYING GEMINI'S REVISED QR THEORY")
    print("=" * 70)

    # Get prime factors
    k13_primes = get_k13_prime_factors()
    print(f"\nPrime factors of K13 moduli m_k:")
    print(f"  {k13_primes}")

    rescue_new_primes = get_rescue_prime_factors()
    print(f"\nNEW prime factors from rescue keys (k=31,39,41):")
    print(f"  m_31 = {M_RESCUE[31]} = {list(prime_factors(M_RESCUE[31]))}")
    print(f"  m_39 = {M_RESCUE[39]} = {list(prime_factors(M_RESCUE[39]))}")
    print(f"  m_41 = {M_RESCUE[41]} = {list(prime_factors(M_RESCUE[41]))}")
    print(f"  New primes: {rescue_new_primes}")

    # TEST 1: Are all 14 failures QRs mod all K13 prime factors?
    print(f"\n{'='*70}")
    print("TEST 1: Are failures QRs mod ALL K13 prime factors?")
    print("=" * 70)

    print(f"\n{'p':>10} | " + " | ".join(f"{q:>3}" for q in k13_primes))
    print("-" * (12 + 6 * len(k13_primes)))

    all_universal_qr = True
    for p in FAILURES:
        symbols = []
        for q in k13_primes:
            leg = legendre_symbol(p, q)
            symbols.append(leg)

        is_universal = all(s == 1 for s in symbols)
        if not is_universal:
            all_universal_qr = False

        row = f"{p:>10} | " + " | ".join(f"{s:>3}" for s in symbols)
        row += f"  {'✓ ALL QR' if is_universal else '✗'}"
        print(row)

    print(f"\nAll failures are universal QRs mod K13 primes: {all_universal_qr}")

    # TEST 2: How do failures behave mod the NEW rescue primes?
    print(f"\n{'='*70}")
    print("TEST 2: Failures mod NEW rescue primes (53, 127, 167)")
    print("=" * 70)

    new_primes = [53, 127, 167]
    print(f"\n{'p':>10} | " + " | ".join(f"{q:>4}" for q in new_primes) + " | Covered by")
    print("-" * 60)

    for p in FAILURES:
        symbols = {q: legendre_symbol(p, q) for q in new_primes}

        # Which rescue key covers this prime?
        # k=41 (m=167): works if p is non-QR mod 167, or if some other mechanism
        # k=39 (m=159=3×53): works if p is non-QR mod 53
        # k=31 (m=127): works if p is non-QR mod 127

        covered_by = []
        if symbols[167] == -1:
            covered_by.append("k=41 (167)")
        if symbols[53] == -1:
            covered_by.append("k=39 (53)")
        if symbols[127] == -1:
            covered_by.append("k=31 (127)")

        row = f"{p:>10} | " + " | ".join(f"{symbols[q]:>4}" for q in new_primes)
        row += f" | {', '.join(covered_by) if covered_by else 'NONE (QR for all!)'}"
        print(row)

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print("=" * 70)

    # Count how many are non-QR mod each new prime
    for q in new_primes:
        non_qr = sum(1 for p in FAILURES if legendre_symbol(p, q) == -1)
        print(f"Non-QR mod {q}: {non_qr}/14 failures")

    # Check Gemini's partition claim
    print(f"\nGemini claims: k=41 covers 8, k=39 covers 4 more, k=31 covers 2 more")
    print("Checking if non-QR status matches coverage...")

    # The claim is more subtle: it's not just about being non-QR mod 167,
    # but about the interaction with the group structure

if __name__ == "__main__":
    main()
