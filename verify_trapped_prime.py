#!/usr/bin/env python3
"""
Verify GPT's critical discovery: p = 66,032,521 is the ONLY prime < 10^8
that is fully trapped at ALL k ∈ K13.

This script:
1. Verifies p = 66,032,521 is trapped at all k ∈ K13
2. Checks the factorizations GPT provided
3. Verifies each prime factor is a QR mod the corresponding m_k
4. Finds which k ∉ K13 rescues this prime
5. Searches for other fully trapped primes up to a limit
"""

from math import gcd, isqrt
from functools import lru_cache

# K13 as defined throughout
K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

def is_prime(n):
    """Miller-Rabin primality test."""
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

    # Write n-1 as 2^r * d
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2

    # Witnesses for deterministic test up to 3,317,044,064,679,887,385,961,981
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
    """Return list of (prime, exponent) pairs."""
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

def jacobi_symbol(a, n):
    """Compute Jacobi symbol (a/n)."""
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be positive odd")
    a = a % n
    result = 1
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in [3, 5]:
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a = a % n
    return result if n == 1 else 0

def divisors_of_square(n):
    """Return all divisors of n²."""
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

def is_trapped_at_k(p, k):
    """
    Check if prime p is trapped at k.
    Trapped means: ALL prime factors of x_k are QRs mod m_k.
    """
    m_k = 4 * k + 3
    x_k = (p + m_k) // 4

    if (p + m_k) % 4 != 0:
        return False, None, None, "x_k not integer"

    facts = factor(x_k)

    for q, e in facts:
        if gcd(q, m_k) > 1:
            continue  # Skip if q divides m_k
        jac = jacobi_symbol(q, m_k)
        if jac == -1:
            # Found a non-QR prime factor - NOT trapped
            return False, x_k, facts, f"q={q} is non-QR mod {m_k}"

    # All prime factors are QRs (or divide m_k) - TRAPPED
    return True, x_k, facts, "all prime factors are QRs"

def has_witness_at_k(p, k):
    """
    Check if prime p has a Type II witness at k.
    Returns (has_witness, witness_d, details)
    """
    m_k = 4 * k + 3
    x_k = (p + m_k) // 4

    if (p + m_k) % 4 != 0:
        return False, None, "x_k not integer"

    if gcd(x_k, m_k) > 1:
        return False, None, f"gcd(x_k, m_k) = {gcd(x_k, m_k)} > 1"

    target = (-x_k) % m_k
    divs = divisors_of_square(x_k)

    for d in divs:
        if d % m_k == target:
            return True, d, f"d={d} ≡ {target} (mod {m_k})"

    return False, None, f"no divisor ≡ {target} (mod {m_k})"

def verify_trapped_prime(p):
    """Verify that p is fully trapped at all k ∈ K13."""
    print(f"\n{'='*70}")
    print(f"VERIFYING p = {p:,}")
    print(f"{'='*70}")

    print(f"\np mod 840 = {p % 840} (Mordell-hard if 1, 121, 169, 289, 361, 529)")
    print(f"p ≡ {p % 4} (mod 4)")
    print(f"p ≡ {p % 8} (mod 8)")

    t = (p + 3) // 4
    print(f"\nt = (p + 3)/4 = {t:,}")

    trapped_count = 0
    escape_k = []

    print(f"\n{'k':>3} | {'m_k':>4} | {'x_k':>15} | {'Trapped?':>8} | Factorization / Reason")
    print("-" * 80)

    for k in K13:
        m_k = 4 * k + 3
        trapped, x_k, facts, reason = is_trapped_at_k(p, k)

        if trapped:
            trapped_count += 1
            fact_str = " · ".join(f"{q}^{e}" if e > 1 else str(q) for q, e in facts)
            print(f"{k:>3} | {m_k:>4} | {x_k:>15,} | {'YES':>8} | {fact_str}")
        else:
            escape_k.append(k)
            print(f"{k:>3} | {m_k:>4} | {x_k:>15,} | {'NO':>8} | {reason}")

    print(f"\nTrapped at {trapped_count}/{len(K13)} values of k")

    if trapped_count == len(K13):
        print(f"\n*** p = {p:,} IS FULLY TRAPPED AT ALL K13! ***")

        # Now check for witnesses
        print(f"\nChecking for Type II witnesses at each k ∈ K13:")
        witness_found = False
        for k in K13:
            has_wit, d, details = has_witness_at_k(p, k)
            status = "✓ WITNESS" if has_wit else "✗ none"
            print(f"  k={k:>2} (m={4*k+3:>3}): {status} - {details}")
            if has_wit:
                witness_found = True

        if not witness_found:
            print(f"\n*** CONFIRMED: NO TYPE II WITNESS FOR ANY k ∈ K13 ***")

        return True, escape_k
    else:
        print(f"\nEscape k values: {escape_k}")
        return False, escape_k

def find_rescue_k(p, k_max=200):
    """Find k ∉ K13 that rescues prime p."""
    print(f"\n{'='*70}")
    print(f"SEARCHING FOR RESCUE k ∉ K13 (up to k={k_max})")
    print(f"{'='*70}")

    rescuers = []

    for k in range(k_max + 1):
        if k in K13:
            continue

        has_wit, d, details = has_witness_at_k(p, k)
        if has_wit:
            m_k = 4 * k + 3
            x_k = (p + m_k) // 4
            rescuers.append((k, m_k, x_k, d, details))
            print(f"k={k:>3} (m={m_k:>3}): x={x_k:,}, witness d={d:,}")

            # Show factorization of x_k
            facts = factor(x_k)
            fact_str = " · ".join(f"{q}^{e}" if e > 1 else str(q) for q, e in facts)
            print(f"       x_k = {fact_str}")

            # Show factorization of witness
            d_facts = factor(d)
            d_fact_str = " · ".join(f"{q}^{e}" if e > 1 else str(q) for q, e in d_facts)
            print(f"       d = {d_fact_str}")
            print()

            if len(rescuers) >= 5:
                print(f"  (found 5 rescuers, stopping search)")
                break

    if rescuers:
        print(f"\nFound {len(rescuers)} rescue k values")
        print(f"Smallest rescue: k = {rescuers[0][0]} (m = {rescuers[0][1]})")
    else:
        print(f"\nNo rescue k found up to k = {k_max}")

    return rescuers

def search_fully_trapped_primes(limit, verbose=True):
    """Search for primes fully trapped at all K13."""
    print(f"\n{'='*70}")
    print(f"SEARCHING FOR FULLY TRAPPED PRIMES UP TO {limit:,}")
    print(f"{'='*70}")

    fully_trapped = []
    count = 0

    # Generate primes p ≡ 1 (mod 4)
    p = 5
    while p <= limit:
        if is_prime(p):
            count += 1

            # Check if trapped at all K13
            all_trapped = True
            for k in K13:
                trapped, _, _, _ = is_trapped_at_k(p, k)
                if not trapped:
                    all_trapped = False
                    break

            if all_trapped:
                fully_trapped.append(p)
                if verbose:
                    print(f"  Found fully trapped prime: p = {p:,}")

            if verbose and count % 100000 == 0:
                print(f"  Checked {count:,} primes, found {len(fully_trapped)} fully trapped")

        p += 4  # Next candidate ≡ 1 (mod 4)

    print(f"\nTotal primes ≡ 1 (mod 4) checked: {count:,}")
    print(f"Fully trapped primes found: {len(fully_trapped)}")

    if fully_trapped:
        print(f"\nList of fully trapped primes:")
        for p in fully_trapped:
            print(f"  p = {p:,} (p mod 840 = {p % 840})")

    return fully_trapped

def main():
    # 1. Verify the claimed fully trapped prime
    p = 66_032_521
    is_fully_trapped, escape_k = verify_trapped_prime(p)

    if is_fully_trapped:
        # 2. Find rescue k values
        rescuers = find_rescue_k(p, k_max=200)

    # 3. Optionally search for other fully trapped primes
    print("\n" + "="*70)
    print("OPTIONAL: Search for other fully trapped primes")
    print("="*70)

    response = input("\nSearch for fully trapped primes up to 10^7? (y/n): ").strip().lower()
    if response == 'y':
        search_fully_trapped_primes(10_000_000, verbose=True)

    response = input("\nSearch for fully trapped primes up to 10^8? (y/n): ").strip().lower()
    if response == 'y':
        search_fully_trapped_primes(100_000_000, verbose=False)

if __name__ == "__main__":
    main()
