#!/usr/bin/env python3
"""
Verify Gemini's Quadratic Residue theory for K13 failures.

Gemini claims: The 14 failures occur because for each k in K13,
all prime factors of x_k are quadratic residues mod m_k,
trapping divisors in QR subgroup while -x_k is a non-residue.
"""

from math import gcd, isqrt

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
M_K = {k: 4*k + 3 for k in K13}

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
    # Euler's criterion: a^((p-1)/2) ≡ (a/p) mod p
    result = pow(a, (p - 1) // 2, p)
    return -1 if result == p - 1 else result

def is_quadratic_residue(a, m):
    """Check if a is a quadratic residue mod m (for m = 4k+3)."""
    a = a % m
    if a == 0:
        return True  # 0 is trivially a QR
    if gcd(a, m) > 1:
        return None  # Not in the unit group

    # For prime m, use Legendre symbol
    if is_prime(m):
        return legendre_symbol(a, m) == 1

    # For composite m, need Jacobi symbol and more care
    # For our case, m_k = 4k+3, check if prime
    # If not prime, factor and use CRT
    return jacobi_symbol(a, m) == 1  # Simplified

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

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, isqrt(n) + 1, 2):
        if n % i == 0: return False
    return True

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

def verify_qr_theory(p):
    """
    For each k in K13, check:
    1. Are all prime factors of x_k quadratic residues mod m_k?
    2. Is -x_k a non-residue mod m_k?
    """
    print(f"\n{'='*70}")
    print(f"PRIME p = {p}")
    print(f"{'='*70}")

    all_factors_qr = True
    target_non_qr = True

    results = []

    for k in K13:
        mk = M_K[k]
        xk = x_k(p, k)
        facts = factor(xk)
        target = (-xk) % mk

        # Check if each prime factor is QR mod m_k
        factors_qr = []
        for q, e in facts:
            if gcd(q, mk) == 1:  # Only check coprime factors
                qr = jacobi_symbol(q, mk) == 1
                factors_qr.append((q, qr))

        all_qr = all(qr for _, qr in factors_qr)

        # Check if -x_k is QR mod m_k
        target_is_qr = jacobi_symbol(target, mk) == 1 if gcd(target, mk) == 1 else None

        # Check if -1 is QR mod m_k (should be False for m_k ≡ 3 mod 4)
        neg1_qr = jacobi_symbol(-1, mk) == 1

        results.append({
            'k': k,
            'm_k': mk,
            'x_k': xk,
            'factors': facts,
            'all_factors_qr': all_qr,
            'target': target,
            'target_is_qr': target_is_qr,
            '-1_is_qr': neg1_qr
        })

        if not all_qr:
            all_factors_qr = False
        if target_is_qr:
            target_non_qr = False

    # Print summary
    print(f"\n{'k':>3} | {'m_k':>4} | {'all_factors_QR':>14} | {'target':>6} | {'target_is_QR':>12} | {'-1_is_QR':>8}")
    print("-" * 70)

    for r in results:
        print(f"{r['k']:>3} | {r['m_k']:>4} | {str(r['all_factors_qr']):>14} | {r['target']:>6} | {str(r['target_is_qr']):>12} | {str(r['-1_is_qr']):>8}")

    print(f"\nGemini's theory prediction:")
    print(f"  All factors QR for all k: {all_factors_qr}")
    print(f"  Target non-QR for all k: {target_non_qr}")
    print(f"  Theory holds: {all_factors_qr and target_non_qr}")

    return all_factors_qr and target_non_qr

def main():
    print("VERIFYING GEMINI'S QUADRATIC RESIDUE THEORY")
    print("=" * 70)

    theory_holds = 0
    theory_fails = 0

    for p in FAILURES:
        if verify_qr_theory(p):
            theory_holds += 1
        else:
            theory_fails += 1

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Theory holds for: {theory_holds}/{len(FAILURES)} failures")
    print(f"Theory fails for: {theory_fails}/{len(FAILURES)} failures")

    if theory_holds == len(FAILURES):
        print("\nGEMINI'S THEORY IS VALIDATED!")
        print("The 14 failures are exactly the 'Poly-Quadratic Residue' primes.")
    else:
        print("\nGemini's theory needs refinement.")

if __name__ == "__main__":
    main()
