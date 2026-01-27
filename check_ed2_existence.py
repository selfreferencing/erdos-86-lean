#!/usr/bin/env python3
"""
Check ED2 existence for primes P ≡ 1 (mod 4).

For each P, we search for (α, d') such that N = 4αP(d')² + 1 factors as X·Y
with X ≡ Y ≡ -1 (mod 4αd'), i.e., X ≡ Y ≡ 3 (mod 4αd').
"""

from math import isqrt, gcd
from sympy import isprime, factorint

def is_squarefree(n):
    """Check if n is squarefree."""
    for p, e in factorint(n).items():
        if e >= 2:
            return False
    return True

def find_factorization(N, mod):
    """
    Find factorization N = X * Y with X ≡ Y ≡ -1 (mod `mod`), X ≤ Y.
    Returns (X, Y) or None.
    """
    target = mod - 1  # -1 (mod mod)
    for x in range(1, isqrt(N) + 1):
        if N % x == 0:
            y = N // x
            if x % mod == target and y % mod == target:
                return (x, y) if x <= y else (y, x)
    return None

def check_ed2_for_prime(P, max_delta=500, verbose=False):
    """
    For prime P ≡ 1 (mod 4), find (α, d') such that ED2 works.
    Returns (δ, α, d', X, Y) or None.
    """
    # Try various (α, d') pairs with δ = α * d'² small
    for d_prime in range(1, isqrt(max_delta) + 2):
        for alpha in range(1, max_delta // (d_prime * d_prime) + 1):
            if not is_squarefree(alpha):
                continue
            delta = alpha * d_prime * d_prime
            if delta > max_delta:
                break

            g = alpha * d_prime  # g = α * d'
            mod = 4 * g  # congruence modulus
            N = 4 * alpha * P * d_prime * d_prime + 1

            result = find_factorization(N, mod)
            if result:
                X, Y = result
                # Verify: b' = (X+1)/(4αd'), c' = (Y+1)/(4αd')
                if (X + 1) % mod == 0 and (Y + 1) % mod == 0:
                    b_prime = (X + 1) // mod
                    c_prime = (Y + 1) // mod
                    if gcd(b_prime, c_prime) == 1:  # coprimality
                        if verbose:
                            print(f"  P={P}: δ={delta} (α={alpha}, d'={d_prime}), N={N}={X}×{Y}")
                            print(f"    b'={b_prime}, c'={c_prime}, gcd={gcd(b_prime, c_prime)}")
                        return (delta, alpha, d_prime, X, Y, b_prime, c_prime)
    return None

def main():
    # Check primes P ≡ 1 (mod 4) up to some limit
    primes_1mod4 = [p for p in range(5, 1000) if isprime(p) and p % 4 == 1]

    print("Checking ED2 existence for primes P ≡ 1 (mod 4)...")
    print("=" * 70)

    results = {}
    failures = []

    for P in primes_1mod4:
        result = check_ed2_for_prime(P, max_delta=500, verbose=False)
        if result:
            delta, alpha, d_prime, X, Y, b_prime, c_prime = result
            results[P] = (delta, alpha, d_prime)
        else:
            failures.append(P)

    print(f"\nTotal primes checked: {len(primes_1mod4)}")
    print(f"Successes: {len(results)}")
    print(f"Failures: {len(failures)}")

    if failures:
        print(f"\nFailed primes: {failures}")

    # Analyze the δ values used
    delta_counts = {}
    for P, (delta, alpha, d_prime) in results.items():
        key = (alpha, d_prime)
        if key not in delta_counts:
            delta_counts[key] = []
        delta_counts[key].append(P)

    print("\n" + "=" * 70)
    print("Analysis of (α, d') pairs used:")
    for key in sorted(delta_counts.keys()):
        alpha, d_prime = key
        delta = alpha * d_prime * d_prime
        count = len(delta_counts[key])
        print(f"  (α={alpha}, d'={d_prime}) [δ={delta}]: {count} primes")
        if count <= 10:
            print(f"    Primes: {delta_counts[key]}")

    # Check the hard cases specifically
    hard_cases = [p for p in primes_1mod4 if p % 840 in {1, 121, 169, 289, 361, 529}]
    print("\n" + "=" * 70)
    print(f"Hard cases (Mordell-hard, {len(hard_cases)} primes):")
    for P in hard_cases[:20]:
        result = check_ed2_for_prime(P, max_delta=1000, verbose=True)
        if not result:
            print(f"  P={P}: NO SOLUTION FOUND (δ ≤ 1000)")

    print("\n" + "=" * 70)
    print("Detailed check for small primes:")
    for P in primes_1mod4[:15]:
        result = check_ed2_for_prime(P, max_delta=100, verbose=True)
        if result:
            delta, alpha, d_prime, X, Y, b_prime, c_prime = result
            # Compute full solution
            g = alpha * d_prime
            b = g * b_prime
            c = g * c_prime
            A = alpha * b_prime * c_prime
            B = b * P
            C = c * P
            print(f"    Full solution: A={A}, B={B}, C={C}")
            # Verify
            lhs = 4 / P
            rhs = 1/A + 1/B + 1/C
            print(f"    Verify: 4/{P} = {lhs:.10f}, 1/{A}+1/{B}+1/{C} = {rhs:.10f}, diff={abs(lhs-rhs):.2e}")
        else:
            print(f"  P={P}: NO SOLUTION")

if __name__ == "__main__":
    main()
