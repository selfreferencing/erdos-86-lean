#!/usr/bin/env python3
"""
Full verification: Check K_COMPLETE covers ALL primes ≡ 1 (mod 4) up to 10^8.
"""

from math import gcd
import sys

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

def factor_small(n, limit=1000):
    """Factor n using trial division up to limit."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n and d <= limit:
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

def divisors_of_square_efficient(n, max_divisors=10000):
    """Return divisors of n² efficiently, with a cap to avoid memory issues."""
    # For very large n, use factorization
    facts = factor_small(n)

    divs = [1]
    for p, e in facts:
        if len(divs) > max_divisors:
            break
        new_divs = []
        for d in divs:
            power = 1
            for i in range(2*e + 1):
                new_divs.append(d * power)
                if len(new_divs) > max_divisors:
                    break
                power *= p
        divs = new_divs
    return sorted(set(divs))

def find_witness_fast(p, k, max_divisors=10000):
    """Find a Type II witness for p at k, with efficiency limits."""
    m_k = 4 * k + 3
    if (p + m_k) % 4 != 0:
        return None
    x_k = (p + m_k) // 4
    if gcd(x_k, m_k) > 1:
        return None
    target = (-x_k) % m_k

    # Try small divisors first (often the witness is small)
    for d in [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32]:
        if x_k % d == 0 or (x_k * x_k) % d == 0:
            if d % m_k == target:
                return k

    # Full divisor search
    divs = divisors_of_square_efficient(x_k, max_divisors)
    for d in divs:
        if d % m_k == target:
            return k
    return None

def find_covering_k_fast(p, K):
    """Find the first k in K that covers prime p."""
    for k in K:
        result = find_witness_fast(p, k)
        if result is not None:
            return k
    return None

def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7

    print(f"Verifying K_COMPLETE covers all primes ≡ 1 (mod 4) up to {limit:,}")
    print(f"K_COMPLETE = {K_COMPLETE}")
    print(f"|K| = {len(K_COMPLETE)}")
    print()

    uncovered = []
    count = 0
    p = 5

    checkpoint = 10**6

    while p < limit:
        if is_prime(p):
            count += 1
            result = find_covering_k_fast(p, K_COMPLETE)
            if result is None:
                uncovered.append(p)
                print(f"UNCOVERED: p = {p:,}, p mod 840 = {p % 840}")

            if count % 100000 == 0:
                print(f"Checked {count:,} primes, up to p = {p:,}, uncovered = {len(uncovered)}")

        p += 4

    print()
    print("=" * 70)
    print("FINAL RESULTS")
    print("=" * 70)
    print(f"Total primes checked: {count:,}")
    print(f"Limit: {limit:,}")
    print(f"Uncovered primes: {len(uncovered)}")

    if uncovered:
        print(f"\nFirst 20 uncovered primes:")
        for p in uncovered[:20]:
            print(f"  p = {p:,}, p mod 840 = {p % 840}")
    else:
        print(f"\n*** ALL {count:,} PRIMES COVERED BY K_COMPLETE! ***")

if __name__ == "__main__":
    main()
