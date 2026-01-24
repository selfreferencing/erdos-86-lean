#!/usr/bin/env python3
"""
Investigate K13 failures to understand why they fail.
"""

from math import gcd, isqrt

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
M_K = {k: 4*k + 3 for k in K13}

# The 14 failures from 5×10^7 verification
FAILURES = [10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
            34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
            46936849, 48991849]

def factorize(n):
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            exp = 0
            while n % d == 0:
                exp += 1
                n //= d
            factors.append((d, exp))
        d += 1
    if n > 1:
        factors.append((n, 1))
    return factors

def divisors(n):
    divs = [1]
    for p, e in factorize(n):
        new_divs = []
        pe = 1
        for _ in range(e + 1):
            for d in divs:
                new_divs.append(d * pe)
            pe *= p
        divs = new_divs
    return sorted(divs)

def x_k(p, k):
    m = M_K[k]
    return (p + m) // 4 if (p + m) % 4 == 0 else None

def analyze_prime(p):
    print(f"\n{'='*70}")
    print(f"ANALYZING p = {p}")
    print(f"p mod 840 = {p % 840}")
    print(f"{'='*70}")

    for k in K13:
        m = M_K[k]
        x = x_k(p, k)
        if x is None:
            print(f"\nk={k:>2}, m_k={m:>3}: x_k undefined (4 ∤ p + m_k)")
            continue

        target = (-x) % m
        facts = factorize(x)

        print(f"\nk={k:>2}, m_k={m:>3}:")
        print(f"  x_k = {x}")
        print(f"  factorization: {facts}")
        print(f"  target: -x_k ≡ {target} (mod {m})")

        # Find all divisors d of x² with d ≤ x and d ≡ target (mod m)
        x_sq = x * x
        witnesses = []
        for d in range(target if target > 0 else m, x + 1, m):
            if d > 0 and x_sq % d == 0:
                witnesses.append(d)

        if witnesses:
            print(f"  WITNESSES: {witnesses[:10]}{'...' if len(witnesses) > 10 else ''}")
        else:
            print(f"  NO WITNESSES!")
            # Explain why
            print(f"  Checking divisors d ≡ {target} (mod {m}) up to {x}:")
            checked = 0
            for d in range(target if target > 0 else m, min(x + 1, 10000), m):
                if d > 0:
                    checked += 1
                    if x_sq % d == 0:
                        print(f"    d={d}: divides x²? YES - should be witness!")
                    else:
                        pass  # print(f"    d={d}: divides x²? NO")
            print(f"  (checked {checked} candidates)")

def main():
    print("Investigating K13 failures")
    print(f"Number of failures: {len(FAILURES)}")

    for p in FAILURES[:5]:  # Analyze first 5
        analyze_prime(p)

if __name__ == "__main__":
    main()
