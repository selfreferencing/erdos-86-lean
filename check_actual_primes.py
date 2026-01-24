#!/usr/bin/env python3
"""
Check that actual Mordell-hard primes in the "hard" residue classes
still have witnesses via larger primes.

The key insight: for actual primes, the x_k values are large and
have many prime factors. Even if small primes don't work,
larger primes can provide witnesses.
"""

K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

def legendre(a, p):
    if a % p == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return result if result == 1 else -1

def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True

def prime_factors(n):
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            if d not in factors:
                factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def x_k(p, k):
    return (p + 4*k + 3) // 4

# The "hard" residue classes mod 1680
HARD_RESIDUES = [1, 121, 169, 289, 361, 529, 841, 961, 1369]

print("=" * 70)
print("CHECKING ACTUAL PRIMES IN HARD RESIDUE CLASSES")
print("=" * 70)
print()

# Find primes in each hard residue class
for res in HARD_RESIDUES[:6]:  # Check first 6
    print(f"Residue class: p ≡ {res} (mod 1680)")
    print("-" * 50)

    # Find primes in this class
    primes_in_class = []
    for p in range(res, 100000, 1680):
        if is_prime(p) and (p % 840) in MORDELL_HARD:
            primes_in_class.append(p)
        if len(primes_in_class) >= 5:
            break

    for p in primes_in_class:
        n = (p + 23) // 4
        print(f"\n  p = {p}, n = {n}")

        found_witness = False
        witness_details = None

        for k in K10:
            x = x_k(p, k)
            factors = prime_factors(x)

            for q in factors:
                if q == 2:
                    continue
                leg = legendre(p, q)
                if leg == -1:
                    found_witness = True
                    witness_details = (k, q, x)
                    break

            if found_witness:
                break

        if found_witness:
            k, q, x = witness_details
            print(f"    WITNESS: k={k}, q={q} | x_k={x}, (p/{q}) = -1")
        else:
            print(f"    NO WITNESS FOUND!")
            # Show more details
            for k in K10:
                x = x_k(p, k)
                factors = prime_factors(x)
                legs = [(q, legendre(p, q)) for q in factors if q > 2]
                print(f"      k={k}: x={x}, factors={factors}")
                print(f"        Legendre: {legs}")

    print()

print("=" * 70)
print("SUMMARY")
print("=" * 70)
print()

# Count how many primes have witnesses
total_checked = 0
with_witness = 0

for p in range(2, 50000):
    if is_prime(p) and (p % 840) in MORDELL_HARD:
        total_checked += 1

        found = False
        for k in K10:
            x = x_k(p, k)
            factors = prime_factors(x)
            for q in factors:
                if q > 2 and legendre(p, q) == -1:
                    found = True
                    break
            if found:
                break

        if found:
            with_witness += 1

print(f"Mordell-hard primes up to 50000: {total_checked}")
print(f"With Legendre witness: {with_witness}")
print(f"Without: {total_checked - with_witness}")
