#!/usr/bin/env python3
"""
Analyze: What would it take for ALL x_k values to have ONLY
prime factors q with (p/q) = 1?

This is the failure condition. Understanding it helps prove it's impossible.
"""

from math import gcd, log2

K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

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

print("=" * 70)
print("FAILURE CONDITION ANALYSIS")
print("=" * 70)
print()
print("For the obstruction to hold for ALL k in K10, we need:")
print("  All prime factors q of ALL x_k values satisfy (p/q) = 1")
print()
print("This means p must be a quadratic residue mod EVERY prime")
print("that divides any of the 10 x_k values.")
print()

# For a specific prime p, count how many distinct primes divide the x_k values
# and how many of them have (p/q) = -1

def analyze_prime(p):
    """Analyze the prime factors of x_k values for a given prime p."""
    all_factors = set()
    bad_factors = []  # (q, k) where (p/q) = -1

    for k in K10:
        x = x_k(p, k)
        factors = prime_factors(x)
        for q in factors:
            if q > 2:
                all_factors.add(q)
                if legendre(p, q) == -1:
                    bad_factors.append((q, k))

    return all_factors, bad_factors

# Analyze some specific primes
test_primes = [1009, 1201, 3361, 8689, 15121]

for p in test_primes:
    all_f, bad_f = analyze_prime(p)
    print(f"p = {p}:")
    print(f"  Total distinct odd prime factors across all x_k: {len(all_f)}")
    print(f"  Bad factors (with (p/q) = -1): {len(bad_f)}")
    print(f"  Ratio bad/total: {len(bad_f)}/{len(all_f)} = {len(bad_f)/len(all_f):.2%}")
    print(f"  Bad factors: {bad_f[:5]}...")
    print()

# Now analyze: what's the minimum number of distinct prime factors
# across all x_k values for primes of various sizes?

print("=" * 70)
print("PRIME FACTOR COUNT ANALYSIS")
print("=" * 70)
print()

MORDELL_HARD = [1, 121, 169, 289, 361, 529]

sizes = [(1000, 10000), (10000, 100000), (100000, 1000000)]

for lo, hi in sizes:
    total_factors = []
    bad_factor_counts = []

    count = 0
    for p in range(lo, hi):
        if is_prime(p) and (p % 840) in MORDELL_HARD:
            all_f, bad_f = analyze_prime(p)
            total_factors.append(len(all_f))
            bad_factor_counts.append(len(bad_f))
            count += 1
            if count >= 50:
                break

    if total_factors:
        print(f"Primes in [{lo}, {hi}]:")
        print(f"  Average distinct prime factors: {sum(total_factors)/len(total_factors):.1f}")
        print(f"  Min/Max: {min(total_factors)} / {max(total_factors)}")
        print(f"  Average bad factors: {sum(bad_factor_counts)/len(bad_factor_counts):.1f}")
        print(f"  Min bad factors: {min(bad_factor_counts)}")
        print()

# Key observation: as p grows, x_k ≈ p/4 grows, so more prime factors
# For failure to occur, ALL these prime factors must have (p/q) = 1
# This becomes exponentially unlikely

print("=" * 70)
print("EXPONENTIAL UNLIKELIHOOD ARGUMENT")
print("=" * 70)
print()

print("Heuristic argument:")
print("- For a random prime q not dividing p, Pr[(p/q) = 1] ≈ 1/2")
print("- If x_k has k distinct odd prime factors, Pr[all have (p/q)=1] ≈ 2^(-k)")
print("- For 10 values with average 5 factors each ≈ 50 total factors")
print("- Pr[all 50 have (p/q)=1] ≈ 2^(-50) ≈ 10^(-15)")
print()
print("This is why empirically we ALWAYS find a witness.")
print()

# But this is a heuristic. For a rigorous proof, we need to show
# that the prime factors across x_k values are "diverse enough"
# to guarantee at least one bad factor.

print("=" * 70)
print("THE RIGOROUS APPROACH")
print("=" * 70)
print()
print("To make this rigorous, we need to prove:")
print()
print("THEOREM: For any prime p > C (some constant),")
print("the 10 values x_5, x_7, ..., x_29 collectively have at least one")
print("odd prime factor q with (p/q) = -1.")
print()
print("PROOF STRATEGY:")
print("1. Show the x_k values have many distinct prime factors")
print("2. These factors are 'independent' in some sense")
print("3. Roughly half have (p/q) = -1 by quadratic reciprocity")
print("4. With enough factors, at least one is bad")
print()
print("For primes below C, verify computationally (already done for C = 50000)")
