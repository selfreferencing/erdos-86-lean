#!/usr/bin/env python3
"""
Deep analysis of the 6 resistant classes to find universal recipes.

For each resistant class r mod 840:
1. Test more primes and more k values
2. Look for patterns in which k values work
3. Determine if a universal recipe exists at a larger modulus
"""

from math import gcd
from collections import defaultdict

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]
RESISTANT_CLASSES = [1, 121, 169, 289, 361, 529]

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
            return d
    return None

def get_primes_in_class(r, M=840, count=20, limit=10**8):
    """Get primes in residue class r mod M."""
    primes = []
    p = r
    while len(primes) < count and p < limit:
        if p > 1 and is_prime(p):
            primes.append(p)
        p += M
    return primes

def analyze_class(r, num_primes=20):
    """Deep analysis of resistant class r mod 840."""
    print(f"\n{'='*70}")
    print(f"ANALYZING CLASS r ≡ {r} (mod 840)")
    print(f"Note: {r} = {int(r**0.5)}² mod 840" if int(r**0.5)**2 % 840 == r else "")
    print(f"{'='*70}")

    primes = get_primes_in_class(r, 840, num_primes)
    print(f"Testing {len(primes)} primes: {primes[:5]}...")

    # For each prime, find ALL k ∈ K_COMPLETE that work
    prime_to_k = {}
    for p in primes:
        working_k = []
        for k in K_COMPLETE:
            witness = find_witness(p, k)
            if witness is not None:
                working_k.append((k, witness))
        prime_to_k[p] = working_k

    # Find k values that work for ALL primes
    all_k = set(K_COMPLETE)
    for p, k_list in prime_to_k.items():
        k_set = set(k for k, w in k_list)
        all_k &= k_set

    print(f"\nk values that work for ALL {len(primes)} primes: {sorted(all_k)}")

    if all_k:
        # This class might have a universal recipe!
        best_k = min(all_k)
        print(f"\n*** POTENTIAL UNIVERSAL RECIPE: k = {best_k}, m = {4*best_k+3} ***")

        # Show witnesses for each prime
        print(f"\nWitnesses at k={best_k}:")
        witness_set = set()
        for p in primes:
            witness = find_witness(p, best_k)
            witness_set.add(witness)
            if len([x for x in primes if find_witness(x, best_k) == witness]) > 1:
                continue  # Don't repeat common witnesses
            print(f"  p={p}: d={witness}, d mod {4*best_k+3} = {witness % (4*best_k+3)}")

        print(f"\nDistinct witnesses used: {sorted(witness_set)}")

    else:
        # No universal k - need hierarchical approach
        print(f"\nNo k ∈ K_COMPLETE works for ALL primes in this class.")
        print("Need hierarchical refinement at larger modulus.")

        # Analyze patterns: which k works for which primes?
        k_coverage = defaultdict(list)
        for p, k_list in prime_to_k.items():
            for k, w in k_list:
                k_coverage[k].append(p)

        # Find k values that cover the most
        print(f"\nBest covering k values:")
        for k in sorted(k_coverage.keys(), key=lambda x: -len(k_coverage[x]))[:5]:
            covered = len(k_coverage[k])
            print(f"  k={k} (m={4*k+3}): covers {covered}/{len(primes)} primes")

        # Suggest hierarchical split
        print(f"\nSuggested approach: Split class {r} mod 840 by residue mod m_k")

    return all_k

def main():
    print("DEEP ANALYSIS OF RESISTANT CLASSES")
    print("=" * 70)

    universal_k = {}
    for r in RESISTANT_CLASSES:
        result = analyze_class(r, num_primes=20)
        if result:
            universal_k[r] = min(result)

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if universal_k:
        print(f"\nClasses with potential universal recipe:")
        for r, k in universal_k.items():
            print(f"  r ≡ {r} (mod 840): k = {k}, m = {4*k+3}")
    else:
        print("\nNo resistant class has a universal k within K_COMPLETE.")

    remaining = set(RESISTANT_CLASSES) - set(universal_k.keys())
    if remaining:
        print(f"\nClasses requiring hierarchical refinement: {sorted(remaining)}")
        print("These need Level 2 recipes at larger modulus.")

if __name__ == "__main__":
    main()
