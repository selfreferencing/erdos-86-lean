#!/usr/bin/env python3
"""
Phase 1: Enumerate Type-I-resistant primes and characterize their structure.

For each prime p ≡ 1 (mod 4), we check Bradford's conditions:
- x ∈ [⌈p/4⌉, ⌊p/2⌋]
- d | x²
- Type I: d ≡ -px (mod m) where m = 4x - p
- Type II: d ≤ x and d ≡ -x (mod m)

We identify primes where Type I fails for ALL admissible x,
then verify Type II succeeds and record structural features.
"""

import math
from collections import defaultdict
from typing import List, Tuple, Optional, Dict, Set
import json

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(math.isqrt(n)) + 1, 2):
        if n % i == 0:
            return False
    return True

def sieve_primes(limit: int) -> List[int]:
    """Sieve of Eratosthenes."""
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = False
    return [i for i in range(2, limit + 1) if sieve[i]]

def get_divisors(n: int) -> List[int]:
    """Get all divisors of n."""
    divisors = []
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            divisors.append(i)
            if i != n // i:
                divisors.append(n // i)
    return sorted(divisors)

def factorize(n: int) -> Dict[int, int]:
    """Return prime factorization as {prime: exponent}."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors

def legendre_symbol(a: int, p: int) -> int:
    """Compute Legendre symbol (a|p) for odd prime p."""
    if p == 2:
        return 1 if a % 2 == 1 else 0
    a = a % p
    if a == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return result if result == 1 else -1

def check_type_i(p: int, x: int) -> Optional[int]:
    """
    Check if Type I solution exists for given p, x.
    Returns witnessing divisor d if found, None otherwise.

    Type I condition: d | x² and d ≡ -px (mod m) where m = 4x - p
    """
    m = 4 * x - p
    if m <= 0:
        return None

    target = (-p * x) % m
    x_squared = x * x

    for d in get_divisors(x_squared):
        if d % m == target:
            return d
    return None

def check_type_ii(p: int, x: int) -> Optional[int]:
    """
    Check if Type II solution exists for given p, x.
    Returns witnessing divisor d if found, None otherwise.

    Type II condition: d | x², d ≤ x, and d ≡ -x (mod m) where m = 4x - p
    """
    m = 4 * x - p
    if m <= 0:
        return None

    target = (-x) % m
    x_squared = x * x

    for d in get_divisors(x_squared):
        if d <= x and d % m == target:
            return d
    return None

def analyze_prime(p: int) -> Dict:
    """
    Analyze a prime p for Type I/II solutions.
    Returns a dict with analysis results.
    """
    x_min = math.ceil(p / 4)
    x_max = p // 2

    # Check Type I for all admissible x
    type_i_witnesses = []
    for x in range(x_min, x_max + 1):
        d = check_type_i(p, x)
        if d is not None:
            type_i_witnesses.append((x, d, 4*x - p))

    type_i_exists = len(type_i_witnesses) > 0

    # Check Type II for all admissible x
    type_ii_witnesses = []
    for x in range(x_min, x_max + 1):
        d = check_type_ii(p, x)
        if d is not None:
            type_ii_witnesses.append((x, d, 4*x - p))

    type_ii_exists = len(type_ii_witnesses) > 0

    result = {
        'p': p,
        'p_mod_4': p % 4,
        'p_mod_24': p % 24,
        'p_mod_840': p % 840,
        'type_i_exists': type_i_exists,
        'type_ii_exists': type_ii_exists,
        'type_i_witness_count': len(type_i_witnesses),
        'type_ii_witness_count': len(type_ii_witnesses),
    }

    if type_i_exists:
        # Record minimal Type I witness
        min_witness = min(type_i_witnesses, key=lambda w: w[0])
        result['type_i_min_x'] = min_witness[0]
        result['type_i_min_d'] = min_witness[1]
        result['type_i_min_m'] = min_witness[2]

    if type_ii_exists:
        # Record minimal Type II witness
        min_witness = min(type_ii_witnesses, key=lambda w: w[0])
        result['type_ii_min_x'] = min_witness[0]
        result['type_ii_min_d'] = min_witness[1]
        result['type_ii_min_m'] = min_witness[2]
        result['type_ii_m_factors'] = factorize(min_witness[2])

    # Type I resistant = Type I fails for all x
    result['type_i_resistant'] = not type_i_exists

    # Complementarity check
    if not type_i_exists and not type_ii_exists:
        result['both_fail'] = True  # This would be a counterexample!
    else:
        result['both_fail'] = False

    # Compute Legendre symbols for small primes
    small_primes = [3, 5, 7, 11, 13]
    result['legendre'] = {q: legendre_symbol(p, q) for q in small_primes if q != p}

    return result

def main():
    import sys

    # Default limit, can be overridden by command line
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 100000

    print(f"Phase 1: Analyzing primes up to {limit}")
    print("=" * 60)

    primes = sieve_primes(limit)
    # Focus on p ≡ 1 (mod 4) as per the complementarity theorem scope
    primes_1mod4 = [p for p in primes if p % 4 == 1]

    print(f"Total primes: {len(primes)}")
    print(f"Primes ≡ 1 (mod 4): {len(primes_1mod4)}")
    print()

    type_i_resistant = []
    both_fail = []
    mod_840_counts = defaultdict(int)

    for i, p in enumerate(primes_1mod4):
        if (i + 1) % 1000 == 0:
            print(f"  Processed {i + 1}/{len(primes_1mod4)} primes...")

        result = analyze_prime(p)

        if result['type_i_resistant']:
            type_i_resistant.append(result)
            mod_840_counts[result['p_mod_840']] += 1

        if result['both_fail']:
            both_fail.append(result)

    print()
    print("=" * 60)
    print("RESULTS")
    print("=" * 60)

    print(f"\nType-I-resistant primes found: {len(type_i_resistant)}")

    if both_fail:
        print(f"\n*** COUNTEREXAMPLES FOUND: {len(both_fail)} ***")
        for r in both_fail:
            print(f"  p = {r['p']}")
    else:
        print("\nNo counterexamples (both fail) found. Complementarity holds in this range.")

    print("\n" + "-" * 60)
    print("Type-I-resistant primes (Type I fails, Type II succeeds):")
    print("-" * 60)

    # The six "difficult" residue classes mod 840 (squares)
    difficult_classes = {1, 121, 169, 289, 361, 529}

    for r in type_i_resistant[:50]:  # Show first 50
        p = r['p']
        mod840 = r['p_mod_840']
        in_difficult = "DIFFICULT" if mod840 in difficult_classes else ""

        type_ii_info = ""
        if r['type_ii_exists']:
            type_ii_info = f"Type II: x={r['type_ii_min_x']}, d={r['type_ii_min_d']}, m={r['type_ii_min_m']}"

        print(f"p={p:7d}  mod840={mod840:3d} {in_difficult:10s}  {type_ii_info}")

    if len(type_i_resistant) > 50:
        print(f"  ... and {len(type_i_resistant) - 50} more")

    print("\n" + "-" * 60)
    print("Distribution of Type-I-resistant primes by residue class mod 840:")
    print("-" * 60)

    for mod_class in sorted(mod_840_counts.keys()):
        count = mod_840_counts[mod_class]
        is_difficult = "← DIFFICULT (square)" if mod_class in difficult_classes else ""
        print(f"  p ≡ {mod_class:3d} (mod 840): {count:5d} primes {is_difficult}")

    # Check: are ALL Type-I-resistant primes in the difficult classes?
    all_in_difficult = all(r['p_mod_840'] in difficult_classes for r in type_i_resistant)
    print(f"\nAll Type-I-resistant primes in difficult classes mod 840? {all_in_difficult}")

    # Analyze Type II witnesses for resistant primes
    print("\n" + "-" * 60)
    print("Type II witness analysis for resistant primes:")
    print("-" * 60)

    m_values = []
    for r in type_i_resistant:
        if r['type_ii_exists']:
            m_values.append(r['type_ii_min_m'])

    if m_values:
        print(f"  Min m: {min(m_values)}")
        print(f"  Max m: {max(m_values)}")
        print(f"  Median m: {sorted(m_values)[len(m_values)//2]}")

        # Check smoothness of m values
        smooth_count = sum(1 for m in m_values if max(factorize(m).keys()) <= 7)
        print(f"  7-smooth m values: {smooth_count}/{len(m_values)} ({100*smooth_count/len(m_values):.1f}%)")

    # Save detailed results
    output_file = f"/Users/kvallie2/Desktop/esc_stage8/phase1_results_{limit}.json"
    with open(output_file, 'w') as f:
        json.dump({
            'limit': limit,
            'type_i_resistant_count': len(type_i_resistant),
            'counterexamples': len(both_fail),
            'mod_840_distribution': dict(mod_840_counts),
            'all_in_difficult_classes': all_in_difficult,
            'resistant_primes': type_i_resistant
        }, f, indent=2)

    print(f"\nDetailed results saved to: {output_file}")

    # Special analysis of p = 2521
    print("\n" + "=" * 60)
    print("SPECIAL ANALYSIS: p = 2521")
    print("=" * 60)

    result_2521 = analyze_prime(2521)
    print(f"p = 2521")
    print(f"  p mod 4: {result_2521['p_mod_4']}")
    print(f"  p mod 840: {result_2521['p_mod_840']}")
    print(f"  Type I exists: {result_2521['type_i_exists']}")
    print(f"  Type II exists: {result_2521['type_ii_exists']}")

    if result_2521['type_ii_exists']:
        print(f"  Type II witness: x={result_2521['type_ii_min_x']}, d={result_2521['type_ii_min_d']}, m={result_2521['type_ii_min_m']}")
        print(f"  m factorization: {result_2521['type_ii_m_factors']}")

    print(f"  Legendre symbols: {result_2521['legendre']}")

if __name__ == "__main__":
    main()
