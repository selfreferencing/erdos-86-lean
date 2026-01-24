#!/usr/bin/env python3
"""
Phase 1: Check ORIGINAL Type I/II definitions from ESC literature.

From the meta-prompts document:
- Type I constraint: m | (kp+1) AND m ≡ -p (mod 4k)
- This corresponds to the factorization identity approach

Type I FAILS when: For ALL k ≥ 1, no divisor m of (kp+1) satisfies m ≡ -p (mod 4k)

We need to bound k. From literature: check k up to some reasonable bound.
For the Type I method, useful solutions have bounded k (typically k ≤ p or smaller).
"""

import math
from collections import defaultdict
from typing import List, Dict, Optional, Tuple
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
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = False
    return [i for i in range(2, limit + 1) if sieve[i]]

def get_divisors(n: int) -> List[int]:
    if n <= 0:
        return []
    divisors = []
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            divisors.append(i)
            if i != n // i:
                divisors.append(n // i)
    return sorted(divisors)

def factorize(n: int) -> Dict[int, int]:
    if n <= 0:
        return {}
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
    if p == 2:
        return 1 if a % 2 == 1 else 0
    a = a % p
    if a == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return result if result == 1 else -1

def check_type_i_original(p: int, k_max: int = None) -> Optional[Tuple[int, int]]:
    """
    Check ORIGINAL Type I condition.

    For some k ≥ 1, find divisor m of (kp+1) such that m ≡ -p (mod 4k).

    Returns (k, m) witness if found, None if Type I fails for all k up to k_max.
    """
    if k_max is None:
        # Reasonable bound: check up to p (usually solutions found much earlier)
        k_max = min(p, 10000)

    for k in range(1, k_max + 1):
        val = k * p + 1
        target = (-p) % (4 * k)  # Target residue class mod 4k

        for m in get_divisors(val):
            if m % (4 * k) == target:
                return (k, m)

    return None

def check_type_ii_original(p: int, k_max: int = None) -> Optional[Tuple[int, int, int]]:
    """
    Check ORIGINAL Type II condition (Lemma 7B style).

    For x_k = (p + m_k)/4 where m_k = 4k+3,
    Need coprime (a,b) with a,b | x_k, a+b ≡ 0 (mod m_k), and b ≥ √x_k

    Returns (k, a, b) witness if found, None otherwise.
    """
    if k_max is None:
        k_max = min(p, 1000)

    for k in range(0, k_max + 1):
        m_k = 4 * k + 3

        # Check if (p + m_k) is divisible by 4
        if (p + m_k) % 4 != 0:
            continue

        x_k = (p + m_k) // 4
        sqrt_x = math.isqrt(x_k)

        divisors = get_divisors(x_k)

        # Find coprime pair (a, b) with a+b ≡ 0 (mod m_k) and b ≥ √x_k
        for a in divisors:
            for b in divisors:
                if b < sqrt_x:
                    continue
                if a * b > x_k:  # a and b must both divide x_k
                    continue
                if x_k % a != 0 or x_k % b != 0:
                    continue
                if math.gcd(a, b) != 1:
                    continue
                if (a + b) % m_k == 0:
                    return (k, a, b)

    return None

def analyze_prime_original(p: int, k_max_i: int = None, k_max_ii: int = None) -> Dict:
    """
    Analyze prime p using ORIGINAL Type I/II definitions.
    """
    type_i_result = check_type_i_original(p, k_max_i)
    type_ii_result = check_type_ii_original(p, k_max_ii)

    result = {
        'p': p,
        'p_mod_4': p % 4,
        'p_mod_24': p % 24,
        'p_mod_840': p % 840,
        'type_i_exists': type_i_result is not None,
        'type_ii_exists': type_ii_result is not None,
    }

    if type_i_result:
        k, m = type_i_result
        result['type_i_k'] = k
        result['type_i_m'] = m
        result['type_i_val'] = k * p + 1

    if type_ii_result:
        k, a, b = type_ii_result
        result['type_ii_k'] = k
        result['type_ii_a'] = a
        result['type_ii_b'] = b
        result['type_ii_m_k'] = 4 * k + 3
        result['type_ii_x_k'] = (p + 4*k + 3) // 4

    result['type_i_resistant'] = not result['type_i_exists']
    result['both_fail'] = not result['type_i_exists'] and not result['type_ii_exists']

    # Legendre symbols
    small_primes = [3, 5, 7, 11, 13, 17, 19, 23]
    result['legendre'] = {q: legendre_symbol(p, q) for q in small_primes if q != p}

    return result

def main():
    import sys

    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    k_max = int(sys.argv[2]) if len(sys.argv) > 2 else 500

    print(f"Phase 1 (Original Type I/II): Analyzing primes up to {limit}")
    print(f"Checking Type I up to k = {k_max}")
    print("=" * 70)

    primes = sieve_primes(limit)
    primes_1mod4 = [p for p in primes if p % 4 == 1]

    print(f"Total primes: {len(primes)}")
    print(f"Primes ≡ 1 (mod 4): {len(primes_1mod4)}")
    print()

    type_i_resistant = []
    both_fail = []
    mod_840_counts = defaultdict(int)

    for i, p in enumerate(primes_1mod4):
        if (i + 1) % 100 == 0:
            print(f"  Processed {i + 1}/{len(primes_1mod4)} primes... (last: p={p})")

        result = analyze_prime_original(p, k_max_i=k_max, k_max_ii=k_max)

        if result['type_i_resistant']:
            type_i_resistant.append(result)
            mod_840_counts[result['p_mod_840']] += 1

        if result['both_fail']:
            both_fail.append(result)

    print()
    print("=" * 70)
    print("RESULTS")
    print("=" * 70)

    print(f"\nType-I-resistant primes found: {len(type_i_resistant)}")

    if both_fail:
        print(f"\n*** PRIMES WHERE BOTH METHODS FAIL (within k bounds): {len(both_fail)} ***")
        for r in both_fail[:20]:
            print(f"  p = {r['p']} (mod 840 = {r['p_mod_840']})")
    else:
        print("\nAll Type-I-resistant primes have Type II solutions.")

    print("\n" + "-" * 70)
    print("Type-I-resistant primes:")
    print("-" * 70)

    difficult_classes = {1, 121, 169, 289, 361, 529}

    for r in type_i_resistant[:30]:
        p = r['p']
        mod840 = r['p_mod_840']
        in_diff = "DIFFICULT" if mod840 in difficult_classes else ""

        type_ii_info = ""
        if r['type_ii_exists']:
            type_ii_info = f"Type II: k={r['type_ii_k']}, a={r['type_ii_a']}, b={r['type_ii_b']}"
        else:
            type_ii_info = "Type II: NOT FOUND"

        print(f"p={p:7d}  mod840={mod840:3d} {in_diff:10s}  {type_ii_info}")

    if len(type_i_resistant) > 30:
        print(f"  ... and {len(type_i_resistant) - 30} more")

    print("\n" + "-" * 70)
    print("Distribution by residue class mod 840:")
    print("-" * 70)

    for mod_class in sorted(mod_840_counts.keys()):
        count = mod_840_counts[mod_class]
        is_diff = "← DIFFICULT" if mod_class in difficult_classes else ""
        print(f"  p ≡ {mod_class:3d} (mod 840): {count:4d} primes {is_diff}")

    all_difficult = all(r['p_mod_840'] in difficult_classes for r in type_i_resistant) if type_i_resistant else True
    print(f"\nAll Type-I-resistant in difficult classes? {all_difficult}")

    # Special analysis of p = 2521
    print("\n" + "=" * 70)
    print("SPECIAL ANALYSIS: p = 2521")
    print("=" * 70)

    # Check with extended k range for 2521
    result_2521 = analyze_prime_original(2521, k_max_i=5000, k_max_ii=500)
    print(f"p = 2521")
    print(f"  p mod 840: {result_2521['p_mod_840']}")
    print(f"  Type I exists (k ≤ 5000): {result_2521['type_i_exists']}")
    if result_2521['type_i_exists']:
        print(f"    Witness: k={result_2521['type_i_k']}, m={result_2521['type_i_m']}")
    print(f"  Type II exists (k ≤ 500): {result_2521['type_ii_exists']}")
    if result_2521['type_ii_exists']:
        print(f"    Witness: k={result_2521['type_ii_k']}, a={result_2521['type_ii_a']}, b={result_2521['type_ii_b']}")
    print(f"  Legendre symbols: {result_2521['legendre']}")

    # Save results
    output_file = f"/Users/kvallie2/Desktop/esc_stage8/phase1_original_results_{limit}.json"
    with open(output_file, 'w') as f:
        json.dump({
            'limit': limit,
            'k_max': k_max,
            'type_i_resistant_count': len(type_i_resistant),
            'both_fail_count': len(both_fail),
            'mod_840_distribution': dict(mod_840_counts),
            'resistant_primes': type_i_resistant,
            'both_fail_primes': both_fail
        }, f, indent=2)

    print(f"\nResults saved to: {output_file}")

if __name__ == "__main__":
    main()
