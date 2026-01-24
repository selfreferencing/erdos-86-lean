#!/usr/bin/env python3
"""
Certificate Verification for K13 Coverage

Instead of computing the (enormous) master modulus, this script:
1. Tests templates directly on Mordell-hard primes
2. Finds which templates cover which primes
3. Verifies 100% coverage empirically

Key insight from GPT1/GPT2: Each template (k, d) defines a congruence class.
We verify coverage by testing on actual primes.
"""

from math import gcd, isqrt
from collections import defaultdict
from typing import List, Tuple, Set, Dict, Optional

# K13 covering set
K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Mordell-hard residue classes mod 840
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

def m_k(k: int) -> int:
    """The modulus m_k = 4k + 3"""
    return 4 * k + 3

def x_k(p: int, k: int) -> int:
    """Compute x_k = (p + m_k) / 4"""
    mk = m_k(k)
    if (p + mk) % 4 != 0:
        return -1
    return (p + mk) // 4

def is_type_ii_witness(x: int, m: int, d: int) -> bool:
    """Check if d is a Type II witness for (x, m)"""
    if d <= 0 or x <= 0 or m <= 0:
        return False
    if d > x:
        return False
    if (x * x) % d != 0:
        return False
    if (x + d) % m != 0:
        return False
    return True

def is_prime(n: int) -> bool:
    """Simple primality test"""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, isqrt(n) + 1, 2):
        if n % i == 0:
            return False
    return True

def find_witness_divisor_pair(p: int, k: int) -> Optional[Tuple[int, int, int]]:
    """
    Find witness using divisor-pair lemma (GPT1).

    Returns (d, a, b) where d is the witness and a, b are the divisor pair.
    """
    mk = m_k(k)
    xk = x_k(p, k)
    if xk <= 0:
        return None

    # Find divisors of x_k
    divisors = []
    i = 1
    while i * i <= xk:
        if xk % i == 0:
            divisors.append(i)
            if i != xk // i:
                divisors.append(xk // i)
        i += 1
    divisors.sort()

    # Look for divisor pair (a, b) with a + b ≡ 0 (mod m_k) and a ≤ b
    for a in divisors:
        for b in divisors:
            if a <= b and (a + b) % mk == 0:
                # Witness is d = x_k * a / b
                if (xk * a) % b == 0:
                    d = (xk * a) // b
                    if is_type_ii_witness(xk, mk, d):
                        return (d, a, b)

    return None

def analyze_template_coverage(limit: int = 50000, verbose: bool = True) -> Dict:
    """
    Analyze which (k, d) templates cover which primes.

    Returns statistics on template usage.
    """
    print(f"Analyzing template coverage for Mordell-hard primes up to {limit}")
    print("=" * 70)

    # Collect all Mordell-hard primes
    primes = []
    for mh in MORDELL_HARD:
        for p in range(mh, limit, 840):
            if p > 1 and is_prime(p):
                primes.append(p)

    print(f"Found {len(primes)} Mordell-hard primes")

    # Track which templates are used
    template_usage = defaultdict(list)  # (k, d) -> [primes]
    prime_coverage = {}  # p -> (k, d, a, b)
    uncovered = []

    for p in primes:
        found = False
        for k in K13:
            result = find_witness_divisor_pair(p, k)
            if result:
                d, a, b = result
                template_usage[(k, d)].append(p)
                prime_coverage[p] = (k, d, a, b)
                found = True
                break
        if not found:
            uncovered.append(p)

    print(f"\nCoverage: {len(prime_coverage)}/{len(primes)} primes")
    print(f"Uncovered: {len(uncovered)}")

    if uncovered:
        print(f"Uncovered primes: {uncovered[:10]}...")

    # Analyze template distribution
    print(f"\nUnique templates used: {len(template_usage)}")

    # Most frequently used templates
    sorted_templates = sorted(template_usage.items(), key=lambda x: -len(x[1]))

    print("\nTop 20 most-used templates:")
    for (k, d), covered_primes in sorted_templates[:20]:
        mk = m_k(k)
        print(f"  (k={k}, d={d}, m_k={mk}): covers {len(covered_primes)} primes")

    # Analyze by k
    print("\nCoverage by k value:")
    k_coverage = defaultdict(int)
    for (k, d), covered_primes in template_usage.items():
        k_coverage[k] += len(covered_primes)

    for k in K13:
        print(f"  k={k} (m_k={m_k(k)}): {k_coverage[k]} primes")

    return {
        'template_usage': dict(template_usage),
        'prime_coverage': prime_coverage,
        'uncovered': uncovered,
        'total_primes': len(primes)
    }

def analyze_small_witnesses(limit: int = 50000) -> None:
    """
    Focus on templates with small d values that might form a finite covering.
    """
    print("\n" + "=" * 70)
    print("SMALL WITNESS ANALYSIS")
    print("=" * 70)

    # Collect primes
    primes = []
    for mh in MORDELL_HARD:
        for p in range(mh, limit, 840):
            if p > 1 and is_prime(p):
                primes.append(p)

    # For each prime, find the smallest witness
    witness_distribution = defaultdict(int)
    max_witness = 0
    max_witness_prime = 0

    for p in primes:
        smallest = None
        for k in K13:
            result = find_witness_divisor_pair(p, k)
            if result:
                d, a, b = result
                if smallest is None or d < smallest:
                    smallest = d

        if smallest:
            witness_distribution[smallest] += 1
            if smallest > max_witness:
                max_witness = smallest
                max_witness_prime = p

    print(f"\nSmallest witness distribution (for {len(primes)} primes):")

    # Group by witness size
    by_size = defaultdict(int)
    for d, count in witness_distribution.items():
        if d <= 10:
            by_size['1-10'] += count
        elif d <= 50:
            by_size['11-50'] += count
        elif d <= 100:
            by_size['51-100'] += count
        elif d <= 500:
            by_size['101-500'] += count
        else:
            by_size['500+'] += count

    for range_name in ['1-10', '11-50', '51-100', '101-500', '500+']:
        pct = 100 * by_size[range_name] / len(primes)
        print(f"  d in {range_name}: {by_size[range_name]} ({pct:.1f}%)")

    print(f"\nLargest witness needed: d={max_witness} for p={max_witness_prime}")

    # Show specific small witness counts
    print("\nSpecific small witnesses:")
    for d in sorted(witness_distribution.keys())[:30]:
        print(f"  d={d}: {witness_distribution[d]} primes")

def check_congruence_patterns(limit: int = 50000) -> None:
    """
    Check if witness values follow predictable congruence patterns.
    """
    print("\n" + "=" * 70)
    print("CONGRUENCE PATTERN ANALYSIS")
    print("=" * 70)

    # Collect primes with their witnesses
    witness_data = []

    for mh in MORDELL_HARD:
        for p in range(mh, limit, 840):
            if p > 1 and is_prime(p):
                for k in K13:
                    result = find_witness_divisor_pair(p, k)
                    if result:
                        d, a, b = result
                        mk = m_k(k)
                        witness_data.append({
                            'p': p,
                            'p_mod840': p % 840,
                            'k': k,
                            'd': d,
                            'm_k': mk,
                            'a': a,
                            'b': b
                        })
                        break

    # For each (Mordell-hard class, k), analyze witness patterns
    print("\nWitness patterns by (Mordell-hard class, k):")

    for mh in MORDELL_HARD:
        for k in K13:
            matching = [w for w in witness_data if w['p_mod840'] == mh and w['k'] == k]
            if matching:
                # Check what witnesses appear
                witness_counts = defaultdict(int)
                for w in matching:
                    witness_counts[w['d']] += 1

                # If there's a dominant witness, report it
                if witness_counts:
                    top_witness = max(witness_counts.items(), key=lambda x: x[1])
                    if top_witness[1] >= len(matching) * 0.8:  # 80%+ use same witness
                        print(f"  ({mh}, k={k}): {len(matching)} primes, witness d={top_witness[0]} ({top_witness[1]}/{len(matching)})")

def main():
    print("Certificate Verification for K13 Coverage")
    print("=" * 70)

    # Run analyses
    result = analyze_template_coverage(limit=100000, verbose=True)

    analyze_small_witnesses(limit=100000)

    check_congruence_patterns(limit=50000)

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total primes tested: {result['total_primes']}")
    print(f"Covered: {len(result['prime_coverage'])}")
    print(f"Uncovered: {len(result['uncovered'])}")
    print(f"Unique templates: {len(result['template_usage'])}")

    if not result['uncovered']:
        print("\nSUCCESS: 100% coverage achieved!")
    else:
        print(f"\nWARNING: {len(result['uncovered'])} primes not covered")

if __name__ == "__main__":
    main()
