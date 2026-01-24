#!/usr/bin/env python3
"""
T-Form Analysis for K13 Coverage (GPT4's Approach)

Key insight: Use t = (p+3)/4 as the base parameter.
- p = 4t - 3
- x_k = t + k (all x_k are just shifts!)
- Mordell-hard primes → t ≡ {1, 31, 43, 73, 91, 133} (mod 210)

Simplified congruence lemma:
For squarefree d coprime to m_k:
    d is witness ⟺ t ≡ -(k + d) (mod m_k·d)
"""

from math import gcd, isqrt
from functools import reduce
from collections import defaultdict
from typing import List, Tuple, Set, Dict, Optional

# K13 covering set
K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Mordell-hard residue classes in t-form (mod 210)
# Derived from p mod 840: t = (p + 3)/4, so t mod 210 = ((p mod 840) + 3)/4
MORDELL_HARD_T = [1, 31, 43, 73, 91, 133]  # (1+3)/4=1, (121+3)/4=31, etc.

# Small primes for witness templates
SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

def m_k(k: int) -> int:
    return 4 * k + 3

def is_prime(n: int) -> bool:
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, isqrt(n) + 1, 2):
        if n % i == 0: return False
    return True

def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)

def mod_inverse(a: int, m: int) -> Optional[int]:
    if gcd(a, m) != 1: return None
    def extended_gcd(a, b):
        if a == 0: return b, 0, 1
        g, x, y = extended_gcd(b % a, a)
        return g, y - (b // a) * x, x
    _, x, _ = extended_gcd(a % m, m)
    return x % m

# =============================================================================
# T-FORM WITNESS RULES
# =============================================================================

def t_form_rule(k: int, d: int) -> Optional[Tuple[int, int]]:
    """
    For squarefree d coprime to m_k:
        d is witness ⟺ t ≡ -(k + d) (mod m_k·d)

    Returns (residue, modulus) or None if incompatible.
    """
    mk = m_k(k)

    if gcd(d, mk) > 1:
        return None  # d not coprime to m_k

    modulus = mk * d
    residue = (-(k + d)) % modulus

    return (residue, modulus)

def t_form_rule_general(k: int, d: int) -> Optional[Tuple[int, int]]:
    """
    More general version using CRT.

    Conditions:
    1. d | x_k² (ensure each prime factor of d divides x_k = t + k)
    2. d ≡ -x_k (mod m_k), i.e., d ≡ -(t + k) (mod m_k)

    For d = q1^e1 * q2^e2 * ...:
    - Condition 1: t + k ≡ 0 (mod qi) for each qi | d, i.e., t ≡ -k (mod qi)
    - Condition 2: t ≡ -k - d (mod m_k)

    Combined via CRT.
    """
    mk = m_k(k)

    # Factor d into primes
    prime_factors = []
    temp = d
    i = 2
    while i * i <= temp:
        if temp % i == 0:
            prime_factors.append(i)
            while temp % i == 0:
                temp //= i
        i += 1
    if temp > 1:
        prime_factors.append(temp)

    # Check coprimality with m_k
    for q in prime_factors:
        if mk % q == 0:
            return None  # Prime factor of d divides m_k

    # Build CRT conditions
    # Condition 1: For each prime q | d, t ≡ -k (mod q)
    # Condition 2: t ≡ -(k + d) (mod m_k)

    conditions = []

    # Product of distinct prime factors
    Q = 1
    for q in prime_factors:
        Q *= q

    # t ≡ -k (mod Q)
    conditions.append(((-k) % Q, Q))

    # t ≡ -(k + d) (mod m_k)
    conditions.append(((-(k + d)) % mk, mk))

    # Combine via CRT
    if not conditions:
        return (0, 1)

    r, m = conditions[0]
    for r2, m2 in conditions[1:]:
        g = gcd(m, m2)
        if (r - r2) % g != 0:
            return None
        lcm_m = m * m2 // g
        m_over_g = m // g
        m2_over_g = m2 // g
        inv = mod_inverse(m_over_g, m2_over_g)
        if inv is None:
            return None
        k_crt = ((r2 - r) // g * inv) % m2_over_g
        r = (r + k_crt * m) % lcm_m
        m = lcm_m

    return (r, m)

def generate_t_form_rules(max_prime_idx: int = 10) -> List[Dict]:
    """Generate rules in t-form."""
    rules = []
    primes = SMALL_PRIMES[:max_prime_idx]

    for k in K13:
        mk = m_k(k)

        # d = 1 (trivial witness)
        # t ≡ -(k + 1) (mod m_k)
        rules.append({
            'k': k, 'd': 1,
            'residue': (-(k + 1)) % mk,
            'modulus': mk,
            'template': 'd=1'
        })

        # d = q (prime witness)
        for q in primes:
            result = t_form_rule(k, q)
            if result:
                r, m = result
                rules.append({
                    'k': k, 'd': q,
                    'residue': r, 'modulus': m,
                    'template': f'd=q({q})'
                })

        # d = q^2 (prime square)
        # Need q | x_k (same as d=q), and d ≡ -x_k means q^2 ≡ -(t+k) (mod m_k)
        for q in primes:
            if gcd(q, mk) > 1:
                continue
            # t ≡ -k (mod q) and t ≡ -(k + q^2) (mod m_k)
            result = t_form_rule_general(k, q*q)
            if result:
                r, m = result
                rules.append({
                    'k': k, 'd': q*q,
                    'residue': r, 'modulus': m,
                    'template': f'd=q^2({q})'
                })

        # d = q1 * q2 (two distinct primes)
        for i, q1 in enumerate(primes):
            for q2 in primes[i+1:]:
                if gcd(q1, mk) > 1 or gcd(q2, mk) > 1:
                    continue
                result = t_form_rule_general(k, q1 * q2)
                if result:
                    r, m = result
                    rules.append({
                        'k': k, 'd': q1 * q2,
                        'residue': r, 'modulus': m,
                        'template': f'd=q1*q2({q1},{q2})'
                    })

    return rules

# =============================================================================
# VERIFICATION
# =============================================================================

def verify_t_form_coverage(rules: List[Dict], t_limit: int = 125000) -> Dict:
    """
    Test coverage in t-form.
    Mordell-hard t values: t ≡ {1, 31, 43, 73, 91, 133} (mod 210)
    """
    # Collect Mordell-hard t values where p = 4t - 3 is prime
    t_values = []
    for t_mod in MORDELL_HARD_T:
        for t in range(t_mod, t_limit, 210):
            p = 4 * t - 3
            if p > 1 and is_prime(p):
                t_values.append(t)

    print(f"Found {len(t_values)} Mordell-hard t values up to {t_limit}")

    # Check coverage
    covered = 0
    uncovered = []

    for t in t_values:
        found = False
        for rule in rules:
            if t % rule['modulus'] == rule['residue']:
                found = True
                break
        if found:
            covered += 1
        else:
            uncovered.append(t)

    return {
        'total': len(t_values),
        'covered': covered,
        'uncovered': uncovered
    }

def verify_witness_works(t: int, k: int, d: int) -> bool:
    """Verify that d is actually a Type II witness at (t, k)."""
    mk = m_k(k)
    xk = t + k

    # Check d | x_k^2
    if (xk * xk) % d != 0:
        return False

    # Check d <= x_k
    if d > xk:
        return False

    # Check d ≡ -x_k (mod m_k)
    if (d + xk) % mk != 0:
        return False

    return True

def main():
    print("=" * 70)
    print("T-FORM ANALYSIS FOR K13 COVERAGE")
    print("=" * 70)
    print()

    # Verify the t-form Mordell-hard classes
    print("Mordell-hard correspondence:")
    print("  p mod 840 → t mod 210")
    p_mods = [1, 121, 169, 289, 361, 529]
    for p_mod in p_mods:
        t_mod = (p_mod + 3) // 4
        print(f"  {p_mod} → {t_mod}")
    print()

    # Generate rules
    print("Generating t-form rules...")
    rules = generate_t_form_rules(max_prime_idx=15)
    print(f"Generated {len(rules)} rules")
    print()

    # Show example rules
    print("Example rules (first 10):")
    for rule in rules[:10]:
        print(f"  k={rule['k']}, d={rule['d']}: t ≡ {rule['residue']} (mod {rule['modulus']})")
    print()

    # Test coverage
    result = verify_t_form_coverage(rules, t_limit=125000)

    print(f"Coverage results:")
    print(f"  Total t values: {result['total']}")
    print(f"  Covered: {result['covered']} ({100*result['covered']/result['total']:.1f}%)")
    print(f"  Uncovered: {len(result['uncovered'])}")

    if result['uncovered']:
        print(f"\nUncovered t values (first 10):")
        for t in result['uncovered'][:10]:
            p = 4 * t - 3
            print(f"  t={t} (p={p}, p mod 840 = {p % 840})")

    # Verify a sample rule actually works
    print("\nVerifying sample rules on actual primes...")
    verified = 0
    failed = []

    for t_mod in MORDELL_HARD_T:
        for t in range(t_mod, 10000, 210):
            p = 4 * t - 3
            if p > 1 and is_prime(p):
                for rule in rules:
                    if t % rule['modulus'] == rule['residue']:
                        if verify_witness_works(t, rule['k'], rule['d']):
                            verified += 1
                        else:
                            failed.append((t, rule))
                        break

    print(f"  Verified: {verified}")
    print(f"  Failed: {len(failed)}")
    if failed:
        print(f"  First failure: t={failed[0][0]}, rule={failed[0][1]}")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"\nThe t-form simplifies the analysis:")
    print(f"  x_k = t + k (all 13 values are just shifts)")
    print(f"  Mordell-hard ⟺ t mod 210 ∈ {{{', '.join(map(str, MORDELL_HARD_T))}}}")
    print(f"  Witness rule: t ≡ -(k + d) (mod m_k·d) for squarefree d")

if __name__ == "__main__":
    main()
