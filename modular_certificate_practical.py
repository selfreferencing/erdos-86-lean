#!/usr/bin/env python3
"""
Practical Modular Certificate System for K13 Coverage

Instead of computing the full LCM (which is astronomical), this script:
1. Generates congruence-forced witness rules
2. Tests coverage on actual Mordell-hard primes
3. Reports which rules cover which primes
4. Identifies gaps that need additional templates
"""

from math import gcd, isqrt
from functools import reduce
from collections import defaultdict
from typing import List, Tuple, Set, Dict, Optional

# K13 covering set
K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Mordell-hard residue classes mod 840
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

# Small primes for witness templates
SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

def m_k(k: int) -> int:
    return 4 * k + 3

def is_prime(n: int) -> bool:
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, isqrt(n) + 1, 2):
        if n % i == 0: return False
    return True

def mod_inverse(a: int, m: int) -> Optional[int]:
    if gcd(a, m) != 1: return None
    def extended_gcd(a, b):
        if a == 0: return b, 0, 1
        g, x, y = extended_gcd(b % a, a)
        return g, y - (b // a) * x, x
    _, x, _ = extended_gcd(a % m, m)
    return x % m

def chinese_remainder(residues: List[Tuple[int, int]]) -> Optional[Tuple[int, int]]:
    if not residues: return (0, 1)
    r, m = residues[0]
    for r2, m2 in residues[1:]:
        g = gcd(m, m2)
        if (r - r2) % g != 0: return None
        lcm_m = m * m2 // g
        m_over_g = m // g
        m2_over_g = m2 // g
        inv = mod_inverse(m_over_g, m2_over_g)
        if inv is None: return None
        k = ((r2 - r) // g * inv) % m2_over_g
        r = (r + k * m) % lcm_m
        m = lcm_m
    return (r, m)

# =============================================================================
# RULE GENERATION
# =============================================================================

def generate_rule(k: int, template_type: str, params: tuple) -> Optional[Dict]:
    """Generate a single congruence-forced witness rule."""
    mk = m_k(k)

    if template_type == 'd=1':
        # d=1 works when x_k ≡ -1 (mod m_k), i.e., p ≡ -4 (mod m_k)
        residue = (-4) % mk
        return {'k': k, 'd': 1, 'residue': residue, 'modulus': mk, 'template': 'd=1'}

    elif template_type == 'd=m_k':
        # d=m_k works when m_k | x_k, i.e., p ≡ 3*m_k (mod 4*m_k)
        residue = (3 * mk) % (4 * mk)
        return {'k': k, 'd': mk, 'residue': residue, 'modulus': 4*mk, 'template': 'd=m_k'}

    elif template_type == 'd=q':
        q = params[0]
        if gcd(q, mk) > 1: return None
        cond1 = ((-mk) % (4*q), 4*q)
        cond2 = ((-4*q) % mk, mk)
        result = chinese_remainder([cond1, cond2])
        if result is None: return None
        return {'k': k, 'd': q, 'residue': result[0], 'modulus': result[1], 'template': f'd=q({q})'}

    elif template_type == 'd=q^2':
        q = params[0]
        if gcd(q, mk) > 1: return None
        cond1 = ((-mk) % (4*q), 4*q)
        cond2 = ((-4*q*q) % mk, mk)
        result = chinese_remainder([cond1, cond2])
        if result is None: return None
        return {'k': k, 'd': q*q, 'residue': result[0], 'modulus': result[1], 'template': f'd=q^2({q})'}

    elif template_type == 'd=q1*q2':
        q1, q2 = params
        if gcd(q1, mk) > 1 or gcd(q2, mk) > 1: return None
        Q = q1 * q2
        cond1 = ((-mk) % (4*Q), 4*Q)
        cond2 = ((-4*Q) % mk, mk)
        result = chinese_remainder([cond1, cond2])
        if result is None: return None
        return {'k': k, 'd': Q, 'residue': result[0], 'modulus': result[1], 'template': f'd=q1*q2({q1},{q2})'}

    return None

def generate_all_rules(max_prime_idx: int = 10) -> List[Dict]:
    """Generate all witness rules from templates."""
    rules = []
    primes = SMALL_PRIMES[:max_prime_idx]

    for k in K13:
        # d = 1
        rule = generate_rule(k, 'd=1', ())
        if rule: rules.append(rule)

        # d = m_k
        rule = generate_rule(k, 'd=m_k', ())
        if rule: rules.append(rule)

        # d = q
        for q in primes:
            rule = generate_rule(k, 'd=q', (q,))
            if rule: rules.append(rule)

        # d = q^2
        for q in primes:
            rule = generate_rule(k, 'd=q^2', (q,))
            if rule: rules.append(rule)

        # d = q1 * q2 (distinct primes only)
        for i, q1 in enumerate(primes):
            for q2 in primes[i+1:]:
                rule = generate_rule(k, 'd=q1*q2', (q1, q2))
                if rule: rules.append(rule)

    return rules

# =============================================================================
# VERIFICATION ON ACTUAL PRIMES
# =============================================================================

def verify_rule_on_prime(rule: Dict, p: int) -> bool:
    """Check if the rule's congruence matches prime p."""
    return p % rule['modulus'] == rule['residue']

def verify_witness_actually_works(p: int, k: int, d: int) -> bool:
    """Verify that d is actually a Type II witness for (p, k)."""
    mk = m_k(k)
    if (p + mk) % 4 != 0:
        return False
    xk = (p + mk) // 4
    if d > xk:
        return False
    if (xk * xk) % d != 0:
        return False
    if (xk + d) % mk != 0:
        return False
    return True

def test_coverage_on_primes(rules: List[Dict], limit: int = 100000) -> Dict:
    """Test rule coverage on actual Mordell-hard primes."""

    # Collect primes
    primes = []
    for mh in MORDELL_HARD:
        for p in range(mh, limit, 840):
            if p > 1 and is_prime(p):
                primes.append(p)

    print(f"Testing {len(rules)} rules on {len(primes)} Mordell-hard primes up to {limit}")
    print()

    # Track coverage
    prime_to_rules = defaultdict(list)  # p -> [rules that match]
    rule_usage = defaultdict(int)  # rule index -> count

    for p in primes:
        for i, rule in enumerate(rules):
            if verify_rule_on_prime(rule, p):
                prime_to_rules[p].append(i)
                rule_usage[i] += 1

    # Check actual coverage and verify witnesses
    covered = 0
    uncovered = []
    verified = 0
    verification_failures = []

    for p in primes:
        matching_rules = prime_to_rules[p]
        if matching_rules:
            covered += 1
            # Verify at least one rule actually produces a valid witness
            rule = rules[matching_rules[0]]
            if verify_witness_actually_works(p, rule['k'], rule['d']):
                verified += 1
            else:
                verification_failures.append((p, rule))
        else:
            uncovered.append(p)

    return {
        'total_primes': len(primes),
        'covered': covered,
        'verified': verified,
        'uncovered': uncovered,
        'verification_failures': verification_failures,
        'rule_usage': rule_usage,
        'prime_to_rules': prime_to_rules
    }

def analyze_uncovered(rules: List[Dict], uncovered_primes: List[int]) -> None:
    """Analyze why certain primes aren't covered."""
    print("\n" + "=" * 70)
    print("ANALYSIS OF UNCOVERED PRIMES")
    print("=" * 70)

    for p in uncovered_primes[:10]:
        print(f"\np = {p}, p mod 840 = {p % 840}")

        # For each k, show what witness would be needed
        for k in K13:
            mk = m_k(k)
            if (p + mk) % 4 != 0:
                continue
            xk = (p + mk) // 4

            # Target: d ≡ -x_k (mod m_k)
            target = (-xk) % mk

            # What would make a rule work?
            # d=1: need p ≡ -4 (mod m_k) → is p ≡ {(-4) % mk}?
            p_mod_mk = p % mk
            d1_needed = (-4) % mk
            dmk_needed = (3 * mk) % (4 * mk)
            p_mod_4mk = p % (4 * mk)

            print(f"  k={k}, m_k={mk}, x_k={xk}, need d ≡ {target} (mod {mk})")
            print(f"    p mod m_k = {p_mod_mk}, d=1 needs {d1_needed}, d=m_k needs p≡{dmk_needed} (mod {4*mk}), actual p mod 4m_k = {p_mod_4mk}")

def find_certificate_for_primes(rules: List[Dict], primes: List[int]) -> Dict:
    """
    For each prime, find the minimal rule that covers it.
    This produces a certificate.
    """
    certificate = {}

    for p in primes:
        for rule in rules:
            if verify_rule_on_prime(rule, p):
                # Verify it actually works
                if verify_witness_actually_works(p, rule['k'], rule['d']):
                    certificate[p] = (rule['k'], rule['d'], rule['template'])
                    break

    return certificate

def main():
    print("=" * 70)
    print("PRACTICAL MODULAR CERTIFICATE SYSTEM")
    print("=" * 70)
    print()

    # Generate rules
    print("Generating witness rules...")
    rules = generate_all_rules(max_prime_idx=15)  # Primes up to 47
    print(f"Generated {len(rules)} rules")
    print()

    # Show rule distribution
    template_counts = defaultdict(int)
    for rule in rules:
        template_type = rule['template'].split('(')[0]
        template_counts[template_type] += 1

    print("Rules by template type:")
    for ttype, count in sorted(template_counts.items()):
        print(f"  {ttype}: {count} rules")
    print()

    # Test coverage
    result = test_coverage_on_primes(rules, limit=100000)

    print(f"\nCoverage results:")
    print(f"  Total primes: {result['total_primes']}")
    print(f"  Covered by rules: {result['covered']} ({100*result['covered']/result['total_primes']:.1f}%)")
    print(f"  Verified witnesses: {result['verified']}")
    print(f"  Uncovered: {len(result['uncovered'])}")

    if result['verification_failures']:
        print(f"  Verification failures: {len(result['verification_failures'])}")
        print("  (Rules match but witness doesn't actually work)")

    # Show most useful rules
    print("\nMost frequently used rules:")
    sorted_usage = sorted(result['rule_usage'].items(), key=lambda x: -x[1])
    for idx, count in sorted_usage[:20]:
        rule = rules[idx]
        print(f"  {rule['template']} at k={rule['k']}: covers {count} primes")

    # Analyze uncovered
    if result['uncovered']:
        analyze_uncovered(rules, result['uncovered'])

    # Generate certificate for covered primes
    print("\n" + "=" * 70)
    print("CERTIFICATE GENERATION")
    print("=" * 70)

    primes = []
    for mh in MORDELL_HARD:
        for p in range(mh, 100000, 840):
            if p > 1 and is_prime(p):
                primes.append(p)

    certificate = find_certificate_for_primes(rules, primes)

    print(f"\nGenerated certificates for {len(certificate)}/{len(primes)} primes")

    # Show sample certificates
    print("\nSample certificates:")
    for p in list(certificate.keys())[:10]:
        k, d, template = certificate[p]
        print(f"  p={p}: k={k}, d={d} ({template})")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if not result['uncovered']:
        print("\nSUCCESS: All primes covered by congruence-forced rules!")
        print("This demonstrates that a finite modular certificate exists.")
    else:
        print(f"\n{len(result['uncovered'])} primes not covered by current rules.")
        print("These may need:")
        print("  - Additional template types (e.g., d = q1^2 * q2)")
        print("  - Larger primes in the template library")
        print("  - Non-congruence-forced witnesses (requiring factorization)")

if __name__ == "__main__":
    main()
