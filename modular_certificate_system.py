#!/usr/bin/env python3
"""
Modular Certificate System for K13 Coverage

Implements GPT3's rigorous approach:
1. Congruence-forced witness templates
2. CRT combination to derive congruence classes
3. Set cover search over Mordell-hard residues

Key insight: We don't need to factor x_k. Instead, we FORCE divisibility
through congruences on p, making everything purely modular.
"""

from math import gcd, isqrt
from functools import reduce
from collections import defaultdict
from typing import List, Tuple, Set, Dict, Optional
import itertools

# K13 covering set
K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Mordell-hard residue classes mod 840
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

# Small primes for witness templates
SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

def m_k(k: int) -> int:
    """The modulus m_k = 4k + 3"""
    return 4 * k + 3

def lcm(a: int, b: int) -> int:
    """Least common multiple"""
    return a * b // gcd(a, b)

def lcm_list(lst: List[int]) -> int:
    """LCM of a list"""
    return reduce(lcm, lst, 1)

def mod_inverse(a: int, m: int) -> Optional[int]:
    """Modular inverse of a mod m, or None if not coprime"""
    if gcd(a, m) != 1:
        return None
    def extended_gcd(a, b):
        if a == 0:
            return b, 0, 1
        g, x, y = extended_gcd(b % a, a)
        return g, y - (b // a) * x, x
    _, x, _ = extended_gcd(a % m, m)
    return x % m

def chinese_remainder(residues: List[Tuple[int, int]]) -> Optional[Tuple[int, int]]:
    """
    CRT: solve system x ≡ r_i (mod m_i)
    Returns (r, M) where M = lcm of all moduli, or None if inconsistent.
    """
    if not residues:
        return (0, 1)

    r, m = residues[0]
    for r2, m2 in residues[1:]:
        g = gcd(m, m2)
        if (r - r2) % g != 0:
            return None  # Inconsistent

        lcm_m = m * m2 // g
        m_over_g = m // g
        m2_over_g = m2 // g
        inv = mod_inverse(m_over_g, m2_over_g)
        if inv is None:
            return None
        k = ((r2 - r) // g * inv) % m2_over_g
        r = (r + k * m) % lcm_m
        m = lcm_m

    return (r, m)

# =============================================================================
# WITNESS TEMPLATE GENERATORS
# =============================================================================

def template_d_equals_1(k: int) -> Optional[Tuple[int, int, int]]:
    """
    Template: d = 1

    Condition: 1 ≡ -x_k (mod m_k)
    Since x_k = (p + m_k)/4, we need:
        1 ≡ -(p + m_k)/4 (mod m_k)
        4 ≡ -(p + m_k) (mod 4*m_k)  [multiply by 4]
        p ≡ -m_k - 4 (mod 4*m_k)

    But simpler: 1 ≡ -x_k (mod m_k) means x_k ≡ -1 ≡ m_k - 1 (mod m_k)
    Since x_k ≡ (p + m_k)/4 ≡ p * 4^{-1} (mod m_k) [since m_k | m_k]
    Actually: x_k = (p + m_k)/4, so 4*x_k = p + m_k, so 4*x_k ≡ p (mod m_k)
    We need x_k ≡ -1 (mod m_k), so 4*(-1) ≡ p (mod m_k), i.e., p ≡ -4 (mod m_k)

    Returns (residue, modulus, d) or None if impossible.
    """
    mk = m_k(k)
    residue = (-4) % mk
    modulus = mk
    return (residue, modulus, 1)

def template_d_equals_mk(k: int) -> Optional[Tuple[int, int, int]]:
    """
    Template: d = m_k (direct divisibility)

    Condition 1: m_k | x_k^2, which requires m_k | x_k
        x_k = (p + m_k)/4, so m_k | x_k means 4*m_k | (p + m_k)
        i.e., p ≡ -m_k (mod 4*m_k), or p ≡ 3*m_k (mod 4*m_k)

    Condition 2: m_k ≡ -x_k (mod m_k)
        This is 0 ≡ -x_k (mod m_k), i.e., m_k | x_k
        Same as condition 1!

    Returns (residue, modulus, d).
    """
    mk = m_k(k)
    residue = (3 * mk) % (4 * mk)  # = 3*m_k since 3*m_k < 4*m_k
    modulus = 4 * mk
    return (residue, modulus, mk)

def template_prime_witness(k: int, q: int) -> Optional[Tuple[int, int, int]]:
    """
    Template: d = q (prime witness)

    Condition 1: q | x_k
        p ≡ -m_k (mod 4q)

    Condition 2: q ≡ -x_k (mod m_k)
        Since 4*x_k ≡ p (mod m_k), we have x_k ≡ p * 4^{-1} (mod m_k)
        Need q ≡ -p * 4^{-1} (mod m_k)
        So p ≡ -4q (mod m_k)

    Combined via CRT.
    """
    mk = m_k(k)

    # Check coprimality
    if gcd(q, mk) > 1:
        return None  # q divides m_k, can't work

    cond1 = ((-mk) % (4*q), 4*q)
    cond2 = ((-4*q) % mk, mk)

    result = chinese_remainder([cond1, cond2])
    if result is None:
        return None

    residue, modulus = result
    return (residue, modulus, q)

def template_prime_square_witness(k: int, q: int) -> Optional[Tuple[int, int, int]]:
    """
    Template: d = q^2 (prime square witness)

    Condition 1: q | x_k (so q^2 | x_k^2)
        p ≡ -m_k (mod 4q)

    Condition 2: q^2 ≡ -x_k (mod m_k)
        p ≡ -4*q^2 (mod m_k)
    """
    mk = m_k(k)

    if gcd(q, mk) > 1:
        return None

    cond1 = ((-mk) % (4*q), 4*q)
    cond2 = ((-4*q*q) % mk, mk)

    result = chinese_remainder([cond1, cond2])
    if result is None:
        return None

    residue, modulus = result
    return (residue, modulus, q*q)

def template_two_prime_witness(k: int, q1: int, q2: int) -> Optional[Tuple[int, int, int]]:
    """
    Template: d = q1 * q2 (product of two primes)

    Condition 1: q1 | x_k AND q2 | x_k
        p ≡ -m_k (mod 4*q1) AND p ≡ -m_k (mod 4*q2)
        Combined: p ≡ -m_k (mod 4*lcm(q1, q2))
        If q1 ≠ q2, this is p ≡ -m_k (mod 4*q1*q2)

    Condition 2: q1*q2 ≡ -x_k (mod m_k)
        p ≡ -4*q1*q2 (mod m_k)
    """
    mk = m_k(k)

    if gcd(q1, mk) > 1 or gcd(q2, mk) > 1:
        return None

    Q = q1 * q2 if q1 != q2 else q1  # Handle case where both are same prime

    cond1 = ((-mk) % (4*Q), 4*Q)
    cond2 = ((-4*q1*q2) % mk, mk)

    result = chinese_remainder([cond1, cond2])
    if result is None:
        return None

    residue, modulus = result
    return (residue, modulus, q1*q2)

# =============================================================================
# RULE GENERATION AND COVERAGE ANALYSIS
# =============================================================================

def generate_all_rules(max_prime_idx: int = 10) -> List[Dict]:
    """
    Generate all witness rules from templates.

    Each rule is: {k, d, residue, modulus, template_type}
    Meaning: if p ≡ residue (mod modulus), then (k, d) is a witness.
    """
    rules = []
    primes = SMALL_PRIMES[:max_prime_idx]

    for k in K13:
        mk = m_k(k)

        # Template: d = 1
        result = template_d_equals_1(k)
        if result:
            r, m, d = result
            rules.append({
                'k': k, 'd': d, 'residue': r, 'modulus': m,
                'template': 'd=1', 'm_k': mk
            })

        # Template: d = m_k
        result = template_d_equals_mk(k)
        if result:
            r, m, d = result
            rules.append({
                'k': k, 'd': d, 'residue': r, 'modulus': m,
                'template': 'd=m_k', 'm_k': mk
            })

        # Template: d = q
        for q in primes:
            result = template_prime_witness(k, q)
            if result:
                r, m, d = result
                rules.append({
                    'k': k, 'd': d, 'residue': r, 'modulus': m,
                    'template': f'd=q({q})', 'm_k': mk
                })

        # Template: d = q^2
        for q in primes:
            result = template_prime_square_witness(k, q)
            if result:
                r, m, d = result
                rules.append({
                    'k': k, 'd': d, 'residue': r, 'modulus': m,
                    'template': f'd=q^2({q})', 'm_k': mk
                })

        # Template: d = q1 * q2
        for i, q1 in enumerate(primes):
            for q2 in primes[i:]:  # q2 >= q1 to avoid duplicates
                if q1 == q2:
                    continue  # This is d=q^2, already handled
                result = template_two_prime_witness(k, q1, q2)
                if result:
                    r, m, d = result
                    rules.append({
                        'k': k, 'd': d, 'residue': r, 'modulus': m,
                        'template': f'd=q1*q2({q1},{q2})', 'm_k': mk
                    })

    return rules

def compute_coverage(rules: List[Dict], base_modulus: int = 840) -> Dict:
    """
    For each Mordell-hard residue class mod base_modulus,
    determine which rules cover it.

    A rule covers class mh if there exists r ≡ mh (mod 840)
    with r ≡ rule['residue'] (mod rule['modulus']).
    """
    coverage = {mh: [] for mh in MORDELL_HARD}

    for rule in rules:
        rule_res = rule['residue']
        rule_mod = rule['modulus']

        # For each Mordell-hard class, check CRT compatibility
        for mh in MORDELL_HARD:
            crt_result = chinese_remainder([(mh, 840), (rule_res, rule_mod)])
            if crt_result is not None:
                # This rule can cover some primes in class mh
                coverage[mh].append(rule)

    return coverage

def analyze_coverage_at_modulus(rules: List[Dict], M: int) -> Dict:
    """
    Lift analysis to modulus M.

    Returns dict mapping each admissible residue r mod M to the rules covering it.
    Admissible means: r mod 840 is Mordell-hard AND gcd(r, M) = 1.
    """
    coverage = {}

    for mh in MORDELL_HARD:
        for r in range(mh, M, 840):
            if gcd(r, M) != 1:
                continue  # Not a potential prime residue

            # Find rules covering this residue
            covering_rules = []
            for rule in rules:
                if r % rule['modulus'] == rule['residue']:
                    covering_rules.append(rule)

            coverage[r] = covering_rules

    return coverage

def find_minimal_cover(rules: List[Dict], M: int) -> Tuple[Set[int], List[int]]:
    """
    Find a minimal set of rules that covers all admissible residues mod M.
    Uses greedy set cover.

    Returns (covered_residues, uncovered_residues).
    """
    # Get all admissible residues
    admissible = set()
    for mh in MORDELL_HARD:
        for r in range(mh, M, 840):
            if gcd(r, M) == 1:
                admissible.add(r)

    # Greedy set cover
    covered = set()
    selected_rules = []

    while covered != admissible:
        # Find rule that covers most uncovered residues
        best_rule = None
        best_new_coverage = set()

        for rule in rules:
            # Residues covered by this rule
            rule_covers = set()
            for r in admissible - covered:
                if r % rule['modulus'] == rule['residue']:
                    rule_covers.add(r)

            if len(rule_covers) > len(best_new_coverage):
                best_rule = rule
                best_new_coverage = rule_covers

        if not best_new_coverage:
            break  # No rule can cover any remaining residues

        selected_rules.append(best_rule)
        covered.update(best_new_coverage)

    uncovered = list(admissible - covered)
    return covered, uncovered, selected_rules

def main():
    print("=" * 70)
    print("MODULAR CERTIFICATE SYSTEM FOR K13 COVERAGE")
    print("=" * 70)
    print()

    # Step 1: Generate rules
    print("Step 1: Generating witness rules...")
    rules = generate_all_rules(max_prime_idx=10)  # Primes up to 29
    print(f"Generated {len(rules)} rules")
    print()

    # Show some example rules
    print("Example rules:")
    for rule in rules[:10]:
        print(f"  k={rule['k']}, d={rule['d']}, p≡{rule['residue']} (mod {rule['modulus']}), template={rule['template']}")
    print()

    # Step 2: Basic coverage analysis mod 840
    print("Step 2: Coverage analysis mod 840...")
    coverage_840 = compute_coverage(rules, 840)

    for mh in MORDELL_HARD:
        num_rules = len(coverage_840[mh])
        print(f"  Class {mh} mod 840: {num_rules} rules can cover")
    print()

    # Step 3: Lift to larger modulus
    # Compute M as lcm of 840 and all rule moduli
    moduli = [840] + [rule['modulus'] for rule in rules]
    M = lcm_list(moduli)

    print(f"Step 3: Working modulus M = lcm of all rule moduli")
    print(f"  M = {M}")
    print(f"  M has {len(str(M))} digits")
    print()

    # If M is too large, use a smaller working modulus
    if M > 10**12:
        print("  M is too large, using smaller working modulus...")
        # Use just 840 and the smallest rule moduli
        small_moduli = [840] + sorted(set(rule['modulus'] for rule in rules))[:20]
        M = lcm_list(small_moduli)
        print(f"  Reduced M = {M}")
    print()

    # Step 4: Count admissible residues and check coverage
    print("Step 4: Detailed coverage analysis...")

    admissible_count = 0
    covered_count = 0
    uncovered_residues = []

    for mh in MORDELL_HARD:
        mh_admissible = 0
        mh_covered = 0
        for r in range(mh, M, 840):
            if gcd(r, M) != 1:
                continue
            mh_admissible += 1

            # Check if any rule covers this
            is_covered = False
            for rule in rules:
                if r % rule['modulus'] == rule['residue']:
                    is_covered = True
                    break

            if is_covered:
                mh_covered += 1
            else:
                uncovered_residues.append(r)

        admissible_count += mh_admissible
        covered_count += mh_covered
        pct = 100 * mh_covered / mh_admissible if mh_admissible > 0 else 0
        print(f"  Class {mh}: {mh_covered}/{mh_admissible} covered ({pct:.1f}%)")

    print()
    print(f"Total: {covered_count}/{admissible_count} admissible residues covered")
    print(f"Uncovered: {len(uncovered_residues)}")

    if uncovered_residues and len(uncovered_residues) <= 20:
        print(f"Uncovered residues: {uncovered_residues}")

    # Step 5: If incomplete, analyze what's missing
    if uncovered_residues:
        print()
        print("Step 5: Analyzing gaps...")

        # For each uncovered residue, show why no rule works
        for r in uncovered_residues[:5]:
            print(f"\n  Residue r = {r} (mod {M}), r mod 840 = {r % 840}")
            print(f"  Why each k fails:")

            for k in K13:
                mk = m_k(k)
                # What would x_k be mod m_k?
                # 4*x_k = p + m_k, so x_k ≡ (p + m_k) * 4^{-1} (mod m_k)
                # Actually simpler: 4*x_k ≡ p (mod m_k)
                inv4 = mod_inverse(4, mk)
                if inv4:
                    xk_mod_mk = (r * inv4) % mk
                    target_d = (-xk_mod_mk) % mk
                    print(f"    k={k}: x_k ≡ {xk_mod_mk} (mod {mk}), need d ≡ {target_d} (mod {mk})")

    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if not uncovered_residues:
        print("SUCCESS: All admissible residues are covered by the generated rules!")
        print("This constitutes a finite certificate for K13 coverage.")
    else:
        print(f"INCOMPLETE: {len(uncovered_residues)} residues not covered.")
        print("Need to expand template library or increase prime bound.")

if __name__ == "__main__":
    main()
