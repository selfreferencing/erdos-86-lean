#!/usr/bin/env python3
"""
Certificate Covering System for K13 Coverage

Implements the GPT1/GPT2 approach:
- Each template (k, d) defines a congruence class on p
- Find a finite set of templates that cover all Mordell-hard residue classes

Key lemmas used:
- Lemma B: d ≡ -x_k (mod m_k) ⟺ p ≡ -4d (mod m_k)
- Lemma D: d | x_k² ⟺ for each q^e || d: q^⌈e/2⌉ | x_k ⟺ p ≡ -m_k (mod 4q^⌈e/2⌉)
"""

from math import gcd, lcm, isqrt
from functools import reduce
from collections import defaultdict
from typing import List, Tuple, Set, Dict, Optional

# K13 covering set
K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Mordell-hard residue classes mod 840
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

def m_k(k: int) -> int:
    """The modulus m_k = 4k + 3"""
    return 4 * k + 3

def prime_factorization(n: int) -> Dict[int, int]:
    """Return prime factorization as {prime: exponent}"""
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

def mod_inverse(a: int, m: int) -> Optional[int]:
    """Compute modular inverse of a mod m, or None if not coprime"""
    if gcd(a, m) != 1:
        return None
    # Extended Euclidean algorithm
    def extended_gcd(a, b):
        if a == 0:
            return b, 0, 1
        g, x, y = extended_gcd(b % a, a)
        return g, y - (b // a) * x, x

    _, x, _ = extended_gcd(a % m, m)
    return x % m

def chinese_remainder(residues: List[Tuple[int, int]]) -> Tuple[int, int]:
    """
    Chinese Remainder Theorem: solve system of congruences
    residues = [(r1, m1), (r2, m2), ...] meaning x ≡ ri (mod mi)
    Returns (r, M) where x ≡ r (mod M) and M = lcm(m1, m2, ...)
    Returns None if no solution exists
    """
    if not residues:
        return (0, 1)

    r, m = residues[0]
    for r2, m2 in residues[1:]:
        g = gcd(m, m2)
        if (r - r2) % g != 0:
            return None  # No solution

        # Combine congruences
        lcm_m = m * m2 // g
        # Need to find x ≡ r (mod m) and x ≡ r2 (mod m2)
        # x = r + k*m for some k, need r + k*m ≡ r2 (mod m2)
        # k*m ≡ r2 - r (mod m2)
        # k ≡ (r2 - r) * (m/g)^{-1} (mod m2/g)
        m_over_g = m // g
        m2_over_g = m2 // g
        inv = mod_inverse(m_over_g, m2_over_g)
        if inv is None:
            return None
        k = ((r2 - r) // g * inv) % m2_over_g
        r = (r + k * m) % lcm_m
        m = lcm_m

    return (r, m)

def template_congruence(k: int, d: int) -> Optional[Tuple[int, int]]:
    """
    For template (k, d), compute the congruence class on p.

    Returns (residue, modulus) such that if p ≡ residue (mod modulus),
    then d is a valid Type II witness for x_k.

    Conditions:
    1. d ≡ -x_k (mod m_k) ⟺ p ≡ -4d (mod m_k)
    2. d | x_k² ⟺ for each q^e || d: p ≡ -m_k (mod 4*q^⌈e/2⌉)
    """
    mk = m_k(k)

    # Condition 1: p ≡ -4d (mod m_k)
    cond1 = ((-4 * d) % mk, mk)

    # Condition 2: For each prime power in d's factorization
    factors = prime_factorization(d)
    conditions = [cond1]

    for q, e in factors.items():
        t = (e + 1) // 2  # ceiling of e/2
        modulus = 4 * (q ** t)
        residue = (-mk) % modulus
        conditions.append((residue, modulus))

    # Combine via CRT
    result = chinese_remainder(conditions)
    return result

def is_admissible_residue(r: int, M: int) -> bool:
    """
    Check if residue r mod M is admissible:
    - r mod 840 is Mordell-hard
    - gcd(r, M) = 1 (so r can be a prime)
    """
    if r % 840 not in MORDELL_HARD:
        return False
    if gcd(r, M) != 1:
        return False
    return True

def generate_candidate_witnesses(max_d: int = 100, squarefree_only: bool = False) -> List[int]:
    """Generate candidate witness values d"""
    candidates = []
    for d in range(1, max_d + 1):
        if squarefree_only:
            factors = prime_factorization(d)
            if any(e > 1 for e in factors.values()):
                continue
        candidates.append(d)
    return candidates

def find_covering_system(max_d: int = 100, verbose: bool = True) -> Dict:
    """
    Find a covering system of templates that covers all Mordell-hard residue classes.

    Returns dict with:
    - 'templates': list of (k, d) pairs
    - 'M': the master modulus
    - 'coverage': dict mapping residue -> template that covers it
    - 'uncovered': list of uncovered residues
    """
    candidates = generate_candidate_witnesses(max_d)

    # Generate all templates and their congruences
    templates = []
    for k in K13:
        mk = m_k(k)
        for d in candidates:
            cong = template_congruence(k, d)
            if cong is not None:
                r, N = cong
                templates.append({
                    'k': k,
                    'd': d,
                    'm_k': mk,
                    'residue': r,
                    'modulus': N
                })

    if verbose:
        print(f"Generated {len(templates)} templates from {len(K13)} k-values and {len(candidates)} d-values")

    # Compute master modulus M
    moduli = [t['modulus'] for t in templates]
    M = reduce(lcm, [840] + moduli)

    if verbose:
        print(f"Master modulus M = {M}")
        print(f"M has {len(str(M))} digits")

    # Find all admissible residue classes mod M
    # This could be huge, so we sample or iterate smartly
    # For now, iterate through Mordell-hard classes and lift to mod M

    admissible = []
    for mh in MORDELL_HARD:
        # All r ≡ mh (mod 840) with gcd(r, M) = 1
        for r in range(mh, M, 840):
            if gcd(r, M) == 1:
                admissible.append(r)

    if verbose:
        print(f"Found {len(admissible)} admissible residue classes mod M")

    # Check coverage
    coverage = {}
    uncovered = []

    for r in admissible:
        covered = False
        for t in templates:
            # Check if r ≡ t['residue'] (mod t['modulus'])
            if r % t['modulus'] == t['residue']:
                coverage[r] = (t['k'], t['d'])
                covered = True
                break
        if not covered:
            uncovered.append(r)

    if verbose:
        print(f"Covered: {len(coverage)} / {len(admissible)}")
        print(f"Uncovered: {len(uncovered)}")
        if uncovered and len(uncovered) <= 20:
            print(f"Uncovered residues: {uncovered}")

    return {
        'templates': templates,
        'M': M,
        'coverage': coverage,
        'uncovered': uncovered,
        'admissible_count': len(admissible)
    }

def verify_template(k: int, d: int, p: int) -> bool:
    """Verify that template (k, d) actually works for prime p"""
    mk = m_k(k)
    xk = (p + mk) // 4

    if (p + mk) % 4 != 0:
        return False

    # Check: d | x_k², d ≤ x_k, (x_k + d) ≡ 0 (mod m_k)
    if (xk * xk) % d != 0:
        return False
    if d > xk:
        return False
    if (xk + d) % mk != 0:
        return False

    return True

def test_coverage_on_primes(result: Dict, limit: int = 10000) -> None:
    """Test that the covering system actually works on real primes"""
    print(f"\n{'='*60}")
    print(f"Testing coverage on Mordell-hard primes up to {limit}")
    print('='*60)

    def is_prime(n):
        if n < 2: return False
        if n == 2: return True
        if n % 2 == 0: return False
        for i in range(3, isqrt(n) + 1, 2):
            if n % i == 0: return False
        return True

    M = result['M']
    coverage = result['coverage']

    tested = 0
    covered = 0
    failed = []

    for mh in MORDELL_HARD:
        for p in range(mh, limit, 840):
            if p < 2 or not is_prime(p):
                continue
            tested += 1

            r = p % M
            if r in coverage:
                k, d = coverage[r]
                if verify_template(k, d, p):
                    covered += 1
                else:
                    failed.append((p, k, d, 'template verification failed'))
            else:
                # Check if any template works
                found = False
                for t in result['templates']:
                    if p % t['modulus'] == t['residue']:
                        if verify_template(t['k'], t['d'], p):
                            covered += 1
                            found = True
                            break
                if not found:
                    failed.append((p, None, None, 'no template matched'))

    print(f"Tested: {tested} primes")
    print(f"Covered by templates: {covered}")
    print(f"Failed: {len(failed)}")
    if failed and len(failed) <= 10:
        for p, k, d, reason in failed:
            print(f"  p={p}: {reason}")

def analyze_small_modulus(max_d: int = 50) -> None:
    """
    Analyze with smaller modulus to understand the structure.
    Focus on coverage mod 840 first.
    """
    print("="*60)
    print(f"SMALL MODULUS ANALYSIS (max_d={max_d})")
    print("="*60)

    candidates = generate_candidate_witnesses(max_d)

    # For each Mordell-hard class, find which templates cover it
    for mh in MORDELL_HARD:
        print(f"\nMordell-hard class {mh} mod 840:")

        covering_templates = []
        for k in K13:
            mk = m_k(k)
            for d in candidates:
                # Check if template (k, d) covers this class
                # Need: mh ≡ -4d (mod gcd(840, m_k))
                g = gcd(840, mk)
                if mh % g == (-4 * d) % g:
                    # Also check the full CRT condition
                    cong = template_congruence(k, d)
                    if cong is not None:
                        r, N = cong
                        # Does this template potentially cover mh mod 840?
                        if r % gcd(N, 840) == mh % gcd(N, 840):
                            covering_templates.append((k, d, N))

        # Show first few
        print(f"  {len(covering_templates)} potential templates")
        for k, d, N in covering_templates[:5]:
            print(f"    k={k} (m_k={m_k(k)}), d={d}, modulus N={N}")

def main():
    print("Certificate Covering System Analysis")
    print("="*60)

    # Start with small analysis
    analyze_small_modulus(max_d=30)

    # Try to find actual covering
    print("\n" + "="*60)
    print("SEARCHING FOR COVERING SYSTEM")
    print("="*60)

    for max_d in [20, 50, 100]:
        print(f"\nTrying max_d = {max_d}:")
        result = find_covering_system(max_d=max_d, verbose=True)

        if not result['uncovered']:
            print("COMPLETE COVERAGE FOUND!")
            test_coverage_on_primes(result, limit=50000)
            break
        else:
            print(f"Coverage incomplete. {len(result['uncovered'])} gaps remain.")

if __name__ == "__main__":
    main()
