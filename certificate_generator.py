#!/usr/bin/env python3
"""
Erdős-Straus Certificate Generator

Based on the Phase 2 analysis (Prompts 22-28), this script:
1. Computes coverage rules for K13 and rescue k values
2. Uses CRT-split sparse storage for efficiency
3. Identifies uncovered residue classes
4. Generates a verifiable certificate

The goal: If |U| = 0 (no uncovered classes), ESC is PROVED.
"""

from math import gcd, isqrt
from functools import lru_cache
from collections import defaultdict
import json

# =============================================================================
# CONSTANTS
# =============================================================================

# K13: The base set of k values
K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Known rescue k values (from our analysis)
K_RESCUE = [3, 31, 39, 41]

# Additional k values to achieve complete coverage mod 840
K_ADDITIONAL = [4, 6, 13, 16, 21, 25]

# Complete K set for full coverage
K_COMPLETE = sorted(set(K13 + K_RESCUE + K_ADDITIONAL))
# K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

# The 14 known K13 failures
K13_FAILURES = [
    10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
    34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
    46936849, 48991849
]

# The unique fully trapped prime
TRAPPED_PRIME = 66032521

# Master modulus M'' and its CRT split
# M'' = 70,148,764,800 = A × B where gcd(A, B) = 1
M_DOUBLE_PRIME = 70_148_764_800
A_SPLIT = 86_400      # 2^7 × 3^3 × 5^2
B_SPLIT = 811_907     # 53 × 15319

# Small primes for witness templates
SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

# =============================================================================
# NUMBER THEORY UTILITIES
# =============================================================================

def is_prime(n):
    """Miller-Rabin primality test."""
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
    """Return list of (prime, exponent) pairs."""
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

def jacobi_symbol(a, n):
    """Compute Jacobi symbol (a/n)."""
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be positive odd")
    a = a % n
    result = 1
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in [3, 5]:
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a = a % n
    return result if n == 1 else 0

def mod_inverse(a, m):
    """Compute modular inverse of a mod m."""
    return pow(a, -1, m)

def chinese_remainder(residues, moduli):
    """
    Solve system of congruences x ≡ r_i (mod m_i).
    Returns (solution, lcm_of_moduli) or None if no solution.
    """
    if len(residues) != len(moduli):
        raise ValueError("Mismatched lengths")

    x = residues[0]
    m = moduli[0]

    for i in range(1, len(residues)):
        r2, m2 = residues[i], moduli[i]
        g = gcd(m, m2)

        if (r2 - x) % g != 0:
            return None  # No solution

        lcm_m = m * m2 // g
        # Solve x ≡ x (mod m) and x ≡ r2 (mod m2)
        # x = x + m * k where m*k ≡ (r2 - x) (mod m2)
        m_inv = mod_inverse(m // g, m2 // g)
        k = ((r2 - x) // g * m_inv) % (m2 // g)
        x = (x + m * k) % lcm_m
        m = lcm_m

    return (x, m)

def divisors_of_square(n):
    """Return all divisors of n²."""
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

# =============================================================================
# WITNESS CHECKING
# =============================================================================

def compute_x_k(p, k):
    """Compute x_k = (p + m_k) / 4 where m_k = 4k + 3."""
    m_k = 4 * k + 3
    if (p + m_k) % 4 != 0:
        return None
    return (p + m_k) // 4

def find_witness(p, k):
    """
    Find a Type II witness d | x_k² with d ≡ -x_k (mod m_k).
    Returns (d, x_k, m_k) if found, else None.
    """
    m_k = 4 * k + 3
    x_k = compute_x_k(p, k)

    if x_k is None:
        return None

    if gcd(x_k, m_k) > 1:
        return None  # gcd obstruction

    target = (-x_k) % m_k

    # Get divisors of x_k²
    divs = divisors_of_square(x_k)

    for d in divs:
        if d % m_k == target:
            return (d, x_k, m_k)

    return None

def is_covered_by_k(p, k):
    """Check if prime p is covered by k (has a Type II witness)."""
    return find_witness(p, k) is not None

def find_covering_k(p, K):
    """Find the first k in K that covers prime p."""
    for k in K:
        if is_covered_by_k(p, k):
            return k
    return None

# =============================================================================
# CRT-SPLIT STORAGE
# =============================================================================

class CRTSplitStorage:
    """
    Sparse storage using CRT split: M'' = A × B.
    Each residue class r (mod M'') maps to (r mod A, r mod B).
    """

    def __init__(self, A=A_SPLIT, B=B_SPLIT):
        self.A = A
        self.B = B
        self.M = A * B

        # Storage: b -> set of a values that are uncovered
        self.uncovered = defaultdict(set)

    def add_uncovered(self, r):
        """Mark residue class r as uncovered."""
        a = r % self.A
        b = r % self.B
        self.uncovered[b].add(a)

    def remove_uncovered(self, r):
        """Mark residue class r as covered."""
        a = r % self.A
        b = r % self.B
        if b in self.uncovered and a in self.uncovered[b]:
            self.uncovered[b].discard(a)
            if not self.uncovered[b]:
                del self.uncovered[b]

    def is_uncovered(self, r):
        """Check if residue class r is uncovered."""
        a = r % self.A
        b = r % self.B
        return b in self.uncovered and a in self.uncovered[b]

    def count_uncovered(self):
        """Count total uncovered classes."""
        return sum(len(a_set) for a_set in self.uncovered.values())

    def get_all_uncovered(self):
        """Get all uncovered residue classes."""
        result = []
        for b, a_set in self.uncovered.items():
            for a in a_set:
                # Reconstruct r from (a, b) using CRT
                # r ≡ a (mod A) and r ≡ b (mod B)
                crt_result = chinese_remainder([a, b], [self.A, self.B])
                if crt_result:
                    r, _ = crt_result
                    result.append(r)
        return sorted(result)

# =============================================================================
# COVERAGE RULE GENERATION
# =============================================================================

def generate_prime_witness_rule(k, q):
    """
    Generate CRT rule for k with prime witness q.

    Conditions:
    1. q | x_k ⟺ p ≡ -m_k (mod 4q)
    2. q ≡ -x_k (mod m_k) ⟺ p ≡ -4q (mod m_k)

    Returns (residue, modulus) for the combined CRT condition, or None.
    """
    m_k = 4 * k + 3

    if gcd(q, m_k) > 1:
        return None  # q divides m_k, skip

    # Condition 1: p ≡ -m_k (mod 4q)
    r1 = (-m_k) % (4 * q)
    mod1 = 4 * q

    # Condition 2: p ≡ -4q (mod m_k)
    r2 = (-4 * q) % m_k
    mod2 = m_k

    # Combine via CRT
    result = chinese_remainder([r1, r2], [mod1, mod2])
    if result is None:
        return None

    residue, modulus = result

    # Filter: must have p ≡ 1 (mod 4)
    if residue % 4 != 1:
        # Adjust to find valid residue in this class
        # The pattern repeats every lcm(modulus, 4)
        lcm_mod = (modulus * 4) // gcd(modulus, 4)
        for offset in range(0, lcm_mod, modulus):
            candidate = (residue + offset) % lcm_mod
            if candidate % 4 == 1:
                return (candidate, lcm_mod)
        return None

    return (residue, modulus)

def generate_rules_for_k(k, primes=SMALL_PRIMES):
    """Generate all prime-witness rules for a given k."""
    rules = []
    m_k = 4 * k + 3

    for q in primes:
        rule = generate_prime_witness_rule(k, q)
        if rule:
            residue, modulus = rule
            rules.append({
                'k': k,
                'm_k': m_k,
                'witness_type': 'prime',
                'q': q,
                'd': q,
                'residue': residue,
                'modulus': modulus
            })

    return rules

def generate_all_rules(K):
    """Generate all coverage rules for a set of k values."""
    all_rules = []
    for k in K:
        rules = generate_rules_for_k(k)
        all_rules.extend(rules)
    return all_rules

# =============================================================================
# COVERAGE COMPUTATION
# =============================================================================

def compute_covered_classes(rules, target_modulus=M_DOUBLE_PRIME):
    """
    Compute set of covered residue classes mod target_modulus.
    Returns set of covered residues.
    """
    covered = set()

    for rule in rules:
        residue = rule['residue']
        modulus = rule['modulus']

        # Find all classes mod target_modulus covered by this rule
        if target_modulus % modulus == 0:
            # Simple case: modulus divides target
            step = modulus
            for r in range(residue, target_modulus, step):
                if r % 4 == 1 and gcd(r, target_modulus) == 1:
                    covered.add(r)
        else:
            # General case: need to find compatible classes
            g = gcd(modulus, target_modulus)
            if residue % g == 0:
                # There are solutions
                lcm_mod = (modulus * target_modulus) // g
                # Find base solution
                crt_result = chinese_remainder([residue, 0], [modulus, target_modulus])
                if crt_result:
                    base, _ = crt_result
                    for r in range(base % target_modulus, target_modulus, modulus // g):
                        if r % 4 == 1 and gcd(r, target_modulus) == 1:
                            covered.add(r % target_modulus)

    return covered

def compute_admissible_classes(modulus):
    """
    Compute all admissible residue classes mod modulus.
    Admissible: r ≡ 1 (mod 4) and gcd(r, modulus) = 1
    """
    admissible = set()
    for r in range(1, modulus, 4):  # r ≡ 1 (mod 4)
        if gcd(r, modulus) == 1:
            admissible.add(r)
    return admissible

# =============================================================================
# CERTIFICATE GENERATION
# =============================================================================

def generate_certificate(K, output_file=None):
    """
    Generate a coverage certificate for the given K set.

    Returns:
    - certificate dict with rules and coverage info
    - uncovered_count
    """
    print(f"Generating certificate for K = {K}")
    print(f"Total |K| = {len(K)}")

    # Generate rules
    print("Generating coverage rules...")
    rules = generate_all_rules(K)
    print(f"Generated {len(rules)} rules")

    # For small modulus testing, use a reduced modulus
    # Full M'' = 70B is too large for direct enumeration
    # Use a smaller test modulus first
    test_modulus = 840  # lcm of small m_k values

    print(f"\nComputing coverage mod {test_modulus}...")
    covered = compute_covered_classes(rules, test_modulus)
    admissible = compute_admissible_classes(test_modulus)
    uncovered = admissible - covered

    print(f"Admissible classes: {len(admissible)}")
    print(f"Covered classes: {len(covered)}")
    print(f"Uncovered classes: {len(uncovered)}")

    coverage_fraction = len(covered) / len(admissible) if admissible else 0
    print(f"Coverage fraction: {coverage_fraction:.4%}")

    # Verify known failures
    print("\nVerifying known failures...")
    for p in K13_FAILURES[:5]:  # Check first 5
        k = find_covering_k(p, K)
        if k is not None:
            witness = find_witness(p, k)
            print(f"  p={p}: covered by k={k}, witness d={witness[0]}")
        else:
            print(f"  p={p}: NOT COVERED by K")

    # Check trapped prime
    print(f"\nChecking trapped prime p={TRAPPED_PRIME}...")
    k = find_covering_k(TRAPPED_PRIME, K)
    if k is not None:
        witness = find_witness(TRAPPED_PRIME, k)
        print(f"  Covered by k={k}, witness d={witness[0]}")
    else:
        print(f"  NOT COVERED by K")

    certificate = {
        'K': K,
        'num_rules': len(rules),
        'test_modulus': test_modulus,
        'admissible_count': len(admissible),
        'covered_count': len(covered),
        'uncovered_count': len(uncovered),
        'coverage_fraction': coverage_fraction,
        'uncovered_classes': sorted(uncovered) if len(uncovered) < 1000 else f"{len(uncovered)} classes",
        'rules': rules[:100]  # Store first 100 rules as sample
    }

    if output_file:
        with open(output_file, 'w') as f:
            json.dump(certificate, f, indent=2)
        print(f"\nCertificate saved to {output_file}")

    return certificate, len(uncovered)

# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 70)
    print("ERDŐS-STRAUS CERTIFICATE GENERATOR")
    print("=" * 70)

    # Test with K13
    print("\n" + "=" * 70)
    print("PHASE 1: Testing K13")
    print("=" * 70)
    cert_k13, uncov_k13 = generate_certificate(K13)

    # Test with K13 ∪ K_RESCUE
    print("\n" + "=" * 70)
    print("PHASE 2: Testing K13 ∪ K_RESCUE")
    print("=" * 70)
    K_full = K13 + K_RESCUE
    cert_full, uncov_full = generate_certificate(K_full)

    # Test with K_COMPLETE (all k values for full coverage)
    print("\n" + "=" * 70)
    print("PHASE 3: Testing K_COMPLETE (23 values)")
    print("=" * 70)
    cert_complete, uncov_complete = generate_certificate(
        K_COMPLETE,
        output_file='/Users/kvallie2/Desktop/esc_stage8/certificate_complete.json'
    )

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"K13 uncovered classes (mod 840): {uncov_k13}")
    print(f"K_full (K13 ∪ K_RESCUE) uncovered: {uncov_full}")
    print(f"K_COMPLETE (23 values) uncovered: {uncov_complete}")
    print(f"\nK_COMPLETE = {K_COMPLETE}")

    if uncov_complete == 0:
        print("\n*** ALL CLASSES COVERED MOD 840 - PROOF CANDIDATE! ***")
        print("Next step: Verify coverage at larger modulus M'' = 70,148,764,800")
    else:
        print(f"\n{uncov_complete} classes remain uncovered - need investigation")

if __name__ == "__main__":
    main()
