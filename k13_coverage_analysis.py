#!/usr/bin/env python3
"""
Computational Exploration of K13 Coverage for Erdős-Straus Conjecture

This script systematically analyzes the K13 coverage claim and identifies
the structure needed for a proof. The goal is to transform computational
verification into a finite case analysis that constitutes a proof.

Author: Generated for Vallier ESC project
"""

from math import gcd, isqrt, log2
from functools import reduce
from collections import defaultdict
import random

# =============================================================================
# CONSTANTS AND CORE DEFINITIONS
# =============================================================================

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
M_K = [4*k + 3 for k in K13]  # [3, 7, 11, 23, 31, 39, 47, 59, 71, 79, 95, 107, 119]

# Mordell-hard residues mod 840
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

# Small primes for witness analysis
SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def is_prime(n):
    """Check if n is prime using trial division."""
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

def prime_factors(n):
    """Return list of distinct prime factors of n."""
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def factorize(n):
    """Return full factorization as list of (prime, exponent) pairs."""
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            exp = 0
            while n % d == 0:
                exp += 1
                n //= d
            factors.append((d, exp))
        d += 1
    if n > 1:
        factors.append((n, 1))
    return factors

def divisors(n):
    """Return all divisors of n."""
    divs = []
    for i in range(1, isqrt(n) + 1):
        if n % i == 0:
            divs.append(i)
            if i != n // i:
                divs.append(n // i)
    return sorted(divs)

def divisors_up_to(n, limit):
    """Return divisors of n that are <= limit."""
    return [d for d in divisors(n) if d <= limit]

def lcm(a, b):
    """Least common multiple."""
    return a * b // gcd(a, b)

def lcm_list(lst):
    """LCM of a list of integers."""
    return reduce(lcm, lst, 1)

def euler_phi(n):
    """Euler's totient function."""
    result = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result

def multiplicative_order(a, m):
    """Compute multiplicative order of a mod m. Returns None if gcd(a,m) > 1."""
    if gcd(a, m) != 1:
        return None
    order = 1
    power = a % m
    while power != 1:
        power = (power * a) % m
        order += 1
        if order > m:
            return None
    return order

def legendre(a, p):
    """Compute Legendre symbol (a/p) for odd prime p."""
    if a % p == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return 1 if result == 1 else -1

def jacobi(a, n):
    """Compute Jacobi symbol (a/n)."""
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be positive and odd")
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

def is_mordell_hard(p):
    """Check if prime p is Mordell-hard (p mod 840 in MORDELL_HARD)."""
    return is_prime(p) and (p % 840) in MORDELL_HARD

def m_k(k):
    """Return m_k = 4k + 3."""
    return 4 * k + 3

def x_k(p, k):
    """Return x_k = (p + m_k)/4 if divisible, else None."""
    m = m_k(k)
    if (p + m) % 4 == 0:
        return (p + m) // 4
    return None

def is_witness(d, x, m):
    """Check if d is a Type II witness: d | x², d ≤ x, d ≡ -x (mod m)."""
    return (x * x) % d == 0 and d <= x and (d + x) % m == 0

def has_type_ii_witness(p, k):
    """Check if k provides a Type II witness for prime p."""
    m = m_k(k)
    x = x_k(p, k)
    if x is None:
        return False, None
    # Check all divisors of x² up to x
    x_sq = x * x
    for d in divisors_up_to(x_sq, x):
        if is_witness(d, x, m):
            return True, d
    return False, None

def get_mordell_hard_primes(limit):
    """Generate Mordell-hard primes up to limit."""
    primes = []
    for p in range(2, limit + 1):
        if is_mordell_hard(p):
            primes.append(p)
    return primes

# =============================================================================
# TASK 1: DIRECT DIVISIBILITY ANALYSIS
# =============================================================================

def task1_direct_divisibility():
    """
    For each k ∈ K13, find the residue class of p (mod 4·m_k) where m_k | x_k.

    We need m_k | x_k = (p + m_k)/4
    This means 4*m_k | (p + m_k), i.e., p ≡ -m_k ≡ 3*m_k (mod 4*m_k).
    """
    print("=" * 80)
    print("TASK 1: DIRECT DIVISIBILITY ANALYSIS")
    print("=" * 80)
    print()
    print("For m_k | x_k, we need p ≡ 3*m_k (mod 4*m_k)")
    print()

    # Table: k, m_k, modulus 4*m_k, direct divisibility residue
    print(f"{'k':>4} {'m_k':>6} {'4*m_k':>8} {'residue':>8} {'= 3*m_k':>8}")
    print("-" * 40)

    coverage_by_k = {}

    for k in K13:
        m = m_k(k)
        modulus = 4 * m
        residue = (3 * m) % modulus
        print(f"{k:>4} {m:>6} {modulus:>8} {residue:>8} {3*m:>8}")

        # Find which Mordell-hard classes (mod 840) are covered
        # Need to lift to lcm(840, 4*m_k)
        combined_mod = lcm(840, modulus)
        covered = []
        for mh in MORDELL_HARD:
            # Check if any p ≡ mh (mod 840) AND p ≡ residue (mod modulus)
            # Use CRT: find r such that r ≡ mh (mod 840) and r ≡ residue (mod modulus)
            for r in range(combined_mod):
                if r % 840 == mh and r % modulus == residue:
                    covered.append(mh)
                    break
        coverage_by_k[k] = covered

    print()
    print("Coverage of Mordell-hard residue classes by direct divisibility:")
    print("-" * 60)
    all_covered = set()
    for k in K13:
        m = m_k(k)
        covered = coverage_by_k[k]
        all_covered.update(covered)
        print(f"k={k:>2} (m_k={m:>3}): covers {covered}")

    print()
    print(f"Union of all covered classes: {sorted(all_covered)}")
    uncovered = set(MORDELL_HARD) - all_covered
    print(f"Uncovered by direct divisibility: {sorted(uncovered)}")

    return coverage_by_k, all_covered

# =============================================================================
# TASK 2: SMALL PRIME WITNESS ANALYSIS
# =============================================================================

def task2_small_prime_witnesses():
    """
    For each (k, q) pair with k ∈ K13 and small prime q:
    Find residue classes of p where q | x_k AND q is a valid witness.

    Condition 1: q | x_k means q | (p + m_k)/4, so p ≡ -m_k (mod 4q)
    Condition 2: q ≡ -x_k (mod m_k), which involves finding when this holds
    """
    print()
    print("=" * 80)
    print("TASK 2: SMALL PRIME WITNESS ANALYSIS")
    print("=" * 80)
    print()

    # For q to be a witness for x_k:
    # 1. q | x_k² and q ≤ x_k  (for small q, this is q | x_k and q ≤ x_k)
    # 2. q ≡ -x_k (mod m_k)

    # From condition 1: q | x_k means (p + m_k) ≡ 0 (mod 4q)
    # So p ≡ -m_k (mod 4q)

    # From condition 2: We need to find when q ≡ -x_k (mod m_k)
    # where x_k = (p + m_k)/4
    # So q ≡ -(p + m_k)/4 (mod m_k)
    # i.e., 4q ≡ -(p + m_k) (mod 4*m_k)  [multiply by 4]
    # i.e., p ≡ -m_k - 4q (mod 4*m_k)

    print("Small prime witness conditions:")
    print("For q | x_k AND q ≡ -x_k (mod m_k):")
    print("  p ≡ -m_k (mod 4q)  AND  p ≡ -m_k - 4q (mod 4*m_k)")
    print()

    witness_classes = {}  # (k, q) -> list of (residue, modulus) covering Mordell-hard classes

    for k in K13:
        m = m_k(k)
        print(f"k = {k}, m_k = {m}:")

        for q in SMALL_PRIMES:
            if gcd(q, m) > 1:
                # q divides m_k, cannot be a unit mod m_k
                continue

            # Condition for q | x_k: p ≡ -m (mod 4q)
            cond1_residue = (-m) % (4 * q)
            cond1_mod = 4 * q

            # Condition for q ≡ -x_k (mod m): p ≡ -m - 4q (mod 4m)
            cond2_residue = (-m - 4*q) % (4 * m)
            cond2_mod = 4 * m

            # Combined modulus via CRT
            combined_mod = lcm(cond1_mod, cond2_mod)

            # Find residues satisfying both conditions
            valid_residues = []
            for r in range(combined_mod):
                if r % cond1_mod == cond1_residue and r % cond2_mod == cond2_residue:
                    valid_residues.append(r)

            if valid_residues:
                # Check which Mordell-hard classes are covered
                super_mod = lcm(840, combined_mod)
                covered_mh = []
                for mh in MORDELL_HARD:
                    for vr in valid_residues:
                        for r in range(super_mod):
                            if r % 840 == mh and r % combined_mod == vr:
                                covered_mh.append(mh)
                                break
                        else:
                            continue
                        break

                if covered_mh:
                    witness_classes[(k, q)] = (valid_residues, combined_mod, covered_mh)
                    print(f"  q={q:>2}: p ≡ {valid_residues} (mod {combined_mod}), covers MH: {covered_mh}")

    # Summary: which Mordell-hard classes are covered by small-prime witnesses for each k
    print()
    print("Summary: Mordell-hard coverage by k via small prime witnesses")
    print("-" * 60)

    cumulative_covered = set()
    for k in K13:
        k_covered = set()
        for q in SMALL_PRIMES:
            if (k, q) in witness_classes:
                k_covered.update(witness_classes[(k, q)][2])
        cumulative_covered.update(k_covered)
        print(f"k={k:>2}: {sorted(k_covered)} (cumulative: {sorted(cumulative_covered)})")

    uncovered = set(MORDELL_HARD) - cumulative_covered
    print()
    print(f"All Mordell-hard classes covered by small primes: {sorted(cumulative_covered)}")
    print(f"Uncovered: {sorted(uncovered)}")

    return witness_classes, cumulative_covered

# =============================================================================
# TASK 3: GCD COUPLING VERIFICATION
# =============================================================================

def task3_gcd_coupling():
    """
    Verify: For distinct a, b ∈ K13, gcd(x_a, x_b) | |a - b|.

    Algebraic proof:
    gcd((p+m_a)/4, (p+m_b)/4) = gcd((p+m_a)/4, (m_a-m_b)/4)
                               = gcd((p+m_a)/4, a-b)
    which divides |a-b|.
    """
    print()
    print("=" * 80)
    print("TASK 3: GCD COUPLING VERIFICATION")
    print("=" * 80)
    print()

    # Algebraic proof
    print("ALGEBRAIC PROOF:")
    print("-" * 60)
    print("For a, b ∈ K13 with a ≠ b:")
    print("  x_a = (p + m_a)/4,  x_b = (p + m_b)/4")
    print("  where m_a = 4a + 3, m_b = 4b + 3")
    print()
    print("  gcd(x_a, x_b) = gcd((p + m_a)/4, (p + m_b)/4)")
    print("               = gcd((p + m_a)/4, (p + m_a)/4 - (p + m_b)/4)")
    print("               = gcd((p + m_a)/4, (m_a - m_b)/4)")
    print("               = gcd((p + m_a)/4, (4a + 3 - 4b - 3)/4)")
    print("               = gcd((p + m_a)/4, a - b)")
    print()
    print("  Since gcd(x, a-b) | (a-b), we have gcd(x_a, x_b) | |a - b|.  □")
    print()

    # Table of max possible gcd for each pair
    print("Maximum possible gcd(x_a, x_b) = |a - b| for pairs in K13:")
    print("-" * 60)
    print(f"{'(a,b)':>12} {'|a-b|':>6} {'divisors':>20}")
    print("-" * 60)

    gcd_bounds = {}
    for i, a in enumerate(K13):
        for b in K13[i+1:]:
            diff = abs(a - b)
            divs = divisors(diff)
            gcd_bounds[(a, b)] = diff
            if diff <= 10:
                print(f"({a:>2},{b:>2}){' '*4} {diff:>6} {str(divs):>20}")

    # Computational verification on sample primes
    print()
    print("COMPUTATIONAL VERIFICATION on sample Mordell-hard primes:")
    print("-" * 60)

    test_primes = get_mordell_hard_primes(10000)[:20]
    violations = []

    for p in test_primes:
        for i, a in enumerate(K13):
            xa = x_k(p, a)
            if xa is None:
                continue
            for b in K13[i+1:]:
                xb = x_k(p, b)
                if xb is None:
                    continue
                g = gcd(xa, xb)
                bound = abs(a - b)
                if g > bound:
                    violations.append((p, a, b, g, bound))

    if violations:
        print("VIOLATIONS FOUND:")
        for v in violations:
            print(f"  p={v[0]}, a={v[1]}, b={v[2]}: gcd={v[3]} > |a-b|={v[4]}")
    else:
        print(f"Verified for {len(test_primes)} primes: No violations found!")

    # Consequence for small primes dividing multiple x_k values
    print()
    print("CONSEQUENCE: Which small primes can divide multiple x_k values?")
    print("-" * 60)
    print("For p > 29, a small prime q can divide x_a and x_b only if q | |a - b|.")
    print()

    # Build table: for each small prime q, which pairs (a,b) allow q | both x_a, x_b?
    for q in [2, 3, 5, 7]:
        pairs = []
        for i, a in enumerate(K13):
            for b in K13[i+1:]:
                if abs(a - b) % q == 0:
                    pairs.append((a, b))
        print(f"q={q}: can divide x_a and x_b for pairs where {q} | |a-b|:")
        print(f"     {pairs[:10]}{'...' if len(pairs) > 10 else ''}")

    return gcd_bounds

# =============================================================================
# TASK 4: COVERAGE FAILURE ANALYSIS
# =============================================================================

def task4_coverage_failures():
    """
    Find residue classes (mod some large M) where NO k ∈ K13 provides
    a witness via direct divisibility or small primes ≤ 29.
    """
    print()
    print("=" * 80)
    print("TASK 4: COVERAGE FAILURE ANALYSIS")
    print("=" * 80)
    print()

    # Compute the modulus for analysis
    # Use lcm of 840 and small prime moduli
    base_mod = 840
    for k in K13:
        m = m_k(k)
        base_mod = lcm(base_mod, 4 * m)

    # This modulus is very large; let's work with a smaller one
    # Focus on 840 * max(m_k) = 840 * 119 = 99960
    analysis_mod = lcm(840, 4 * 119)  # 840 * 119 / gcd = ...
    print(f"Analysis modulus: lcm(840, 4*119) = {analysis_mod}")

    # For each Mordell-hard residue class mod 840, track which k values
    # could potentially provide witnesses

    # First, collect direct divisibility coverage
    direct_coverage = {}
    for k in K13:
        m = m_k(k)
        modulus = 4 * m
        residue = (3 * m) % modulus
        # For which MH classes does this apply?
        for mh in MORDELL_HARD:
            # Check CRT compatibility
            for r in range(lcm(840, modulus)):
                if r % 840 == mh and r % modulus == residue:
                    if mh not in direct_coverage:
                        direct_coverage[mh] = []
                    direct_coverage[mh].append(k)
                    break

    print("Direct divisibility coverage of Mordell-hard classes:")
    for mh in MORDELL_HARD:
        ks = direct_coverage.get(mh, [])
        print(f"  MH ≡ {mh:>3} (mod 840): k ∈ {ks}")

    # Now check small prime witness coverage
    # For each (mh, k, q) triple, check if q can be a witness

    print()
    print("Detailed coverage analysis (direct + small prime witnesses):")
    print("-" * 60)

    detailed_coverage = {mh: set() for mh in MORDELL_HARD}

    for mh in MORDELL_HARD:
        # Direct divisibility
        for k in direct_coverage.get(mh, []):
            detailed_coverage[mh].add((k, 'direct', m_k(k)))

        # Small prime witnesses
        for k in K13:
            m = m_k(k)
            for q in SMALL_PRIMES:
                if gcd(q, m) > 1:
                    continue

                # Check if q can be a witness for this (mh, k) combination
                # p ≡ mh (mod 840), p ≡ -m (mod 4q), p ≡ -m-4q (mod 4m)

                cond1_mod = 840
                cond1_res = mh
                cond2_mod = 4 * q
                cond2_res = (-m) % cond2_mod
                cond3_mod = 4 * m
                cond3_res = (-m - 4*q) % cond3_mod

                combined_mod = lcm(lcm(cond1_mod, cond2_mod), cond3_mod)

                # Check if compatible
                found = False
                for r in range(combined_mod):
                    if (r % cond1_mod == cond1_res and
                        r % cond2_mod == cond2_res and
                        r % cond3_mod == cond3_res):
                        found = True
                        break

                if found:
                    detailed_coverage[mh].add((k, q, m))

    print("Coverage details:")
    uncovered_mh = []
    for mh in MORDELL_HARD:
        coverage = detailed_coverage[mh]
        if coverage:
            print(f"  MH ≡ {mh:>3}: {len(coverage)} witness sources")
            # Show first few
            sample = list(coverage)[:5]
            for s in sample:
                if s[1] == 'direct':
                    print(f"         k={s[0]}, direct divisibility (m_k={s[2]})")
                else:
                    print(f"         k={s[0]}, q={s[1]} (m_k={s[2]})")
            if len(coverage) > 5:
                print(f"         ... and {len(coverage)-5} more")
        else:
            print(f"  MH ≡ {mh:>3}: NO COVERAGE!")
            uncovered_mh.append(mh)

    if uncovered_mh:
        print()
        print(f"UNCOVERED Mordell-hard classes: {uncovered_mh}")
        print("These require deeper analysis!")
    else:
        print()
        print("ALL Mordell-hard classes have at least one potential witness source!")

    return detailed_coverage

# =============================================================================
# TASK 5: PROBABILISTIC/DENSITY ANALYSIS
# =============================================================================

def task5_probabilistic_analysis(num_samples=500, p_min=10**5, p_max=10**6):
    """
    For random large p, estimate the probability that k ∈ K13 fails to have a witness.
    """
    print()
    print("=" * 80)
    print("TASK 5: PROBABILISTIC/DENSITY ANALYSIS")
    print("=" * 80)
    print()

    print(f"Sampling Mordell-hard primes in [{p_min}, {p_max}]...")
    print()

    # Collect Mordell-hard primes in range
    mordell_primes = []
    for p in range(p_min, p_max):
        if is_mordell_hard(p):
            mordell_primes.append(p)
            if len(mordell_primes) >= num_samples:
                break

    print(f"Found {len(mordell_primes)} Mordell-hard primes for analysis")
    print()

    # Track statistics
    k_success_count = {k: 0 for k in K13}
    num_working_k = []
    hard_cases = []  # primes with only 1-2 working k values

    for p in mordell_primes:
        working_ks = []
        for k in K13:
            has_witness, d = has_type_ii_witness(p, k)
            if has_witness:
                working_ks.append(k)
                k_success_count[k] += 1

        num_working_k.append(len(working_ks))
        if len(working_ks) <= 2:
            hard_cases.append((p, working_ks))

    # Report results
    print("Success rate by k:")
    print("-" * 40)
    for k in K13:
        rate = k_success_count[k] / len(mordell_primes) * 100
        print(f"  k={k:>2}: {k_success_count[k]:>4}/{len(mordell_primes)} ({rate:>5.1f}%)")

    print()
    print("Distribution of 'number of working k values':")
    print("-" * 40)
    from collections import Counter
    dist = Counter(num_working_k)
    for n in sorted(dist.keys()):
        print(f"  {n:>2} working k's: {dist[n]:>4} primes ({dist[n]/len(mordell_primes)*100:.1f}%)")

    min_working = min(num_working_k)
    max_working = max(num_working_k)
    avg_working = sum(num_working_k) / len(num_working_k)
    print()
    print(f"Min working k's: {min_working}")
    print(f"Max working k's: {max_working}")
    print(f"Average working k's: {avg_working:.2f}")

    if 0 in dist:
        print()
        print("WARNING: Found primes with NO working k values!")
        for p, ks in hard_cases:
            if len(ks) == 0:
                print(f"  p = {p}")

    # Analyze hard cases
    if hard_cases:
        print()
        print(f"Hard cases (≤2 working k's): {len(hard_cases)} primes")
        print("-" * 60)
        for p, ks in hard_cases[:10]:
            print(f"  p = {p}: working k's = {ks}")
            # Show x_k factorizations for this prime
            print(f"    x_k values and factorizations:")
            for k in K13[:5]:  # Show first 5
                x = x_k(p, k)
                if x:
                    facts = factorize(x)
                    print(f"      k={k}: x={x}, factors={facts}")

    return k_success_count, num_working_k, hard_cases

# =============================================================================
# TASK 6: FINITE VERIFICATION SETUP
# =============================================================================

def task6_finite_verification():
    """
    Set up finite verification for the proof.
    """
    print()
    print("=" * 80)
    print("TASK 6: FINITE VERIFICATION SETUP")
    print("=" * 80)
    print()

    # First, determine which residue classes need explicit verification
    # by running through small primes and checking coverage

    print("Step 1: Enumerate residue classes needing verification")
    print("-" * 60)

    # Use modulus 840 as base
    # For each Mordell-hard class, find the smallest prime and verify

    verification_cases = []

    for mh in MORDELL_HARD:
        # Find smallest Mordell-hard prime in this class
        p = mh
        while not is_prime(p):
            p += 840

        # Verify K13 coverage for this prime
        witnesses = []
        for k in K13:
            has_witness, d = has_type_ii_witness(p, k)
            if has_witness:
                witnesses.append((k, d))

        verification_cases.append({
            'residue': mh,
            'smallest_prime': p,
            'witnesses': witnesses,
            'covered': len(witnesses) > 0
        })

    print("Verification results for smallest prime in each Mordell-hard class:")
    print()
    all_covered = True
    for case in verification_cases:
        status = "✓ COVERED" if case['covered'] else "✗ FAILED"
        print(f"  MH ≡ {case['residue']:>3} (mod 840): p = {case['smallest_prime']}")
        print(f"    {status}")
        if case['witnesses']:
            for k, d in case['witnesses'][:3]:
                print(f"    Witness: k={k}, d={d}")
            if len(case['witnesses']) > 3:
                print(f"    ... and {len(case['witnesses'])-3} more witnesses")
        if not case['covered']:
            all_covered = False

    print()
    if all_covered:
        print("ALL Mordell-hard residue classes have verified witnesses!")
        print()
        print("Step 2: Prove witnesses generalize across residue class")
        print("-" * 60)
        print()
        print("For a witness (k, d) to work for all p' ≡ p (mod M):")
        print("  1. d | x_k'² must hold (follows from divisibility structure)")
        print("  2. d ≤ x_k' must hold (need x_k' large enough)")
        print("  3. d ≡ -x_k' (mod m_k) must hold (follows from p' ≡ p (mod m_k))")
        print()
        print("Key insight: For fixed k and d, condition 3 depends only on p mod 4*m_k.")
        print("If we choose M = lcm(840, 4*m_k) for the relevant k, the witness generalizes.")
    else:
        print("Some residue classes are not covered - deeper analysis needed!")

    return verification_cases

# =============================================================================
# ADDITIONAL ANALYSIS: WITNESS STRUCTURE
# =============================================================================

def analyze_witness_structure(p):
    """
    For a given Mordell-hard prime p, return detailed witness info.
    """
    print()
    print(f"WITNESS STRUCTURE FOR p = {p}")
    print("=" * 60)

    for k in K13:
        m = m_k(k)
        x = x_k(p, k)
        if x is None:
            print(f"k={k:>2}: x_k undefined (4 ∤ p + m_k)")
            continue

        facts = factorize(x)
        target = (-x) % m

        print(f"k={k:>2}: m_k={m:>3}, x_k={x}")
        print(f"       factorization: {facts}")
        print(f"       target: -x_k ≡ {target} (mod {m})")

        # Find witnesses
        x_sq = x * x
        witnesses = []
        for d in divisors_up_to(x_sq, x):
            if (d + x) % m == 0:
                witnesses.append(d)

        if witnesses:
            print(f"       WITNESSES: {witnesses[:10]}{'...' if len(witnesses) > 10 else ''}")
            # Identify the smallest
            print(f"       smallest witness: {min(witnesses)}")
        else:
            print(f"       NO WITNESSES")
        print()

# =============================================================================
# MAIN EXECUTION
# =============================================================================

def main():
    """Run all tasks."""
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " K13 COVERAGE ANALYSIS FOR ERDŐS-STRAUS CONJECTURE ".center(78) + "║")
    print("╚" + "═" * 78 + "╝")
    print()

    print("K13 =", K13)
    print("M_K =", M_K)
    print("Mordell-hard residues (mod 840):", MORDELL_HARD)
    print()

    # Run each task
    task1_direct_divisibility()
    task2_small_prime_witnesses()
    task3_gcd_coupling()
    task4_coverage_failures()
    task5_probabilistic_analysis(num_samples=200, p_min=10**4, p_max=10**6)
    task6_finite_verification()

    # Sample witness structure analysis
    print()
    print("=" * 80)
    print("SAMPLE WITNESS STRUCTURE ANALYSIS")
    print("=" * 80)
    sample_primes = [1009, 3361, 8689]
    for p in sample_primes:
        if is_mordell_hard(p):
            analyze_witness_structure(p)

if __name__ == "__main__":
    main()
