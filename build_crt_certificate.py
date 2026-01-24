#!/usr/bin/env python3
"""
Build a rigorous CRT certificate for Erdős-Straus.

Phase 1: Build witness menu (k, d) pairs
Phase 2: Check CRT coverage at mod 840
Phase 3: Refine resistant classes
Phase 4: Verify completeness

This is the PROOF approach - checking logical entailment, not sampling.
"""

from math import gcd
from collections import defaultdict
import sys

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

def lcm(a, b):
    return a * b // gcd(a, b)

def rad(n):
    """Compute radical of n (product of distinct prime factors)."""
    if n <= 1:
        return 1
    result = 1
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            result *= d
            while temp % d == 0:
                temp //= d
        d += 1 if d == 2 else 2
    if temp > 1:
        result *= temp
    return result

def extended_gcd(a, b):
    """Extended Euclidean algorithm."""
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def crt_solve(r1, m1, r2, m2):
    """
    Solve x ≡ r1 (mod m1) and x ≡ r2 (mod m2) using CRT.
    Returns (solution, modulus) or (None, None) if no solution.
    """
    g = gcd(m1, m2)
    if (r1 - r2) % g != 0:
        return None, None

    m = lcm(m1, m2)
    _, x, _ = extended_gcd(m1, m2)

    diff = (r2 - r1) // g
    solution = (r1 + m1 * x * diff) % m
    return solution, m

def compute_crt_rule(k, d):
    """
    Compute the CRT rule for (k, d).

    For d to be a witness at k, we need:
    1. d ≡ -x_k (mod m_k)  =>  p ≡ -4d (mod m_k)
    2. rad(d) | x_k        =>  p ≡ -m_k (mod 4·rad(d))

    Returns dict with rule info, or None if invalid.
    """
    m_k = 4 * k + 3

    # Check gcd condition
    if gcd(d, m_k) > 1:
        return None  # d must be coprime to m_k for valid witness

    rad_d = rad(d)

    # Condition 1: p ≡ -4d (mod m_k)
    r1 = (-4 * d) % m_k
    m1 = m_k

    # Condition 2: p ≡ -m_k (mod 4·rad(d))
    m2 = 4 * rad_d
    r2 = (-m_k) % m2

    # Combine via CRT
    r, L = crt_solve(r1, m1, r2, m2)

    if r is None:
        return None

    # Also need p ≡ 1 (mod 4) - check compatibility
    if r % 4 != 1:
        # Check if there's a solution with p ≡ 1 (mod 4)
        r_new, L_new = crt_solve(r, L, 1, 4)
        if r_new is None:
            return None
        r, L = r_new, L_new

    return {
        'k': k,
        'd': d,
        'm_k': m_k,
        'rad_d': rad_d,
        'L': L,
        'r': r,
    }

def get_admissible_classes(M):
    """Get all admissible residue classes mod M."""
    return [r for r in range(1, M, 4) if gcd(r, M) == 1]

def check_containment(class_r, class_M, rule_r, rule_L):
    """
    Check if class {p : p ≡ class_r (mod class_M)} is contained in
    rule class {p : p ≡ rule_r (mod rule_L)}.

    TRUE containment holds iff:
    1. rule_L divides class_M (rule is coarser than class)
    2. class_r ≡ rule_r (mod rule_L)
    """
    if class_M % rule_L != 0:
        return False
    return class_r % rule_L == rule_r

def build_witness_menu(D_max=500):
    """Build menu of (k, d) pairs with their CRT rules."""
    print(f"Building witness menu with D_max = {D_max}...")

    menu = []

    for k in K_COMPLETE:
        m_k = 4 * k + 3
        for d in range(1, D_max + 1):
            rule = compute_crt_rule(k, d)
            if rule is not None:
                menu.append(rule)

    print(f"  Generated {len(menu)} valid (k, d) rules")
    return menu

def check_coverage_mod_M(menu, M=840):
    """
    Check which admissible classes mod M are covered by CRT containment.

    This is the RIGOROUS check - not sampling.
    """
    print(f"\nChecking CRT coverage at mod {M}...")

    admissible = get_admissible_classes(M)
    print(f"  Admissible classes: {len(admissible)}")

    covered = {}  # class -> covering rule
    uncovered = []

    for r in admissible:
        found = False
        for rule in menu:
            if check_containment(r, M, rule['r'], rule['L']):
                covered[r] = rule
                found = True
                break

        if not found:
            uncovered.append(r)

    print(f"  Covered by CRT entailment: {len(covered)}")
    print(f"  Uncovered (resistant): {len(uncovered)}")

    if uncovered:
        print(f"  Resistant classes: {uncovered}")

    return covered, uncovered

def refine_class(r, M, refine_mod, menu):
    """
    Refine class r mod M by splitting into sub-classes mod (M * refine_mod).
    Return which sub-classes are covered and which aren't.
    """
    M_new = M * refine_mod
    covered_sub = {}
    uncovered_sub = []

    # Find all sub-classes
    for s in range(refine_mod):
        # Find t such that t ≡ r (mod M) and t ≡ s (mod refine_mod)
        t, L = crt_solve(r, M, s, refine_mod)
        if t is None:
            continue

        # Check if this sub-class is admissible
        if t % 4 != 1 or gcd(t, M_new) != 1:
            continue

        # Check coverage
        found = False
        for rule in menu:
            if check_containment(t, M_new, rule['r'], rule['L']):
                covered_sub[t] = rule
                found = True
                break

        if not found:
            uncovered_sub.append((t, s))

    return covered_sub, uncovered_sub

def main():
    D_max = int(sys.argv[1]) if len(sys.argv) > 1 else 500

    print("=" * 70)
    print("CRT CERTIFICATE CONSTRUCTION FOR ERDŐS-STRAUS")
    print("=" * 70)
    print(f"K_COMPLETE = {K_COMPLETE}")
    print(f"|K| = {len(K_COMPLETE)}")
    print(f"D_max = {D_max}")
    print()

    # Phase 1: Build witness menu
    menu = build_witness_menu(D_max)

    # Phase 2: Check coverage at mod 840
    covered_840, uncovered_840 = check_coverage_mod_M(menu, 840)

    # Show coverage statistics
    print("\n" + "=" * 70)
    print("PHASE 2 RESULTS: MOD 840")
    print("=" * 70)

    # Count by k
    k_counts = defaultdict(int)
    for r, rule in covered_840.items():
        k_counts[rule['k']] += 1

    print("\nCoverage by k value:")
    for k in sorted(k_counts.keys()):
        print(f"  k={k} (m={4*k+3}): covers {k_counts[k]} classes")

    # Phase 3: Refine uncovered classes
    if uncovered_840:
        print("\n" + "=" * 70)
        print("PHASE 3: REFINING RESISTANT CLASSES")
        print("=" * 70)

        # Try refining by mod 11
        all_level2_covered = {}
        all_level2_uncovered = []

        for r in uncovered_840:
            print(f"\nRefining class r ≡ {r} (mod 840) by mod 11:")
            sub_covered, sub_uncovered = refine_class(r, 840, 11, menu)

            print(f"  Covered sub-classes: {len(sub_covered)}")
            print(f"  Uncovered sub-classes: {len(sub_uncovered)}")

            all_level2_covered.update(sub_covered)
            for t, s in sub_uncovered:
                all_level2_uncovered.append((r, s, t))

        print(f"\nLevel 2 total: {len(all_level2_covered)} covered, {len(all_level2_uncovered)} uncovered")

        # Phase 3b: Refine Level 2 uncovered by mod 23
        if all_level2_uncovered:
            print("\n" + "-" * 70)
            print("REFINING LEVEL 2 UNCOVERED BY MOD 23")
            print("-" * 70)

            all_level3_covered = {}
            all_level3_uncovered = []

            M2 = 840 * 11  # = 9240

            for r_840, s_11, t_9240 in all_level2_uncovered:
                sub_covered, sub_uncovered = refine_class(t_9240, M2, 23, menu)

                if sub_covered:
                    print(f"  Class ({r_840}, {s_11}): {len(sub_covered)} covered by mod 23")

                all_level3_covered.update(sub_covered)
                for t, s in sub_uncovered:
                    all_level3_uncovered.append((r_840, s_11, s, t))

            print(f"\nLevel 3 total: {len(all_level3_covered)} covered, {len(all_level3_uncovered)} uncovered")

            if all_level3_uncovered:
                print("\n*** UNCOVERED AT LEVEL 3 ***")
                for item in all_level3_uncovered[:10]:
                    print(f"  {item}")

    # Final summary
    print("\n" + "=" * 70)
    print("CERTIFICATE SUMMARY")
    print("=" * 70)

    total_classes_840 = len(get_admissible_classes(840))
    covered_at_840 = len(covered_840)
    resistant_840 = len(uncovered_840)

    print(f"Level 1 (mod 840): {covered_at_840}/{total_classes_840} covered by CRT entailment")

    if uncovered_840:
        level2_covered = len(all_level2_covered) if 'all_level2_covered' in dir() else 0
        level2_uncovered = len(all_level2_uncovered) if 'all_level2_uncovered' in dir() else 0
        print(f"Level 2 (mod 9240): {level2_covered} covered, {level2_uncovered} need Level 3")

        if 'all_level3_covered' in dir():
            level3_covered = len(all_level3_covered)
            level3_uncovered = len(all_level3_uncovered)
            print(f"Level 3 (mod 212520): {level3_covered} covered, {level3_uncovered} uncovered")

            if level3_uncovered == 0:
                print("\n*** ALL CLASSES COVERED BY CRT ENTAILMENT ***")
                print("This constitutes a rigorous proof of ESC for p ≡ 1 (mod 4).")
            else:
                print(f"\n*** {level3_uncovered} CLASSES REMAIN UNCOVERED ***")
                print("Need larger D_max or additional refinement.")
    else:
        print("\n*** ALL CLASSES COVERED AT LEVEL 1 ***")

if __name__ == "__main__":
    main()
