#!/usr/bin/env python3
"""
Build CRT certificate using UNION coverage (multiple rules per class).

Key insight: A class C mod M might not be contained in any single rule,
but every prime in C might still be covered by SOME rule (different primes,
different rules). To prove this rigorously, we need to show:

    C ⊆ ⋃_{(k,d)} Rule_{k,d}

This is equivalent to: C ∩ (complement of union) = ∅

For computational tractability, we:
1. For each class C, compute intersections C ∩ Rule for each rule
2. These intersections partition C into sub-classes
3. Each sub-class is either:
   a. Covered by the rule (contained in Rule)
   b. Needs to be checked against other rules
"""

from math import gcd
from collections import defaultdict
import sys

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

def lcm(a, b):
    return a * b // gcd(a, b)

def rad(n):
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
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def crt_solve(r1, m1, r2, m2):
    g = gcd(m1, m2)
    if (r1 - r2) % g != 0:
        return None, None
    m = lcm(m1, m2)
    _, x, _ = extended_gcd(m1, m2)
    diff = (r2 - r1) // g
    solution = (r1 + m1 * x * diff) % m
    return solution, m

def compute_crt_rule(k, d):
    """Compute CRT rule for (k, d)."""
    m_k = 4 * k + 3
    if gcd(d, m_k) > 1:
        return None

    rad_d = rad(d)
    r1 = (-4 * d) % m_k
    m1 = m_k
    m2 = 4 * rad_d
    r2 = (-m_k) % m2

    r, L = crt_solve(r1, m1, r2, m2)
    if r is None:
        return None

    # Also need p ≡ 1 (mod 4)
    if r % 4 != 1:
        r_new, L_new = crt_solve(r, L, 1, 4)
        if r_new is None:
            return None
        r, L = r_new, L_new

    return {'k': k, 'd': d, 'm_k': m_k, 'rad_d': rad_d, 'L': L, 'r': r}

def get_admissible_classes(M):
    """Get admissible classes mod M (p ≡ 1 mod 4, gcd(p, M) = 1)."""
    return [r for r in range(1, M, 4) if gcd(r, M) == 1]

def check_intersection_coverage(class_r, class_M, rules, depth=0, max_depth=4):
    """
    Check if class is covered by union of rules.

    Returns: (covered, covering_info)
    - covered: True if class is provably covered
    - covering_info: dict with details
    """
    if depth > max_depth:
        return False, {'reason': 'max_depth_reached', 'class': (class_r, class_M)}

    # Check if class is contained in any single rule
    for rule in rules:
        L = rule['L']
        r_rule = rule['r']

        # True containment: L | M and r ≡ r_rule (mod L)
        if class_M % L == 0 and class_r % L == r_rule:
            return True, {'rule': (rule['k'], rule['d']), 'type': 'containment'}

    # Check intersection coverage: split class by rules
    # For each rule, compute the intersection modulus
    min_combined_M = float('inf')
    best_split = None

    for rule in rules:
        L = rule['L']
        r_rule = rule['r']

        # Intersection of class mod M and rule mod L exists iff
        # class_r ≡ r_rule (mod gcd(M, L))
        g = gcd(class_M, L)
        if class_r % g != r_rule % g:
            continue  # No intersection

        # Compute the combined class: intersection
        combined_r, combined_M = crt_solve(class_r, class_M, r_rule, L)
        if combined_r is None:
            continue

        # This intersection is covered by the rule
        # The complement in class_r mod class_M needs checking

        if combined_M < min_combined_M and combined_M > class_M:
            min_combined_M = combined_M
            best_split = (rule, combined_r, combined_M)

    if best_split is None:
        # No rule intersects non-trivially - class is truly uncovered
        return False, {'reason': 'no_intersecting_rule', 'class': (class_r, class_M)}

    # We have a split. The intersection is covered.
    # Now we need to check all other sub-classes at the finer modulus.
    rule, int_r, int_M = best_split

    # All sub-classes at modulus int_M that reduce to class_r mod class_M
    sub_classes = []
    for r in range(int_M):
        if r % class_M == class_r and r % 4 == 1 and gcd(r, int_M) == 1:
            sub_classes.append(r)

    # The intersection sub-class int_r is covered
    # Check all others
    all_covered = True
    coverage_info = {'split_M': int_M, 'sub_classes': {}}

    for sub_r in sub_classes:
        if sub_r == int_r:
            coverage_info['sub_classes'][sub_r] = {'covered': True, 'by': (rule['k'], rule['d'])}
        else:
            # Recursively check this sub-class
            sub_covered, sub_info = check_intersection_coverage(sub_r, int_M, rules, depth+1, max_depth)
            coverage_info['sub_classes'][sub_r] = {'covered': sub_covered, 'info': sub_info}
            if not sub_covered:
                all_covered = False

    return all_covered, coverage_info

def main():
    D_max = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 840

    print("=" * 70)
    print("UNION COVERAGE CERTIFICATE FOR ERDŐS-STRAUS")
    print("=" * 70)
    print(f"Working modulus M = {M}")
    print(f"D_max = {D_max}")
    print()

    # Build rules
    print("Building CRT rules...")
    rules = []
    for k in K_COMPLETE:
        for d in range(1, D_max + 1):
            rule = compute_crt_rule(k, d)
            if rule:
                rules.append(rule)

    print(f"  Generated {len(rules)} valid rules")

    # Get admissible classes
    admissible = get_admissible_classes(M)
    print(f"  Admissible classes mod {M}: {len(admissible)}")
    print()

    # Check coverage
    print("Checking union coverage...")
    covered_classes = []
    uncovered_classes = []

    for r in admissible:
        covered, info = check_intersection_coverage(r, M, rules, max_depth=3)
        if covered:
            covered_classes.append((r, info))
        else:
            uncovered_classes.append((r, info))

    print(f"\nResults:")
    print(f"  Covered: {len(covered_classes)}")
    print(f"  Uncovered: {len(uncovered_classes)}")

    if uncovered_classes:
        print(f"\nUncovered classes:")
        for r, info in uncovered_classes[:10]:
            print(f"  r = {r}: {info.get('reason', 'unknown')}")

    # Analyze coverage types
    containment_count = 0
    split_count = 0
    for r, info in covered_classes:
        if info.get('type') == 'containment':
            containment_count += 1
        else:
            split_count += 1

    print(f"\nCoverage breakdown:")
    print(f"  Single-rule containment: {containment_count}")
    print(f"  Multi-rule union: {split_count}")

    # Show some examples of union coverage
    print(f"\nExamples of union coverage:")
    count = 0
    for r, info in covered_classes:
        if info.get('type') != 'containment' and count < 3:
            print(f"\n  Class r ≡ {r} (mod {M}):")
            if 'split_M' in info:
                print(f"    Split to modulus {info['split_M']}")
                for sub_r, sub_info in list(info.get('sub_classes', {}).items())[:5]:
                    status = "covered" if sub_info.get('covered') else "UNCOVERED"
                    by = sub_info.get('by', sub_info.get('info', {}).get('rule', 'recursive'))
                    print(f"      r ≡ {sub_r}: {status} by {by}")
            count += 1

if __name__ == "__main__":
    main()
