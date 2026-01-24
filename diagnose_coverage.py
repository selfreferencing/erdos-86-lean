#!/usr/bin/env python3
"""
Diagnose why k=0 appears to cover all 96 classes.
Check if the containment logic is too weak.
"""

from math import gcd

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

    # Need p ≡ 1 (mod 4)
    if r % 4 != 1:
        r_new, L_new = crt_solve(r, L, 1, 4)
        if r_new is None:
            return None
        r, L = r_new, L_new

    return {'k': k, 'd': d, 'm_k': m_k, 'rad_d': rad_d, 'L': L, 'r': r}

def check_containment(class_r, class_M, rule_r, rule_L):
    g = gcd(class_M, rule_L)
    return (class_r % g) == (rule_r % g)

# Get admissible classes mod 840
admissible = [r for r in range(1, 840, 4) if gcd(r, 840) == 1]
print(f"Admissible classes mod 840: {len(admissible)}")

# Look at k=0 rules
print("\n=== k=0 RULES ANALYSIS ===")
print(f"m_k = 3 for k=0")

k0_rules = []
for d in range(1, 100):
    rule = compute_crt_rule(0, d)
    if rule:
        k0_rules.append(rule)

print(f"\nFirst 20 k=0 rules:")
for rule in k0_rules[:20]:
    g = gcd(840, rule['L'])
    print(f"  d={rule['d']:>3}: L={rule['L']:>6}, r={rule['r']:>6}, gcd(840,L)={g:>3}")

# Check what's happening with containment
print("\n=== CONTAINMENT ANALYSIS ===")
print("For containment to hold: class_r ≡ rule_r (mod gcd(840, L))")
print()

# Find all unique gcds
unique_gcds = set()
for rule in k0_rules:
    unique_gcds.add(gcd(840, rule['L']))
print(f"Unique gcd(840, L) values for k=0 rules: {sorted(unique_gcds)}")

# For each unique gcd, what residues mod g are covered?
print("\n=== RESIDUE COVERAGE BY GCD ===")
for g in sorted(unique_gcds):
    residues_covered = set()
    for rule in k0_rules:
        if gcd(840, rule['L']) == g:
            residues_covered.add(rule['r'] % g)

    # What admissible residues fall in each covered residue class mod g?
    admissible_by_residue = {}
    for res in range(g):
        admissible_by_residue[res] = [r for r in admissible if r % g == res]

    total_covered = sum(len(admissible_by_residue[res]) for res in residues_covered)
    print(f"\ngcd = {g}:")
    print(f"  Residues covered: {sorted(residues_covered)}")
    print(f"  Admissible classes covered: {total_covered} / {len(admissible)}")

# THE CRITICAL CHECK: For a specific resistant class, verify containment properly
print("\n=== CRITICAL CHECK: RESISTANT CLASS r=1 ===")
r = 1  # Known resistant class
print(f"Class: p ≡ 1 (mod 840)")
print()

# Find which k=0 rule supposedly covers it
for rule in k0_rules:
    g = gcd(840, rule['L'])
    if r % g == rule['r'] % g:
        print(f"Rule d={rule['d']} claims to cover:")
        print(f"  L = {rule['L']}")
        print(f"  r_rule = {rule['r']}")
        print(f"  gcd(840, L) = {g}")
        print(f"  1 % {g} = {1 % g}")
        print(f"  r_rule % {g} = {rule['r'] % g}")
        print()

        # VERIFICATION: Test with actual primes
        print("  Testing with actual primes p ≡ 1 (mod 840):")
        test_primes = [p for p in [841, 1681, 2521, 3361, 4201, 5041, 5881]
                       if all(p % d != 0 for d in [2, 3, 5, 7])]
        for p in test_primes[:3]:
            # Check if p satisfies the rule
            satisfies_rule = (p % rule['L'] == rule['r'])

            # Check if p has witness at k=0 with d=rule['d']
            m_k = 3
            if (p + m_k) % 4 == 0:
                x_k = (p + m_k) // 4
                d = rule['d']
                has_witness = (x_k % d == 0) and (d % m_k == (-x_k) % m_k)
            else:
                has_witness = False

            print(f"    p={p}: satisfies_rule={satisfies_rule}, has_witness={has_witness}")

        break

# Show the actual issue
print("\n=== THE ISSUE ===")
print("The containment check says: if r ≡ rule_r (mod gcd(M, L)), then class ⊆ rule")
print("But this is only valid if EVERY p in the class satisfies the CRT constraint.")
print()
print("The CRT constraint for k=0, d=? is:")
print("  p ≡ -4d (mod 3) AND p ≡ -3 (mod 4·rad(d))")
print()
print("For p ≡ 1 (mod 840), does EVERY such p satisfy these conditions for some d?")
print("Let's check specific primes in class r=1 mod 840:")

def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True

# Find primes p ≡ 1 (mod 840)
primes_in_1 = []
p = 1
while len(primes_in_1) < 5:
    p += 840
    if is_prime(p) and p % 4 == 1:
        primes_in_1.append(p)

print(f"\nPrimes p ≡ 1 (mod 840): {primes_in_1}")

for p in primes_in_1:
    print(f"\np = {p}:")
    m_k = 3
    if (p + m_k) % 4 == 0:
        x_k = (p + m_k) // 4
        print(f"  x_0 = (p+3)/4 = {x_k}")
        print(f"  x_0 % 3 = {x_k % 3}")
        print(f"  Need d ≡ {(-x_k) % 3} (mod 3) with d | x_0²")

        # Find valid d
        found = False
        for d in range(1, 101):
            if (x_k * x_k) % d == 0 and d % m_k == (-x_k) % m_k:
                print(f"  Found witness: d = {d}")
                found = True
                break
        if not found:
            print(f"  NO WITNESS FOUND for d ≤ 100")
    else:
        print(f"  (p+3) % 4 = {(p+m_k) % 4} ≠ 0, so k=0 doesn't apply!")
