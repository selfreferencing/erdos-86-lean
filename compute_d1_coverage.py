#!/usr/bin/env python3
"""
Compute which Mordell-hard residue classes are covered by d1Sufficient for at least one k in K10.
"""

from math import gcd
from functools import reduce

# K10 values
K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Mordell-hard residue classes mod 840
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

def lcm(a, b):
    return a * b // gcd(a, b)

def lcm_list(lst):
    return reduce(lcm, lst)

# d1Sufficient: p % (16*k + 12) = (12*k + 5)
def d1_modulus(k):
    return 16 * k + 12

def d1_target(k):
    return 12 * k + 5

print("=" * 60)
print("d1Sufficient conditions for K10")
print("=" * 60)

for k in K10:
    mod = d1_modulus(k)
    tgt = d1_target(k)
    print(f"k={k:2d}: p ≡ {tgt:3d} (mod {mod:3d})")

print()

# Compute the LCM of all d1 moduli
d1_moduli = [d1_modulus(k) for k in K10]
d1_lcm = lcm_list(d1_moduli)
print(f"LCM of d1 moduli: {d1_lcm}")

# For the combined analysis, we work mod LCM(840, d1_lcm)
combined_mod = lcm(840, d1_lcm)
print(f"Combined modulus (LCM with 840): {combined_mod}")
print()

# Enumerate all Mordell-hard residues mod combined_mod
mordell_hard_extended = []
for base in MORDELL_HARD:
    for i in range(combined_mod // 840):
        r = base + i * 840
        mordell_hard_extended.append(r % combined_mod)
mordell_hard_extended = sorted(set(mordell_hard_extended))
print(f"Number of Mordell-hard residue classes mod {combined_mod}: {len(mordell_hard_extended)}")
print()

# For each Mordell-hard residue, check which k values have d1Sufficient
covered = []
not_covered = []

for r in mordell_hard_extended:
    covering_ks = []
    for k in K10:
        mod = d1_modulus(k)
        tgt = d1_target(k)
        if r % mod == tgt:
            covering_ks.append(k)
    if covering_ks:
        covered.append((r, covering_ks))
    else:
        not_covered.append(r)

print(f"Covered by d1Sufficient: {len(covered)} residue classes")
print(f"NOT covered by d1Sufficient: {len(not_covered)} residue classes")
print()

if not_covered:
    print("=" * 60)
    print("Residue classes NOT covered by d1Sufficient (need QRSufficient)")
    print("=" * 60)
    for r in not_covered[:50]:  # Show first 50
        print(f"  p ≡ {r} (mod {combined_mod})")
    if len(not_covered) > 50:
        print(f"  ... and {len(not_covered) - 50} more")
    print()

    # Analyze these residue classes mod 840
    not_covered_mod840 = sorted(set(r % 840 for r in not_covered))
    print(f"NOT covered residue classes mod 840: {not_covered_mod840}")
    print()

# Additional analysis: for each k, how many residue classes does it cover?
print("=" * 60)
print("Coverage by individual k values")
print("=" * 60)

for k in K10:
    mod = d1_modulus(k)
    tgt = d1_target(k)
    count = sum(1 for r in mordell_hard_extended if r % mod == tgt)
    print(f"k={k:2d}: covers {count:5d} out of {len(mordell_hard_extended)} ({100*count/len(mordell_hard_extended):.2f}%)")

print()

# Compute pairwise coverage
print("=" * 60)
print("Finding minimal covering subset")
print("=" * 60)

# Greedy algorithm to find smallest subset of K10 that covers all Mordell-hard residues
remaining = set(not_covered)
full_remaining = set(mordell_hard_extended)
selected_ks = []

print(f"Starting with {len(full_remaining)} Mordell-hard residue classes")

for k in K10:
    mod = d1_modulus(k)
    tgt = d1_target(k)
    covers = sum(1 for r in full_remaining if r % mod == tgt)
    print(f"k={k:2d} (mod {mod:3d}): would cover {covers} classes")

print()

# Check if d1Sufficient alone covers everything
if len(not_covered) == 0:
    print("*** d1Sufficient COMPLETELY covers all Mordell-hard residue classes! ***")
    print("This means the proof is straightforward: just verify d1Sufficient for each k.")
else:
    print(f"*** d1Sufficient leaves {len(not_covered)} classes uncovered ***")
    print("*** These require QRSufficient analysis ***")
    print()

    # For the uncovered classes, analyze what constraints they face
    print("Analyzing constraints on uncovered classes...")
    print()

    # Check divisibility patterns for x_k values in uncovered classes
    # x_k = (p + 4k + 3) / 4
    # For p ≡ r (mod combined_mod), we have x_k ≡ (r + 4k + 3) / 4 (mod combined_mod/4)

    for r in not_covered[:10]:  # Analyze first 10
        print(f"p ≡ {r} (mod {combined_mod}):")
        for k in K10:
            m_k = 4 * k + 3
            x_k_mod = (r + m_k) // 4  # This works because p ≡ 1 (mod 4)
            print(f"  k={k:2d}: x_k ≡ {x_k_mod} (mod ...), m_k = {m_k}")
        print()
