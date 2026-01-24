#!/usr/bin/env python3
"""
Compute which Mordell-hard residue classes mod 840 are covered by d1Sufficient for at least one k in K10.
Uses a more efficient approach that avoids computing large LCMs.
"""

from math import gcd

# K10 values
K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

# Mordell-hard residue classes mod 840
MORDELL_HARD = [1, 121, 169, 289, 361, 529]

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

# For Mordell-hard primes, we need p ≡ r (mod 840) for r in MORDELL_HARD
# For d1Sufficient, we need p ≡ t (mod m) for (m, t) = (16k+12, 12k+5)
#
# These are compatible iff there exists p satisfying both.
# By CRT, this happens iff t ≡ r (mod gcd(m, 840))

print("=" * 60)
print("Checking CRT compatibility")
print("=" * 60)

coverage_by_k = {k: [] for k in K10}

for r in MORDELL_HARD:
    print(f"\nMordell-hard class: p ≡ {r} (mod 840)")
    covering_ks = []
    for k in K10:
        m = d1_modulus(k)
        t = d1_target(k)
        g = gcd(m, 840)
        # Compatible iff t ≡ r (mod g)
        if t % g == r % g:
            covering_ks.append(k)
            coverage_by_k[k].append(r)
            print(f"  k={k:2d}: COMPATIBLE (gcd={g}, {t}≡{r} mod {g})")
        else:
            print(f"  k={k:2d}: incompatible (gcd={g}, {t}≢{r} mod {g})")

    if covering_ks:
        print(f"  ==> Covered by: {covering_ks}")
    else:
        print(f"  ==> NOT COVERED by any k in K10!")

print()
print("=" * 60)
print("Summary: Coverage by k value")
print("=" * 60)

for k in K10:
    print(f"k={k:2d}: covers Mordell-hard classes {coverage_by_k[k]}")

print()

# Check if all 6 Mordell-hard classes are covered
covered_classes = set()
for k in K10:
    covered_classes.update(coverage_by_k[k])

if covered_classes == set(MORDELL_HARD):
    print("*** SUCCESS: d1Sufficient covers ALL Mordell-hard residue classes! ***")
else:
    uncovered = set(MORDELL_HARD) - covered_classes
    print(f"*** INCOMPLETE: d1Sufficient misses classes {uncovered} ***")
    print("*** These require QRSufficient analysis ***")

print()

# Detailed analysis: which (r, k) pairs have d1Sufficient working?
print("=" * 60)
print("Complete compatibility matrix")
print("=" * 60)

print("        ", end="")
for k in K10:
    print(f" k={k:2d}", end="")
print()

for r in MORDELL_HARD:
    print(f"r={r:3d}: ", end="")
    for k in K10:
        m = d1_modulus(k)
        t = d1_target(k)
        g = gcd(m, 840)
        if t % g == r % g:
            print("   ✓ ", end="")
        else:
            print("   . ", end="")
    print()

print()

# Now analyze: for primes p ≡ r (mod 840), how often does d1Sufficient actually hold?
# d1Sufficient requires p ≡ t (mod m) where m = 16k+12
# Given p ≡ r (mod 840), the additional constraint is p ≡ t (mod m)
# If compatible, this happens with probability 1/(m/gcd(m,840))

print("=" * 60)
print("Density analysis: fraction of primes covered")
print("=" * 60)

for r in MORDELL_HARD:
    print(f"\np ≡ {r} (mod 840):")
    for k in K10:
        m = d1_modulus(k)
        t = d1_target(k)
        g = gcd(m, 840)
        if t % g == r % g:
            sublattice = m // g
            print(f"  k={k:2d}: d1Sufficient holds for 1/{sublattice} = {100/sublattice:.2f}% of primes in this class")
