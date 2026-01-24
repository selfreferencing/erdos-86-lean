#!/usr/bin/env python3
"""
Analyze: for primes where ALL d1Sufficient conditions fail,
what can we say about QRSufficient?

Key question: Is there a pattern that guarantees QRSufficient for at least one k?
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

# m_k = 4k + 3 (Bradford modulus)
def m_k(k):
    return 4 * k + 3

# x_k = (p + m_k) / 4 for Mordell-hard primes
def x_k(p, k):
    return (p + m_k(k)) // 4

print("=" * 70)
print("ANALYSIS: QRSufficient when d1Sufficient fails everywhere")
print("=" * 70)
print()

# The k values where d1 can work for Mordell-hard primes:
# k=5, 7, 11, 14, 17, 19, 23, 26 (k=9 and k=29 never work)
WORKING_D1_KS = [5, 7, 11, 14, 17, 19, 23, 26]

print("k values where d1Sufficient is compatible with Mordell-hard primes:")
print(f"  {WORKING_D1_KS}")
print("k values where d1Sufficient NEVER works for Mordell-hard primes:")
print(f"  k=9 (mod 12 mismatch), k=29 (mod 28 mismatch)")
print()

# For a prime p, d1Sufficient fails for all k iff:
# For each k in WORKING_D1_KS: p ≢ 12k+5 (mod 16k+12)

# The moduli for working k values
working_d1_moduli = {k: (d1_modulus(k), d1_target(k)) for k in WORKING_D1_KS}

print("d1Sufficient moduli and targets for working k values:")
for k, (mod, tgt) in working_d1_moduli.items():
    print(f"  k={k:2d}: p ≡ {tgt:3d} (mod {mod:3d})")
print()

# The residue classes where d1 fails for k are:
# For p ≡ r (mod 840), d1 fails for k iff r ≢ t_k (mod gcd(m_k, 840))

# Let's compute the joint modulus for the d1 conditions
d1_mods = [d1_modulus(k) for k in WORKING_D1_KS]
joint_d1_mod = lcm_list(d1_mods)
print(f"LCM of d1 moduli for working k values: {joint_d1_mod}")

# That's too big. Let's work with a smaller combined modulus.
# We'll combine with 840 using smaller pieces.

# Key insight: The x_k values satisfy x_k = x_5 + (k - 5)
# So x_5, x_7, x_9, x_11, x_14, x_17, x_19, x_23, x_26, x_29 are:
# n, n+2, n+4, n+6, n+9, n+12, n+14, n+18, n+21, n+24
# where n = x_5 = (p + 23) / 4

print()
print("=" * 70)
print("The x_k coupling structure")
print("=" * 70)
print()
print("x_k values relative to x_5 = n:")
offsets = {k: k - 5 for k in K10}
for k in K10:
    print(f"  k={k:2d}: x_k = n + {offsets[k]:2d},  m_k = {m_k(k):3d}")
print()

# For QRSufficient(k, p) to hold, we need:
#   ∃ d | x_k², d ≤ x_k, d ≡ -x_k (mod m_k)
#
# For this to FAIL (obstruction), we need:
#   All prime factors of x_k are QR mod m_k, AND -x_k is NQR mod m_k

# The key question: can all 10 obstructions hold simultaneously?

print("=" * 70)
print("Obstruction conditions")
print("=" * 70)
print()

# For each k, the obstruction is:
# AllQR_k: every prime q | x_k is QR mod m_k
# TargetNQR_k: -x_k is NQR mod m_k

# Let's think about small prime factors.
# From QR_ANALYSIS_DATA.md, we computed which small primes are NQR for which m_k.

# NQR table (from earlier analysis):
nqr_table = {
    2: [14, 23],      # 2 is NQR mod m_k for k in {14, 23}
    3: [7, 19],       # 3 is NQR mod m_k for k in {7, 19}
    5: [7, 14, 17, 19],
    7: [5, 17, 19, 23, 26],
}

print("Small primes that are NQR mod m_k:")
for q, ks in nqr_table.items():
    ms = [m_k(k) for k in ks]
    print(f"  q={q}: NQR mod m_k for k ∈ {ks} (m_k = {ms})")
print()

# If q | x_k and q is NQR mod m_k, then AllQR_k is FALSE, so obstruction fails.
# This means k "survives" (could have a witness).

# The offsets of x_k from x_5 = n are:
# k=5: 0, k=7: 2, k=9: 4, k=11: 6, k=14: 9, k=17: 12, k=19: 14, k=23: 18, k=26: 21, k=29: 24

print("=" * 70)
print("Divisibility analysis: which x_k values have small prime factors?")
print("=" * 70)
print()

# For n = x_5 (unknown), consider n mod small primes.
# x_k = n + offset[k]
#
# 2 | x_k iff (n + offset[k]) ≡ 0 (mod 2)
# Since offset[14]=9 (odd) and offset[23]=18 (even):
# 2 | x_14 iff n is odd
# 2 | x_23 iff n is even
# So ALWAYS at least one of x_14, x_23 is even.
# Since 2 is NQR for both k=14 and k=23, at least one obstruction fails!

print("CRITICAL FINDING:")
print("-" * 50)
print("2 | x_14 iff n is odd  (since x_14 = n + 9)")
print("2 | x_23 iff n is even (since x_23 = n + 18)")
print()
print("Since 2 is NQR mod m_14=59 AND NQR mod m_23=95,")
print("at least one of Obs_14 or Obs_23 ALWAYS fails!")
print()
print("But wait - this doesn't directly give QRSufficient.")
print("Obstruction failure means AllQR fails, not that a witness exists.")
print("-" * 50)
print()

# Actually, the logic is more subtle:
# If 2 | x_k and 2 is NQR mod m_k, then:
#   - Not all prime factors of x_k are QR mod m_k
#   - So the QR obstruction (AllQR ∧ TargetNQR) is FALSE
#   - This means there MIGHT be a witness d, but doesn't guarantee it

# The correct approach: if 2 | x_k and 2 is NQR mod m_k, then
# the divisor d = 2^a (power of 2) has some chance of satisfying d ≡ -x_k (mod m_k)

# Let's think about this more carefully.
# If x_k = 2^a * m where m is odd, then divisors of x_k² include all 2^b for 0 ≤ b ≤ 2a.
# We need 2^b ≡ -x_k (mod m_k).
# Since 2 is NQR mod m_k, the powers 2^b cycle through a subgroup of index 2.
# If -x_k is in that subgroup, we get a witness; if not, we don't.

print("Refined analysis:")
print("-" * 50)
print("When 2 | x_k and 2 is NQR mod m_k:")
print("  - 2 generates a subgroup H of (Z/m_k)× of index 2")
print("  - If -x_k ∈ H, then some 2^b ≡ -x_k (mod m_k)")
print("  - If -x_k ∉ H, then no power-of-2 divisor works")
print()
print("We need: for the k where 2 | x_k, either -x_k ∈ ⟨2⟩, or")
print("there's another small prime factor giving a witness.")
print("-" * 50)
print()

# Let's check: for k=14 (m_14=59) and k=23 (m_23=95):
# What is the order of 2 mod 59? And mod 95?

def multiplicative_order(a, m):
    """Compute the multiplicative order of a mod m."""
    if gcd(a, m) != 1:
        return None
    order = 1
    power = a % m
    while power != 1:
        power = (power * a) % m
        order += 1
        if order > m:
            return None  # Should never happen for valid input
    return order

order_2_mod_59 = multiplicative_order(2, 59)
order_2_mod_95 = multiplicative_order(2, 95)

print(f"Order of 2 mod 59: {order_2_mod_59}")
print(f"Order of 2 mod 95: {order_2_mod_95}")
print(f"φ(59) = {59-1}, φ(95) = {(5-1)*(19-1)} = {4*18}")
print()

# The subgroup ⟨2⟩ has |⟨2⟩| = order of 2.
# If order = φ(m)/2, then ⟨2⟩ is exactly the QR subgroup.
# If order = φ(m), then ⟨2⟩ = (Z/m)× (2 is a primitive root).

if order_2_mod_59 == 58:
    print("2 is a primitive root mod 59 → ⟨2⟩ = (Z/59)×")
    print("So every nonzero residue is a power of 2.")
    print("This means: if 2 | x_14, we can ALWAYS find 2^b ≡ -x_14 (mod 59)!")
elif order_2_mod_59 == 29:
    print("ord(2) = 29 = φ(59)/2 → ⟨2⟩ = QR subgroup of index 2")
else:
    print(f"ord(2) = {order_2_mod_59}, index = {58 // order_2_mod_59}")

print()

# Let's also check the elements of ⟨2⟩ mod 59
print("Powers of 2 mod 59:")
powers = [pow(2, i, 59) for i in range(order_2_mod_59)]
print(f"  First 15: {powers[:15]}")
print(f"  All {len(powers)} elements: {sorted(powers)}")
print()

# Since 2 is a primitive root mod 59, ⟨2⟩ = (Z/59)×, which has 58 elements.
# This means for ANY x_14 coprime to 59, we can find 2^b ≡ -x_14 (mod 59).
# And since x_14 ≠ 0 (it's large), x_14 is coprime to 59.

print("=" * 70)
print("KEY THEOREM CANDIDATE")
print("=" * 70)
print()
print("Claim: 2 is a primitive root mod 59.")
print()
print("Proof: ord(2) = 58 = φ(59) ✓")
print()
print("Consequence: For any Mordell-hard prime p with n = x_5 odd,")
print("we have 2 | x_14 = n + 9, and since 2 is a primitive root mod 59,")
print("there exists b with 2^b ≡ -x_14 (mod 59).")
print()
print("If 2^b ≤ x_14 (which is true for small b), then d = 2^b is a witness!")
print()
print("This covers half of all Mordell-hard primes (those with n odd).")
print()

# Now check k=23 for the other half
print("=" * 70)
print("Analysis for k=23 (m_23 = 95 = 5 × 19)")
print("=" * 70)
print()

# For composite m = 5 × 19, we use CRT.
# ⟨2⟩ mod 5: ord(2) = 4 = φ(5), so 2 is primitive root mod 5
# ⟨2⟩ mod 19: ord(2) = ?

order_2_mod_5 = multiplicative_order(2, 5)
order_2_mod_19 = multiplicative_order(2, 19)

print(f"Order of 2 mod 5: {order_2_mod_5} (φ(5)={4})")
print(f"Order of 2 mod 19: {order_2_mod_19} (φ(19)={18})")
print()

# ord(2) mod 95 = lcm(ord(2) mod 5, ord(2) mod 19)
print(f"Order of 2 mod 95 = lcm({order_2_mod_5}, {order_2_mod_19}) = {lcm(order_2_mod_5, order_2_mod_19)}")
print()

# ⟨2⟩ mod 95 has |⟨2⟩| = 36 elements
# (Z/95)× has φ(95) = 72 elements
# So ⟨2⟩ has index 2 in (Z/95)×

print("⟨2⟩ has index 2 in (Z/95)×.")
print("This means: only half of residues mod 95 are powers of 2.")
print()
print("For -x_23 to be a power of 2 mod 95, we need:")
print("  - (-x_23 mod 5) ∈ ⟨2⟩ mod 5 = {1,2,3,4} = (Z/5)×  ✓ (always true)")
print("  - (-x_23 mod 19) ∈ ⟨2⟩ mod 19")
print()

# What is ⟨2⟩ mod 19?
print(f"ord(2) mod 19 = {order_2_mod_19}")
if order_2_mod_19 == 18:
    print("2 is a primitive root mod 19 → ⟨2⟩ = (Z/19)×")
else:
    powers_19 = [pow(2, i, 19) for i in range(order_2_mod_19)]
    print(f"⟨2⟩ mod 19 = {sorted(powers_19)} ({len(powers_19)} elements)")
    non_powers = [i for i in range(1, 19) if i not in powers_19]
    print(f"Non-powers of 2 mod 19 = {non_powers}")
print()

# Since 2 is a primitive root mod 19, ⟨2⟩ mod 19 = (Z/19)×
# So ⟨2⟩ mod 95 should equal (Z/95)×... but we computed index 2!
# Let me recheck.

print("Recomputing ⟨2⟩ mod 95...")
powers_95 = set()
p = 1
for i in range(100):
    powers_95.add(p)
    p = (p * 2) % 95
    if p == 1:
        break
print(f"Number of elements in ⟨2⟩ mod 95: {len(powers_95)}")
print(f"φ(95) = {4 * 18} = 72")
print()

# Wait, I think I made an error. Let me recalculate.
# 2 is primitive root mod 5 (ord = 4 = φ(5))
# 2 is primitive root mod 19 (ord = 18 = φ(19))
# So by CRT, ord(2) mod 95 = lcm(4, 18) = 36, not 72.
# ⟨2⟩ mod 95 has 36 elements, index 2 in (Z/95)×.

# But wait - 2 is primitive root mod both 5 and 19.
# The issue is that the orders might not combine to give a primitive root.
# lcm(4, 18) = 36 < 72 = 4 * 18.

# Hmm, this means ⟨2⟩ mod 95 is NOT all of (Z/95)×.
# So there exist residues that are not powers of 2 mod 95.

print("ISSUE: ⟨2⟩ mod 95 has only 36 elements (index 2).")
print("So not every -x_23 is a power of 2 mod 95.")
print()
print("We need a different approach for k=23 when n is even.")
print()

# The good news is that for k=14 and n odd, we have a full solution.
# For k=23 and n even, we need additional analysis.

# Let's check if there are OTHER small primes that help with k=23.
# From the NQR table: 2, 7 are NQR mod 95.

print("=" * 70)
print("Additional factors for k=23")
print("=" * 70)
print()
print("NQR primes mod 95: {2, 7}")
print()
print("x_23 = n + 18 where n = x_5")
print()
print("When n is even:")
print("  x_23 = even + 18 = even")
print("  So 2 | x_23")
print()
print("But we also need to check if 7 | x_k for some k.")
print()

# 7 is NQR for k ∈ {5, 17, 19, 23, 26}
# x_5 = n, x_17 = n+12, x_19 = n+14, x_23 = n+18, x_26 = n+21
# 7 | x_k iff n ≡ -offset[k] (mod 7)

print("Checking when 7 | x_k for k where 7 is NQR mod m_k:")
for k in [5, 17, 19, 23, 26]:
    offset = k - 5
    target = (-offset) % 7
    print(f"  k={k:2d}: 7 | x_k iff n ≡ {target} (mod 7)")
print()

# So:
# 7 | x_5 iff n ≡ 0 (mod 7)
# 7 | x_17 iff n ≡ 2 (mod 7)  [since -12 ≡ 2 (mod 7)]
# 7 | x_19 iff n ≡ 0 (mod 7)  [since -14 ≡ 0 (mod 7)]
# 7 | x_23 iff n ≡ 3 (mod 7)  [since -18 ≡ 3 (mod 7)]
# 7 | x_26 iff n ≡ 0 (mod 7)  [since -21 ≡ 0 (mod 7)]

# This means for n ≡ 0 (mod 7): 7 | x_5, x_19, x_26 (all have 7 as NQR factor)
# For n ≡ 2 (mod 7): 7 | x_17
# For n ≡ 3 (mod 7): 7 | x_23

# Combined with the parity analysis:
# n even: 2 | x_23
# n odd: 2 | x_14

# And 7 conditions:
# n ≡ 0 (mod 7): 7 | x_5, x_19, x_26
# n ≡ 2 (mod 7): 7 | x_17
# n ≡ 3 (mod 7): 7 | x_23

# For n odd and any residue mod 7:
#   2 | x_14 and 2 is primitive root mod 59 → k=14 works!

# For n even:
#   2 | x_23 and we need -x_23 ∈ ⟨2⟩ mod 95
#   OR we need 7 | x_k for some k with 7 NQR

print("=" * 70)
print("Combined analysis: n even")
print("=" * 70)
print()

for r7 in range(7):
    print(f"n even, n ≡ {r7} (mod 7):")
    factors = []
    if r7 == 0:
        factors.extend([(7, 5), (7, 19), (7, 26)])
    elif r7 == 2:
        factors.append((7, 17))
    elif r7 == 3:
        factors.append((7, 23))
    factors.append((2, 23))  # 2 | x_23 always when n is even
    print(f"  NQR factors: {factors}")
    print()

print("Conclusion:")
print("For n even, we always have 2 | x_23 (and 2 is NQR mod 95).")
print("If 7 is a primitive root mod the relevant m_k, we get witnesses from 7^b too.")
print()

# Check if 7 is primitive root mod relevant moduli
for k in [5, 17, 19, 23, 26]:
    m = m_k(k)
    if gcd(7, m) > 1:
        print(f"k={k:2d}: 7 | m_k = {m}, so 7 is not a unit")
    else:
        o = multiplicative_order(7, m)
        phi = m - 1 if gcd(m, 6) == 1 else None  # Simplified for primes
        # Actually compute φ(m)
        if m == 23 or m == 31 or m == 47 or m == 59 or m == 71 or m == 79 or m == 107:
            phi = m - 1
        elif m == 39:
            phi = 24  # (3-1)*(13-1)
        elif m == 95:
            phi = 72  # (5-1)*(19-1)
        elif m == 119:
            phi = 96  # (7-1)*(17-1)
        print(f"k={k:2d}: ord(7) mod {m} = {o}, φ({m}) = {phi}")
