#!/usr/bin/env python3
"""
Extended case analysis including primes 3, 5, 11, 13.

From previous analysis, we need to cover:
- n even, n ≡ 4 (mod 14) = n ≡ 4 (mod 7)
- n even, n ≡ 6 (mod 14) = n ≡ 6 (mod 7)
- n even, n ≡ 8 (mod 14) = n ≡ 1 (mod 7)
- n even, n ≡ 10 (mod 14) = n ≡ 3 (mod 7)
- n even, n ≡ 12 (mod 14) = n ≡ 5 (mod 7)
"""

from math import gcd

K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

def m_k(k):
    return 4 * k + 3

def multiplicative_order(a, m):
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

def euler_phi(n):
    result = n
    temp = n
    p = 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result

def is_primitive_root(a, m):
    if gcd(a, m) != 1:
        return False
    return multiplicative_order(a, m) == euler_phi(m)

# All small primes to consider
PRIMES = [2, 3, 5, 7, 11, 13]

print("=" * 70)
print("PRIMITIVE ROOTS FOR EACH k ∈ K10")
print("=" * 70)
print()

pr_table = {}  # pr_table[k] = list of primes that are PR mod m_k
for k in K10:
    m = m_k(k)
    prs = [q for q in PRIMES if gcd(q, m) == 1 and is_primitive_root(q, m)]
    pr_table[k] = prs
    print(f"k={k:2d}, m_k={m:3d}: primitive roots in {PRIMES} are {prs}")

print()

# Offsets for x_k = n + offset
offsets = {k: k - 5 for k in K10}

print("=" * 70)
print("DIVISIBILITY CONDITIONS: q | x_k")
print("=" * 70)
print()

# For each prime q and each k, determine when q | x_k
# q | x_k = n + offset[k] iff n ≡ -offset[k] (mod q)

for q in PRIMES:
    print(f"Prime q = {q}:")
    for k in K10:
        offset = offsets[k]
        target = (-offset) % q
        print(f"  {q} | x_{k} iff n ≡ {target} (mod {q})")
    print()

# Now let's analyze all n mod lcm(2, 3, 5, 7) = 210
# But that's too many. Let's focus on the problematic cases.

print("=" * 70)
print("DETAILED ANALYSIS OF PROBLEMATIC CASES")
print("=" * 70)
print()

# The cases n even, n ≡ r (mod 7) for r ∈ {1, 3, 4, 5, 6}
# (r=0 and r=2 are already covered)

for r7 in [1, 3, 4, 5, 6]:
    print(f"Case: n even, n ≡ {r7} (mod 7)")
    print("-" * 50)

    # For n even: n ≡ 0 (mod 2)
    # For n ≡ r7 (mod 7)
    # We need to check all n mod 2*3*5*7 = 210 that satisfy these constraints

    # Find which k values have a PR factor
    witnesses = []

    for q in PRIMES:
        for k in K10:
            offset = offsets[k]
            # q | x_k iff n ≡ -offset (mod q)
            target = (-offset) % q

            # Check if this is compatible with our constraints
            # n ≡ 0 (mod 2) and n ≡ r7 (mod 7)

            if q == 2:
                # 2 | x_k iff n ≡ -offset (mod 2)
                # n is even, so n ≡ 0 (mod 2)
                # So 2 | x_k iff offset is even
                if offset % 2 == 0:
                    if is_primitive_root(2, m_k(k)):
                        witnesses.append((2, k, "always (offset even)"))
            elif q == 7:
                # Already handled in previous analysis
                if r7 == target:
                    if is_primitive_root(7, m_k(k)):
                        witnesses.append((7, k, f"7 ≡ {target} (mod 7)"))
            else:
                # For q ∈ {3, 5, 11, 13}, n mod q can be anything
                # So for some n ≡ 0 (mod 2) ≡ r7 (mod 7), we might have q | x_k

                # The condition is: n ≡ target (mod q)
                # Combined with n ≡ 0 (mod 2) and n ≡ r7 (mod 7)
                # By CRT, there exists such n iff the conditions are compatible
                # They're always compatible since gcd(q, 14) = 1 for q ∈ {3, 5, 11, 13}

                if is_primitive_root(q, m_k(k)):
                    witnesses.append((q, k, f"when n ≡ {target} (mod {q})"))

    if witnesses:
        print(f"  Potential witnesses:")
        for q, k, cond in witnesses:
            print(f"    q={q}, k={k}: {cond}")
    else:
        print(f"  NO primitive root witnesses found!")

    print()

# Let's be more systematic: for each problematic (n mod 2, n mod 7) pair,
# find which (n mod 3, n mod 5) give witnesses

print("=" * 70)
print("COMPLETE COVERAGE CHECK MOD 210")
print("=" * 70)
print()

# For each n mod 210, check if there's a witness
all_covered = True
uncovered = []

for n_mod_210 in range(210):
    # Check if this is a problematic case
    n_mod_2 = n_mod_210 % 2
    n_mod_7 = n_mod_210 % 7

    # Skip non-problematic cases (odd n, or n ≡ 0, 2 mod 7 when even)
    if n_mod_2 == 1:
        continue  # Odd n: covered by k=14
    if n_mod_7 in [0, 2]:
        continue  # Even n with 7 | x_k for some k with 7 as PR

    # This is a problematic case
    n_mod_3 = n_mod_210 % 3
    n_mod_5 = n_mod_210 % 5

    witnesses = []

    for q in PRIMES:
        for k in K10:
            offset = offsets[k]
            target = (-offset) % q

            # Check if q | x_k for this n
            n_mod_q = n_mod_210 % q
            if n_mod_q == target:
                # q | x_k
                if is_primitive_root(q, m_k(k)):
                    witnesses.append((q, k))

    if not witnesses:
        uncovered.append(n_mod_210)
        all_covered = False

if all_covered:
    print("ALL cases mod 210 are covered by primitive root witnesses!")
else:
    print(f"UNCOVERED cases mod 210: {uncovered}")
    print(f"Number of uncovered cases: {len(uncovered)}")
    print()

    # Analyze uncovered cases
    for n_mod_210 in uncovered[:10]:
        print(f"n ≡ {n_mod_210} (mod 210):")
        print(f"  n ≡ {n_mod_210 % 2} (mod 2)")
        print(f"  n ≡ {n_mod_210 % 3} (mod 3)")
        print(f"  n ≡ {n_mod_210 % 5} (mod 5)")
        print(f"  n ≡ {n_mod_210 % 7} (mod 7)")

        # Check which primes divide which x_k
        for k in K10:
            offset = offsets[k]
            x_k_mod_210 = (n_mod_210 + offset) % 210
            factors = []
            for q in PRIMES:
                if x_k_mod_210 % q == 0:
                    factors.append(q)
            print(f"    x_{k} ≡ {x_k_mod_210} (mod 210), small factors: {factors}")

        print()

print("=" * 70)
print("SUMMARY")
print("=" * 70)
print()
print("To prove ten_k_cover_exists, we need to show that every n mod 210")
print("has at least one k ∈ K10 with a witness d.")
print()
print(f"Cases covered by single-prime primitive roots: {210 - len(uncovered)} / 210")
print(f"Cases requiring deeper analysis: {len(uncovered)} / 210")
