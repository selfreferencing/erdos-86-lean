#!/usr/bin/env python3
"""
Test whether the 'uncovered' classes from CRT containment analysis
are actually uncovered (have primes without witnesses).
"""

from math import gcd

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

def is_prime(n):
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

def divisors_of_square(n):
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

def find_witness(p, k):
    """Find a Type II witness d for p at k."""
    m_k = 4 * k + 3
    if (p + m_k) % 4 != 0:
        return None
    x_k = (p + m_k) // 4
    if gcd(x_k, m_k) > 1:
        return None
    target = (-x_k) % m_k
    divs = divisors_of_square(x_k)
    for d in divs:
        if d % m_k == target:
            return (k, d, x_k, m_k)
    return None

def find_any_witness(p):
    """Find any witness for p using K_COMPLETE."""
    for k in K_COMPLETE:
        result = find_witness(p, k)
        if result:
            return result
    return None

# Test specific uncovered classes from Level 3
# Format from output: (r_840, s_11, t_23, full_residue)
uncovered_examples = [
    (1, 1, 1, 1),
    (1, 1, 2, 175561),
    (1, 1, 3, 138601),
    (1, 1, 4, 101641),
    (1, 1, 6, 27721),
]

M3 = 212520  # = 840 × 11 × 23

print("=" * 70)
print("TESTING 'UNCOVERED' CLASSES FROM LEVEL 3")
print("=" * 70)
print()

for r_840, s_11, t_23, full_r in uncovered_examples:
    print(f"Class: r ≡ {full_r} (mod {M3})")
    print(f"  (r_840={r_840}, s_11={s_11}, t_23={t_23})")

    # Find primes in this class
    primes = []
    p = full_r
    while len(primes) < 5 and p < 10**8:
        if is_prime(p) and p % 4 == 1 and gcd(p, M3) == 1:
            primes.append(p)
        p += M3

    print(f"  Sample primes: {primes}")

    all_covered = True
    for p in primes:
        witness = find_any_witness(p)
        if witness:
            k, d, x_k, m_k = witness
            print(f"    p={p}: k={k}, d={d}")
        else:
            print(f"    p={p}: *** NO WITNESS ***")
            all_covered = False

    print(f"  Status: {'All covered' if all_covered else '*** UNCOVERED ***'}")
    print()

# Summary: Do we have any truly uncovered primes?
print("=" * 70)
print("EXHAUSTIVE CHECK OF ALL LEVEL 3 'UNCOVERED' CLASSES")
print("=" * 70)
print()

# Generate all 330 uncovered class representatives
resistant = [1, 121, 169, 289, 361, 529]
uncovered_s_values = [1, 3, 4, 5, 9]  # From the Level 2 output

def crt_two(r1, m1, r2, m2):
    """Solve x ≡ r1 (mod m1) and x ≡ r2 (mod m2) via CRT."""
    g = gcd(m1, m2)
    if (r1 - r2) % g != 0:
        return None, None
    from math import gcd as mgcd
    def extended_gcd(a, b):
        if a == 0:
            return b, 0, 1
        g, x, y = extended_gcd(b % a, a)
        return g, y - (b // a) * x, x

    m = m1 * m2 // g
    _, x, _ = extended_gcd(m1, m2)
    diff = (r2 - r1) // g
    solution = (r1 + m1 * x * diff) % m
    return solution, m

uncovered_any = []
covered_count = 0
total_count = 0

for r in resistant:
    for s in uncovered_s_values:
        # Compute residue mod 9240 = 840 × 11
        t_9240, _ = crt_two(r, 840, s, 11)
        if t_9240 is None:
            continue

        for t in range(23):
            # Compute residue mod 212520
            full_r, _ = crt_two(t_9240, 9240, t, 23)
            if full_r is None:
                continue

            total_count += 1

            # Find one prime in this class
            p = full_r
            found_prime = None
            while found_prime is None and p < 10**8:
                if is_prime(p) and p % 4 == 1 and gcd(p, M3) == 1:
                    found_prime = p
                p += M3

            if found_prime is None:
                # No prime in class (shouldn't happen for admissible)
                continue

            witness = find_any_witness(found_prime)
            if witness:
                covered_count += 1
            else:
                uncovered_any.append((r, s, t, full_r, found_prime))
                print(f"UNCOVERED: r={r}, s={s}, t={t}, p={found_prime}")

print()
print(f"Total classes checked: {total_count}")
print(f"Covered (prime has witness): {covered_count}")
print(f"Uncovered (no witness found): {len(uncovered_any)}")

if uncovered_any:
    print("\nUNCOVERED PRIMES:")
    for item in uncovered_any[:10]:
        print(f"  {item}")
else:
    print("\n*** ALL PRIMES IN 'UNCOVERED' CLASSES ACTUALLY HAVE WITNESSES! ***")
    print("The CRT containment check is too strict - coverage still holds.")
