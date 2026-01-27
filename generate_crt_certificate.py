#!/usr/bin/env python3
"""
Generate the CRT certificate for the offset covering.

For each (k, d) pair, the conditions:
  - p ≡ -(k+d) (mod 4k)  [so c = (p+k+d)/(4k) is integer]
  - p ≡ -k (mod d)       [so d | (p+k)]

give a specific residue class of p. We need pairs covering all p ≡ 1 (mod 4).
"""

import math
from collections import defaultdict

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def lcm(a, b):
    return a * b // gcd(a, b)

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0: return False
    return True

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def crt(r1, m1, r2, m2):
    """Solve x ≡ r1 (mod m1) and x ≡ r2 (mod m2). Returns (r, m) or None."""
    g = gcd(m1, m2)
    if (r2 - r1) % g != 0:
        return None  # No solution
    m = lcm(m1, m2)
    _, x, _ = extended_gcd(m1, m2)
    r = (r1 + m1 * ((r2 - r1) // g) * x) % m
    return r, m

def get_residue_class(k, d):
    """
    For pair (k, d), compute the residue class of p covered.
    Conditions:
      - p ≡ -(k+d) (mod 4k)
      - p ≡ -k (mod d)
      - p ≡ 1 (mod 4)
    """
    # Condition 1: p ≡ -(k+d) (mod 4k)
    r1 = (-(k + d)) % (4 * k)
    m1 = 4 * k

    # Condition 2: p ≡ -k (mod d)
    r2 = (-k) % d
    m2 = d

    # Combine with CRT
    result = crt(r1, m1, r2, m2)
    if result is None:
        return None
    r12, m12 = result

    # Condition 3: p ≡ 1 (mod 4)
    result = crt(r12, m12, 1, 4)
    if result is None:
        return None

    return result  # (residue, modulus)

def find_solution(P, max_offset=100, max_c=50000):
    """Find (k, c, d) for prime P."""
    for k in range(3, max_offset, 4):  # k ≡ 3 (mod 4)
        for c in range(1, max_c):
            d = (4*c - 1) * k - P
            if d <= 0:
                continue
            target = (P + k) * c * P
            if target % d == 0:
                return k, c, d
    return None, None, None

def main():
    print("GENERATING CRT CERTIFICATE")
    print("=" * 60)

    # Step 1: Collect all (k, d) pairs used
    primes = [p for p in range(5, 100001) if is_prime(p) and p % 4 == 1]
    print(f"Processing {len(primes)} primes...")

    kd_pairs = defaultdict(list)  # (k, d) -> [primes]

    for i, P in enumerate(primes):
        if i % 1000 == 0:
            print(f"  Progress: {i}/{len(primes)}")
        k, c, d = find_solution(P)
        if k is not None:
            kd_pairs[(k, d)].append(P)

    print(f"\nFound {len(kd_pairs)} distinct (k, d) pairs")

    # Step 2: Analyze each pair
    print("\n" + "=" * 60)
    print("ANALYZING (k, d) PAIRS")
    print("=" * 60)

    # Sort by frequency
    sorted_pairs = sorted(kd_pairs.items(), key=lambda x: -len(x[1]))

    valid_certificates = []

    for (k, d), prime_list in sorted_pairs[:50]:
        result = get_residue_class(k, d)
        if result:
            r, m = result
            # Verify: all primes in the list should satisfy p ≡ r (mod m)
            all_match = all(p % m == r for p in prime_list)
            valid_certificates.append((k, d, r, m, len(prime_list), all_match))

            if len(prime_list) >= 10:
                check = "✓" if all_match else "✗"
                print(f"(k={k:2d}, d={d:4d}): p ≡ {r:4d} (mod {m:4d}), {len(prime_list):4d} primes {check}")

    # Step 3: Build minimal covering
    print("\n" + "=" * 60)
    print("BUILDING MINIMAL CRT COVERING")
    print("=" * 60)

    # Find a common modulus M that's manageable
    # Start with residue classes mod 840 (= lcm(4, 3, 5, 7, 8))
    M = 840
    target_residues = {r for r in range(M) if r % 4 == 1}
    print(f"Target: cover all {len(target_residues)} residue classes ≡ 1 (mod 4) in Z/{M}Z")

    covered = set()
    selected = []

    # Greedy selection
    for (k, d, r, m, count, valid) in sorted(valid_certificates, key=lambda x: -x[4]):
        if not valid:
            continue
        # Which residues mod M does this cover?
        new_covered = set()
        for res in target_residues:
            if res % m == r % m:
                new_covered.add(res)

        newly_covered = new_covered - covered
        if newly_covered:
            selected.append((k, d, r, m, len(newly_covered)))
            covered |= new_covered
            print(f"Select (k={k}, d={d}): r≡{r} (mod {m}), covers {len(newly_covered)} new, total {len(covered)}/{len(target_residues)}")

            if covered == target_residues:
                print("\n✓ COMPLETE COVERING FOUND!")
                break

    if covered != target_residues:
        uncovered = target_residues - covered
        print(f"\n✗ Incomplete: {len(uncovered)} residues uncovered")
        print(f"  Uncovered: {sorted(uncovered)[:20]}...")

        # Try to find pairs for uncovered residues
        print("\nSearching for pairs to cover remaining residues...")
        for r in sorted(uncovered)[:5]:
            # Find a prime in this residue class
            for p in primes:
                if p % M == r:
                    k, c, d = find_solution(p)
                    if k:
                        print(f"  r={r}: P={p} uses (k={k}, d={d})")
                    break

    # Step 4: Output the certificate
    print("\n" + "=" * 60)
    print("FINAL CRT CERTIFICATE")
    print("=" * 60)
    print(f"Modulus M = {M}")
    print(f"Certificate has {len(selected)} pairs:")
    for k, d, r, m, count in selected:
        c_formula = f"(p + {k} + {d}) / {4*k}"
        print(f"  (k={k:2d}, d={d:4d}): p ≡ {r:4d} (mod {m:4d}), c = {c_formula}")

if __name__ == "__main__":
    main()
