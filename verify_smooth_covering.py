#!/usr/bin/env python3
"""
Verify complete covering at Q_smooth = 857,656,800 using D6 + smooth DP congruences.

Q = 2^5 * 3^2 * 5^2 * 7^2 * 11 * 13 * 17 = 857,656,800
"""

import time
from math import gcd
from collections import defaultdict


def lcm2(a, b):
    return a * b // gcd(a, b)


def divisors(n):
    if n <= 0: return []
    small, large = [], []
    i = 1
    while i * i <= n:
        if n % i == 0:
            small.append(i)
            if i != n // i:
                large.append(n // i)
        i += 1
    return small + large[::-1]


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def get_residues_for_M(M):
    k = (M + 1) // 4
    if 4 * k - 1 != M:
        return set()
    seen = set()
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            res = (-4 * a * s * s) % M
            seen.add(res)
    return seen


# ═══════════════════════════════════════════════════════════════════
# The 24 smooth DP congruences from dp_minimal_moduli.py
# Format: (target_prime, target_qr, u, v, delta, modulus, residue)
# ═══════════════════════════════════════════════════════════════════

SMOOTH_DP = [
    # Prime 5 QR classes
    (5, 1, 4, 35, 39, 560, 521),       # r≡1 mod 5
    (5, 4, 70, 1, 71, 280, 209),       # r≡4 mod 5
    # Prime 7 QR classes
    (7, 1, 20, 35, 55, 560, 505),      # r≡1 mod 7
    (7, 2, 42, 5, 47, 840, 793),       # r≡2 mod 7
    (7, 4, 14, 17, 31, 952, 921),      # r≡4 mod 7
    # Prime 11 QR classes
    (11, 1, 10, 77, 87, 3080, 2993),   # r≡1 mod 11
    (11, 3, 8, 55, 63, 1760, 1697),    # r≡3 mod 11
    (11, 4, 40, 55, 95, 1760, 1665),   # r≡4 mod 11
    (11, 5, 28, 11, 39, 1232, 1193),   # r≡5 mod 11
    (11, 9, 2, 77, 79, 616, 537),      # r≡9 mod 11
    # Prime 13 QR classes
    (13, 1, 26, 77, 103, 8008, 7905),  # r≡1 mod 13
    (13, 3, 10, 13, 23, 520, 497),     # r≡3 mod 13
    (13, 4, 22, 65, 87, 5720, 5633),    # r≡4 mod 13 (smooth: 2^3*5*11*13)
    (13, 9, 4, 91, 95, 1456, 1361),    # r≡9 mod 13
    (13, 10, 260, 3, 263, 3120, 2857), # r≡10 mod 13 (smooth: 2^4*3*5*13)
    (13, 12, 182, 1, 183, 728, 545),   # r≡12 mod 13
    # Prime 17 QR classes
    (17, 1, 50, 85, 135, 3400, 3265),  # r≡1 mod 17
    (17, 2, 238, 49, 287, 6664, 6377), # r≡2 mod 17
    (17, 4, 34, 13, 47, 1768, 1721),   # r≡4 mod 17
    (17, 8, 26, 221, 247, 1768, 1521), # r≡8 mod 17
    (17, 9, 8, 119, 127, 3808, 3681),  # r≡9 mod 17
    (17, 13, 4, 187, 191, 2992, 2801), # r≡13 mod 17 (smooth: 2^4*11*17)
    (17, 15, 2, 85, 87, 680, 593),     # r≡15 mod 17
    (17, 16, 238, 1, 239, 952, 713),   # r≡16 mod 17
]


def verify_dp_smoothness():
    """Verify all DP moduli are 17-smooth."""
    q1_primes = {2, 3, 5, 7, 11, 13, 17}
    print("Verifying DP modulus smoothness:")
    all_smooth = True
    for tp, tr, u, v, delta, mod, res in SMOOTH_DP:
        n = mod
        factors = set()
        d = 2
        while d * d <= n:
            while n % d == 0:
                factors.add(d)
                n //= d
            d += 1
        if n > 1:
            factors.add(n)
        new_primes = factors - q1_primes
        if new_primes:
            print(f"  NOT SMOOTH: p={tp}, r={tr}, mod={mod}, factors={factors}, "
                  f"new={new_primes}")
            all_smooth = False
    if all_smooth:
        print("  All 24 DP moduli are 17-smooth!")
    return all_smooth


def compute_Q():
    """Compute Q = lcm(Q1, all DP moduli)."""
    Q1 = 30_630_600
    Q = Q1
    for _, _, _, _, _, mod, _ in SMOOTH_DP:
        Q = lcm2(Q, mod)
    return Q


def main():
    t0 = time.time()

    # Step 0: Verify smoothness
    print("=" * 80)
    if not verify_dp_smoothness():
        print("ERROR: Non-smooth DP entries found! Aborting.")
        return

    # Step 1: Compute Q
    Q = compute_Q()
    print(f"\nQ = {Q:,}")
    n = Q
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    print(f"Q = " + " * ".join(f"{p}^{e}" if e > 1 else str(p)
                                 for p, e in sorted(factors.items())))

    # Step 2: Build D6 data
    print(f"\n{'=' * 80}")
    print("Building D6 coverage data...")
    oQ = odd_part(Q)
    M_values = sorted([d for d in divisors(oQ) if d % 4 == 3 and d >= 3])
    print(f"D6 M-values: {len(M_values)}")

    M_data = {}
    for M in M_values:
        residues = get_residues_for_M(M)
        if residues:
            M_data[M] = residues
    print(f"D6 M-values with residues: {len(M_data)}")

    # Step 3: Build DP coverage lookup
    # For each DP congruence, precompute (modulus, residue)
    dp_congruences = [(mod, res) for _, _, _, _, _, mod, res in SMOOTH_DP]
    print(f"DP congruences: {len(dp_congruences)}")

    # Step 4: Verify coverage
    print(f"\n{'=' * 80}")
    print(f"Verifying complete coverage mod Q = {Q:,}")
    print(f"Iterating over {Q // 24:,} candidate values (step 24)...")
    print("=" * 80)

    target_count = 0
    d6_count = 0
    dp_count = 0
    uncovered = []
    
    check_interval = Q // 240  # report every ~0.4%
    next_report = check_interval

    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        target_count += 1

        # Check D6
        covered = False
        for M in M_data:
            if x % M in M_data[M]:
                covered = True
                d6_count += 1
                break

        if not covered:
            # Check DP
            for mod, res in dp_congruences:
                if x % mod == res:
                    covered = True
                    dp_count += 1
                    break

        if not covered:
            uncovered.append(x)
            if len(uncovered) <= 20:
                print(f"  UNCOVERED: x = {x} "
                      f"(mod5={x%5}, mod7={x%7}, mod11={x%11}, mod13={x%13}, mod17={x%17})")

        if x > next_report:
            pct = 100 * x / Q
            elapsed = time.time() - t0
            eta = elapsed / (pct / 100) - elapsed if pct > 0 else 0
            print(f"  Progress: {pct:.1f}% ({target_count:,} targets, "
                  f"{d6_count:,} D6, {dp_count:,} DP, "
                  f"{len(uncovered)} uncov) [elapsed {elapsed:.0f}s, ETA {eta:.0f}s]")
            next_report += check_interval

    # Results
    print(f"\n{'=' * 80}")
    print("RESULTS")
    print("=" * 80)
    print(f"Q = {Q:,}")
    print(f"Total target classes: {target_count:,}")
    print(f"D6 covered: {d6_count:,}")
    print(f"DP covered: {dp_count:,}")
    print(f"Uncovered: {len(uncovered)}")

    if not uncovered:
        print(f"\n*** COMPLETE COVERING VERIFIED! ***")
        print(f"*** Every coprime class ≡ 1 (mod 24) mod {Q:,} is covered! ***")
    else:
        print(f"\n{len(uncovered)} classes remain uncovered:")
        for x in uncovered[:50]:
            print(f"  x={x}: mod5={x%5}, mod7={x%7}, mod11={x%11}, "
                  f"mod13={x%13}, mod17={x%17}")
        if len(uncovered) > 50:
            print(f"  ... and {len(uncovered) - 50} more")
        
        # Analyze patterns
        print("\nResidue patterns of uncovered:")
        for p in [5, 7, 11, 13, 17]:
            dist = defaultdict(int)
            for x in uncovered:
                dist[x % p] += 1
            print(f"  mod {p}: {dict(sorted(dist.items()))}")

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
