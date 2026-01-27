#!/usr/bin/env python3
"""
Deep structural analysis of uncovered residue classes at Q = 857,656,800.

Reproduces uncovered classes from verify_full_dp.py (D6 + DP logic),
then analyzes their quadratic residue structure, Legendre symbols,
and D6 residue gaps to guide finding additional covering methods.
"""

import time
from math import gcd, isqrt
from collections import defaultdict

# ── helpers ──────────────────────────────────────────────────────────────

def lcm2(a, b):
    return a * b // gcd(a, b)

def divisors(n):
    if n <= 0:
        return []
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

def legendre(a, p):
    """Legendre symbol (a|p) for odd prime p."""
    a = a % p
    if a == 0:
        return 0
    val = pow(a, (p - 1) // 2, p)
    return val if val <= 1 else -1

def is_qr(a, p):
    """Is a a quadratic residue mod p? (including 0)"""
    return legendre(a, p) >= 0

def euler_phi(n):
    """Euler's totient function."""
    result = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result

# ── D6 residue computation ──────────────────────────────────────────────

def get_residues_for_M(M):
    """Compute D6 residues: -4*alpha*s^2 mod M where M = 4*alpha*s*r - 1."""
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

# ── DP congruence computation ───────────────────────────────────────────

def compute_dp_congruences(Q):
    """Enumerate all DP congruences for Q."""
    Q4 = Q // 4
    divs_Q4 = divisors(Q4)
    dp_congruences = []
    seen = set()
    for u in divs_Q4:
        for v in divs_Q4:
            delta = u + v
            if delta % 4 != 3:
                continue
            L = lcm2(u, v)
            if Q4 % L != 0:
                continue
            modulus = 4 * L
            res = (-delta) % modulus
            g = gcd(modulus, 24)
            if res % g != 1 % g:
                continue
            key = (modulus, res)
            if key not in seen:
                seen.add(key)
                dp_congruences.append((modulus, res))
    return dp_congruences

# ── main analysis ───────────────────────────────────────────────────────

def main():
    t0 = time.time()
    Q = 857_656_800
    Q4 = Q // 4
    oQ = odd_part(Q)

    PRIMES = [3, 5, 7, 11, 13, 17]
    PRIMES_3MOD4 = [3, 7, 11]   # primes that are 3 mod 4

    print("=" * 80)
    print("STRUCTURAL ANALYSIS OF UNCOVERED CLASSES")
    print(f"Q = {Q:,}   odd(Q) = {oQ:,}")
    print("=" * 80)

    # ── Step 0: Factor Q ─────────────────────────────────────────────────
    print(f"\nFactoring Q = {Q}...")
    temp = Q
    factors_Q = []
    d = 2
    while d * d <= temp:
        if temp % d == 0:
            e = 0
            while temp % d == 0:
                e += 1
                temp //= d
            factors_Q.append((d, e))
        d += 1
    if temp > 1:
        factors_Q.append((temp, 1))
    print(f"  Q = {' * '.join(f'{p}^{e}' if e > 1 else str(p) for p,e in factors_Q)}")
    print(f"  odd(Q) = {oQ}")

    # ── Step 1: Build D6 M-values and residues ───────────────────────────
    print(f"\nBuilding D6 data...")
    M_values = sorted([d for d in divisors(oQ) if d % 4 == 3 and d >= 3])
    M_data = {}
    for M in M_values:
        res = get_residues_for_M(M)
        if res:
            M_data[M] = res
    print(f"  {len(M_data)} M-values with residues (from {len(M_values)} candidates)")
    print(f"  M-values: {M_values[:20]}{'...' if len(M_values) > 20 else ''}")

    # ── Step 2: Build DP congruences ─────────────────────────────────────
    print(f"\nBuilding DP congruences...")
    dp_congruences = compute_dp_congruences(Q)
    print(f"  {len(dp_congruences)} DP congruences")

    # ── Step 3: Single pass to collect uncovered classes ──────────────────
    print(f"\nScanning for uncovered classes (x in 1..Q, x ≡ 1 mod 24, gcd(x,Q)=1)...")

    uncovered = []
    total_targets = 0
    d6_count = 0
    dp_count = 0

    check_interval = Q // 24   # ~10 progress reports
    next_report = check_interval

    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        total_targets += 1

        # D6 check
        found = False
        for M, residues in M_data.items():
            if x % M in residues:
                found = True
                d6_count += 1
                break

        if not found:
            # DP check
            for mod, res in dp_congruences:
                if x % mod == res:
                    found = True
                    dp_count += 1
                    break

        if not found:
            uncovered.append(x)

        if x > next_report:
            elapsed = time.time() - t0
            pct = 100 * x / Q
            print(f"  {pct:.0f}%  targets={total_targets:,}  "
                  f"d6={d6_count:,}  dp={dp_count:,}  uncov={len(uncovered)}  "
                  f"[{elapsed:.0f}s]")
            next_report += check_interval

    t_scan = time.time() - t0
    print(f"\nScan complete in {t_scan:.1f}s")
    print(f"  Targets: {total_targets:,}")
    print(f"  D6 covered: {d6_count:,} ({100*d6_count/total_targets:.4f}%)")
    print(f"  DP covered: {dp_count:,} ({100*dp_count/total_targets:.4f}%)")
    print(f"  Uncovered: {len(uncovered)}")

    if not uncovered:
        print("\n*** COMPLETE COVERAGE! Nothing to analyze. ***")
        return

    # ══════════════════════════════════════════════════════════════════════
    # ANALYSIS OF UNCOVERED CLASSES
    # ══════════════════════════════════════════════════════════════════════

    print("\n" + "=" * 80)
    print("PART A: QUADRATIC RESIDUE STRUCTURE OF UNCOVERED CLASSES")
    print("=" * 80)

    # For each uncovered x, compute Legendre symbols and QR status mod small primes
    qr_all_count = 0       # QR mod ALL of {3,5,7,11,13,17}
    qr_stats = {p: 0 for p in PRIMES}    # count of QR mod p
    legendre_stats = {p: defaultdict(int) for p in PRIMES_3MOD4}
    perfect_sq_count = 0

    # Track which primes make x a QNR
    qnr_pattern = defaultdict(int)   # frozenset of primes where QNR -> count

    for x in uncovered:
        # QR checks
        qr_set = set()
        qnr_set = set()
        for p in PRIMES:
            if is_qr(x, p):
                qr_stats[p] += 1
                qr_set.add(p)
            else:
                qnr_set.add(p)

        if len(qr_set) == len(PRIMES):
            qr_all_count += 1

        qnr_pattern[frozenset(qnr_set)] += 1

        # Legendre symbols for primes 3 mod 4
        for p in PRIMES_3MOD4:
            L = legendre(x, p)
            legendre_stats[p][L] += 1

        # Perfect square check
        sq = isqrt(x)
        if sq * sq == x:
            perfect_sq_count += 1

    N = len(uncovered)
    print(f"\nTotal uncovered classes: {N}")

    print(f"\n--- QR mod individual primes ---")
    for p in PRIMES:
        cnt = qr_stats[p]
        print(f"  QR mod {p:2d}: {cnt:6d} / {N} = {100*cnt/N:.2f}%  "
              f"(expected ~{100*(p+1)/(2*p):.1f}% for QR+0)")

    print(f"\n--- QR mod ALL of {PRIMES} ---")
    print(f"  {qr_all_count} / {N} = {100*qr_all_count/N:.2f}%")

    print(f"\n--- Legendre symbols for primes ≡ 3 mod 4 ---")
    for p in PRIMES_3MOD4:
        stats = legendre_stats[p]
        print(f"  (x|{p:2d}):  +1: {stats[1]:6d}   -1: {stats[-1]:6d}   0: {stats[0]:6d}")

    print(f"\n--- Perfect squares ---")
    print(f"  {perfect_sq_count} / {N} uncovered classes are perfect squares")

    print(f"\n--- QNR pattern distribution (top 15) ---")
    sorted_patterns = sorted(qnr_pattern.items(), key=lambda t: -t[1])
    for pat, cnt in sorted_patterns[:15]:
        label = "{" + ",".join(str(p) for p in sorted(pat)) + "}" if pat else "{}"
        print(f"  QNR at {label:25s}: {cnt:6d} ({100*cnt/N:.2f}%)")

    # ══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 80)
    print("PART B: D6 RESIDUES MOD SMALL PRIMES")
    print("=" * 80)

    # For each small prime p, compute the EXACT set of D6 residues mod p
    # using ALL M values that are 3 mod 4 dividing odd(Q)
    print(f"\nComputing D6 residue images mod small primes...")

    for p in PRIMES:
        d6_residues_mod_p = set()
        for M, residues in M_data.items():
            for r in residues:
                d6_residues_mod_p.add(r % p)
        # QNR mod p
        qnr_mod_p = set()
        for a in range(1, p):
            if legendre(a, p) == -1:
                qnr_mod_p.add(a)
        # Which QNR mod p are NOT D6 residues?
        qnr_not_d6 = qnr_mod_p - d6_residues_mod_p
        qnr_in_d6 = qnr_mod_p & d6_residues_mod_p
        print(f"\n  p = {p}:")
        print(f"    D6 residues mod {p}: {sorted(d6_residues_mod_p)} ({len(d6_residues_mod_p)}/{p} classes)")
        print(f"    QNR mod {p}: {sorted(qnr_mod_p)}")
        print(f"    QNR that ARE D6 residues: {sorted(qnr_in_d6)}")
        print(f"    QNR NOT in D6 residues: {sorted(qnr_not_d6)}")

    # ══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 80)
    print("PART C: WHY D6 MISSES SPECIFIC CLASSES")
    print("=" * 80)

    # For uncovered x that is QNR mod some p in {3,7,11}:
    # identify which M should cover it and check why D6 missed
    print(f"\nFor primes p ≡ 3 mod 4 in {{3, 7, 11}}, checking why D6 misses QNR classes...")

    # Group uncovered by residue mod small moduli
    for p in PRIMES_3MOD4:
        print(f"\n  --- Analysis for p = {p} ---")
        # M values divisible by p (or with M % p specific structure)
        relevant_Ms = [M for M in M_data if M % p == 0]
        print(f"    M-values divisible by {p}: {len(relevant_Ms)}")
        if relevant_Ms:
            print(f"      Examples: {relevant_Ms[:10]}")

        # For x QNR mod p, the D6 residue -4*alpha*s^2 mod M
        # must also be QNR mod p.
        # Since -4*alpha*s^2 = -(2s)^2 * alpha, its QR character mod p
        # depends on alpha mod p.
        # (-(2s)^2 * alpha | p) = (-1|p) * (alpha|p)
        # For p ≡ 3 mod 4: (-1|p) = -1
        # So (D6 residue | p) = -(alpha|p)
        # D6 residue is QNR mod p iff alpha is QR mod p.

        if p in PRIMES_3MOD4:
            print(f"    Key identity: (-4*alpha*s^2 | {p}) = (-1|{p}) * (alpha|{p})")
            print(f"      (-1|{p}) = {legendre(-1, p)}")
            print(f"      So D6 residue is QNR mod {p} iff alpha is QR mod {p}")

    # ══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 80)
    print("PART D: FIRST 100 UNCOVERED VALUES")
    print("=" * 80)

    first100 = uncovered[:100]
    sq_in_100 = 0
    print(f"\nFirst {len(first100)} uncovered values:")
    for i, x in enumerate(first100):
        sq = isqrt(x)
        is_sq = (sq * sq == x)
        if is_sq:
            sq_in_100 += 1
        mods = "  ".join(f"mod{p}={x%p}" for p in PRIMES)
        leg = "  ".join(f"({x}|{p})={legendre(x,p):+d}" for p in PRIMES_3MOD4)
        sq_mark = " [SQUARE]" if is_sq else ""
        if i < 30:
            print(f"  x={x:>12,d}:  {mods}  {sq_mark}")

    if len(first100) > 30:
        print(f"  ... ({len(first100) - 30} more)")
    print(f"\n  Perfect squares in first 100: {sq_in_100}")

    # ══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 80)
    print("PART E: RESIDUE CLASS DISTRIBUTION OF UNCOVERED")
    print("=" * 80)

    # Distribution mod various moduli
    for mod_val in [3, 5, 7, 8, 11, 13, 15, 17, 21, 24, 35, 105, 840]:
        dist = defaultdict(int)
        for x in uncovered:
            dist[x % mod_val] += 1
        vals = sorted(dist.items())
        n_classes = len(vals)
        if n_classes <= 30:
            print(f"\n  mod {mod_val} ({n_classes} classes populated):")
            for r, c in vals:
                bar = "#" * min(c * 50 // max(v for _, v in vals), 50) if vals else ""
                print(f"    {r:4d}: {c:6d}  {bar}")
        else:
            print(f"\n  mod {mod_val}: {n_classes} classes populated out of {mod_val}")

    # ══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 80)
    print("PART F: SUMMARY AND COVERING GAP CHARACTERIZATION")
    print("=" * 80)

    # Characterize what the uncovered classes look like
    print(f"\nTotal uncovered: {N}")
    print(f"QR mod ALL of {PRIMES}: {qr_all_count} ({100*qr_all_count/N:.2f}%)")
    print(f"Perfect squares: {perfect_sq_count}")

    # Check: are all uncovered classes QR mod ALL primes dividing Q?
    q_prime_factors = [p for p, e in factors_Q if p > 2]
    qr_all_q_primes = 0
    for x in uncovered:
        if all(is_qr(x, p) for p in q_prime_factors):
            qr_all_q_primes += 1
    print(f"QR mod ALL prime factors of Q ({q_prime_factors}): "
          f"{qr_all_q_primes} / {N} = {100*qr_all_q_primes/N:.2f}%")

    # Check Jacobi symbol (x | odd(Q))
    # Jacobi = product of Legendre over prime factors
    jacobi_plus = 0
    jacobi_minus = 0
    for x in uncovered:
        j = 1
        for p, e in factors_Q:
            if p == 2:
                continue
            j *= legendre(x, p) ** e
        if j == 1:
            jacobi_plus += 1
        else:
            jacobi_minus += 1
    print(f"\nJacobi symbol (x | odd(Q)):")
    print(f"  +1: {jacobi_plus}   -1: {jacobi_minus}")

    # Specific guidance
    print(f"\n--- STRUCTURAL CHARACTERIZATION ---")
    if qr_all_count == N:
        print("ALL uncovered classes are QR mod every small prime.")
        print("These are the 'Mordell-hard' cases: perfect-square-like residues.")
        print("Additional identity types needed: possibly Type I (k-based) or Type III.")
    elif qr_all_count == 0:
        print("NO uncovered classes are QR mod all small primes.")
        print("Every uncovered class is QNR mod at least one prime.")
        print("D6 should theoretically cover these. Investigate M-value gaps.")
    else:
        print(f"{qr_all_count} uncovered are QR-everywhere (Mordell-hard).")
        print(f"{N - qr_all_count} are QNR mod some prime (should be D6-coverable).")
        print("Two gaps to close:")
        print("  1. D6 M-value coverage gaps for QNR classes")
        print("  2. Additional identity for Mordell-hard (QR-everywhere) classes")

    print(f"\nTotal elapsed: {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
