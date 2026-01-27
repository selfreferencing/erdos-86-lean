#!/usr/bin/env python3
"""
Covering search v5: Complete covering via D6 + ALL divisor-pair congruences
whose moduli divide Q.

Strategy:
  1. Build D6 covering at Q = 30,630,600 = 2^3 * 3^2 * 5^2 * 7 * 11 * 13 * 17
  2. Q/4 = 7,657,650. Enumerate ALL (u,v) pairs with lcm(u,v) | Q/4
  3. For each pair, the DP congruence P ≡ -(u+v) (mod 4*lcm(u,v)) covers
     a residue class. Collect all such congruences.
  4. Check if D6 + DP covers 100% of coprime targets mod Q.
  5. If not, try enlarging Q by small primes.
"""

import time
from math import gcd
from collections import defaultdict


def lcm2(a, b):
    return a * b // gcd(a, b)


def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True


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


def factorize(n):
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


# ═══════════════════════════════════════════════════════════════════
# Lemma D.6
# ═══════════════════════════════════════════════════════════════════

def get_residues_for_M(M):
    k = (M + 1) // 4
    if 4 * k - 1 != M:
        return set()
    seen = set()
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            r = rem // s
            res = (-4 * a * s * s) % M
            seen.add(res)
    return seen


def get_triples_for_M(M):
    k = (M + 1) // 4
    if 4 * k - 1 != M:
        return []
    seen = set()
    triples = []
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            r = rem // s
            res = (-4 * a * s * s) % M
            if res not in seen:
                seen.add(res)
                triples.append((r, s, a, res))
    return triples


# ═══════════════════════════════════════════════════════════════════
# Divisor-pair congruences with moduli dividing Q
# ═══════════════════════════════════════════════════════════════════

def enumerate_dp_congruences(Q, max_delta=5000):
    """
    Find ALL divisor-pair congruences P ≡ -(u+v) (mod 4*lcm(u,v))
    where 4*lcm(u,v) | Q and u+v ≡ 3 (mod 4).

    For the (u,v) divisor-pair construction:
      - delta = u + v (the offset), must be ≡ 3 (mod 4)
      - A = (P + delta)/4
      - Need u | A and v | A
      - Congruence: P ≡ -delta (mod 4*lcm(u,v))
      - b = A/u, c = A/v satisfies (P+delta)(b+c) = 4*delta*b*c
    """
    Q4 = Q // 4
    divs_Q4 = divisors(Q4)
    divs_Q4_set = set(divs_Q4)

    congruences = []  # (modulus, residue, delta, u, v)
    seen = set()

    # Strategy: enumerate pairs (u, v) where both u and v divide some
    # divisor of Q4, and lcm(u,v) divides Q4.
    # Since Q4 = 7,657,650 has 288 divisors, we enumerate pairs of divisors.

    count = 0
    for u in divs_Q4:
        for v in divs_Q4:
            if v < u:
                continue  # avoid duplicates (u,v) and (v,u) give same congruence
            delta = u + v
            if delta % 4 != 3:
                continue
            if delta > max_delta:
                continue
            L = lcm2(u, v)
            if L not in divs_Q4_set:
                continue
            modulus = 4 * L
            res = (-delta) % modulus

            # Check compatibility with P ≡ 1 (mod 24)
            g = gcd(modulus, 24)
            if res % g != 1 % g:
                continue

            key = (modulus, res)
            if key not in seen:
                seen.add(key)
                congruences.append((modulus, res, delta, u, v))
                count += 1

    # Also enumerate non-symmetric (u, v) with u > v
    for u in divs_Q4:
        for v in divs_Q4:
            if v >= u:
                continue
            delta = u + v
            if delta % 4 != 3:
                continue
            if delta > max_delta:
                continue
            L = lcm2(u, v)
            if L not in divs_Q4_set:
                continue
            modulus = 4 * L
            res = (-delta) % modulus

            g = gcd(modulus, 24)
            if res % g != 1 % g:
                continue

            key = (modulus, res)
            if key not in seen:
                seen.add(key)
                congruences.append((modulus, res, delta, u, v))
                count += 1

    return congruences


def enumerate_dp_extended(Q, max_delta=10000):
    """
    Extended DP search: u and v don't both need to be divisors of Q/4.
    We need lcm(u,v) | Q/4, which means:
    - For each prime p | Q/4 with p^e || Q/4, we need max(v_p(u), v_p(v)) <= e
    - u and v can only have prime factors dividing Q/4

    This allows much larger u, v values (not just divisors of Q/4).
    """
    Q4 = Q // 4
    facs = factorize(Q4)
    primes = sorted(facs.keys())

    # For efficiency, enumerate u values that are "smooth" w.r.t. Q4's primes
    # and bounded, then for each u, check if delta-u works.
    divs_Q4_set = set(divisors(Q4))

    congruences = []
    seen = set()

    # For each delta ≡ 3 (mod 4), find u with u | Q4 and (delta-u) | Q4
    # But we want lcm(u, delta-u) | Q4.

    # More efficient: iterate over divisor pairs
    divs_Q4 = divisors(Q4)

    for u in divs_Q4:
        for v in divs_Q4:
            delta = u + v
            if delta % 4 != 3:
                continue
            if delta > max_delta:
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
                congruences.append((modulus, res, delta, u, v))

    return congruences


# ═══════════════════════════════════════════════════════════════════
# Phase 1: Build D6 covering
# ═══════════════════════════════════════════════════════════════════

def build_d6_covering(Q):
    """Compute D6 coverage at given Q."""
    oQ = odd_part(Q)
    M_values = [d for d in divisors(oQ) if d % 4 == 3 and d >= 3]

    M_data = {}
    for M in M_values:
        residues = get_residues_for_M(M)
        if residues:
            M_data[M] = residues

    targets = set()
    covered = set()
    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        targets.add(x)
        for M in M_data:
            if x % M in M_data[M]:
                covered.add(x)
                break

    return M_data, targets, covered


# ═══════════════════════════════════════════════════════════════════
# Phase 2: Add DP coverage
# ═══════════════════════════════════════════════════════════════════

def add_dp_coverage(Q, targets, already_covered, dp_congruences):
    """Check which additional targets are covered by DP congruences."""
    dp_covered = set()
    dp_witness = {}  # residue -> (mod, res, delta, u, v)

    for x in targets:
        if x in already_covered:
            continue
        for modulus, res, delta, u, v in dp_congruences:
            if Q % modulus != 0:
                continue
            if x % modulus == res:
                dp_covered.add(x)
                dp_witness[x] = (modulus, res, delta, u, v)
                break

    return dp_covered, dp_witness


# ═══════════════════════════════════════════════════════════════════
# Phase 3: Analyze uncovered classes
# ═══════════════════════════════════════════════════════════════════

def analyze_uncovered(Q, uncovered):
    """Analyze residue patterns of uncovered classes."""
    primes_in_Q = [p for p in sorted(factorize(Q).keys()) if p > 2]

    print(f"\nResidue distribution of {len(uncovered)} uncovered classes:")
    for M in primes_in_Q:
        dist = defaultdict(int)
        for x in uncovered:
            dist[x % M] += 1
        print(f"  mod {M:>3}: {dict(sorted(dist.items()))}")


# ═══════════════════════════════════════════════════════════════════
# Phase 4: Verify with actual primes
# ═══════════════════════════════════════════════════════════════════

def ed2_check(P, r, s, alpha):
    M = 4 * alpha * s * r - 1
    val = 4 * alpha * s * s + P
    if val % M != 0:
        return None
    m = val // M
    c_prime = m * r - s
    if c_prime <= 0:
        return None
    A = alpha * s * c_prime
    L = (P + 3) // 4
    U = (3 * P - 3) // 4
    if A < L or A > U:
        return None
    offset = 4 * A - P
    g = alpha * r
    b = g * s
    c = g * c_prime
    if offset % 4 != 3 or b <= 0 or c <= 0:
        return None
    if (P + offset) * (b + c) != 4 * offset * b * c:
        return None
    return (offset, b, c, A)


def verify_primes(Q, M_d6_data, dp_witness, max_P=500_000):
    """Verify all primes P ≡ 1 (mod 24) up to max_P."""
    checked = 0
    by_d6 = 0
    by_dp = 0
    by_search = 0
    failures = []

    for P in range(25, max_P + 1, 24):
        if not is_prime(P):
            continue
        checked += 1
        found = False
        r_mod_Q = P % Q

        # Try D6
        for M, residues in M_d6_data.items():
            if P % M not in residues:
                continue
            triples = get_triples_for_M(M)
            for r, s, alpha, res in triples:
                if P % M == res:
                    result = ed2_check(P, r, s, alpha)
                    if result is not None:
                        found = True
                        by_d6 += 1
                        break
            if found:
                break

        # Try DP witness
        if not found and r_mod_Q in dp_witness:
            modulus, res, delta, u, v = dp_witness[r_mod_Q]
            if (P + delta) % 4 == 0:
                A = (P + delta) // 4
                if A % u == 0 and A % v == 0:
                    b = A // u
                    c = A // v
                    if b > 0 and c > 0 and (P + delta) * (b + c) == 4 * delta * b * c:
                        found = True
                        by_dp += 1

        # Direct search fallback
        if not found:
            for delta in range(3, 501, 4):
                if (P + delta) % 4 != 0:
                    continue
                A = (P + delta) // 4
                divs_A = divisors(A)
                divs_set = set(divs_A)
                for uu in divs_A:
                    if uu >= delta:
                        break
                    vv = delta - uu
                    if vv > 0 and vv in divs_set:
                        bb = A // uu
                        cc = A // vv
                        if (P + delta) * (bb + cc) == 4 * delta * bb * cc:
                            found = True
                            by_search += 1
                            break
                if found:
                    break

        if not found:
            failures.append(P)

    return checked, by_d6, by_dp, by_search, failures


# ═══════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    # ──────────────────────────────────────────────────────────
    # Phase 1: D6 covering
    # ──────────────────────────────────────────────────────────
    print("=" * 80)
    print("PHASE 1: Building D6 covering")
    print("=" * 80)

    # Build Q incrementally
    Q = 24
    for f in [5, 7, 9, 11, 13, 17, 25]:
        Q = lcm2(Q, f)

    print(f"Q = {Q:,}")
    print(f"Q factorization: ", end="")
    facs = factorize(Q)
    print(" * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(facs.items())))
    print(f"Q/4 = {Q//4:,}")
    print(f"Divisors of Q/4: {len(divisors(Q//4))}")

    M_d6_data, targets, d6_covered = build_d6_covering(Q)
    d6_uncovered = targets - d6_covered
    d6_pct = 100.0 * len(d6_covered) / len(targets)

    print(f"\nD6 coverage: {len(d6_covered):,}/{len(targets):,} = {d6_pct:.4f}%")
    print(f"Uncovered by D6: {len(d6_uncovered):,}")
    print(f"D6 M-values used: {len(M_d6_data)}")

    # ──────────────────────────────────────────────────────────
    # Phase 2: DP congruences
    # ──────────────────────────────────────────────────────────
    print(f"\n{'=' * 80}")
    print("PHASE 2: Finding DP congruences with moduli dividing Q")
    print("=" * 80)

    dp_congs = enumerate_dp_extended(Q, max_delta=50000)
    print(f"Total DP congruences (moduli | Q): {len(dp_congs)}")

    # Show modulus distribution
    mod_dist = defaultdict(int)
    for mod, res, delta, u, v in dp_congs:
        mod_dist[mod] += 1
    print(f"Distinct moduli: {len(mod_dist)}")
    for mod in sorted(mod_dist.keys())[:20]:
        print(f"  mod {mod}: {mod_dist[mod]} congruences")
    if len(mod_dist) > 20:
        print(f"  ... and {len(mod_dist) - 20} more moduli")

    dp_covered, dp_witness = add_dp_coverage(Q, targets, d6_covered, dp_congs)
    combined = d6_covered | dp_covered
    final_uncov = targets - combined
    combined_pct = 100.0 * len(combined) / len(targets)

    print(f"\nDP covers {len(dp_covered):,} additional classes")
    print(f"Combined: {len(combined):,}/{len(targets):,} = {combined_pct:.6f}%")
    print(f"Still uncovered: {len(final_uncov):,}")

    if final_uncov:
        analyze_uncovered(Q, final_uncov)

        # ──────────────────────────────────────────────────────────
        # Phase 3: Try enlarging Q
        # ──────────────────────────────────────────────────────────
        print(f"\n{'=' * 80}")
        print("PHASE 3: Trying enlarged Q values")
        print("=" * 80)

        for extra in [19, 23, 29, 31, 37, 41, 43]:
            if Q % extra == 0:
                continue
            Q2 = Q * extra
            print(f"\n  Q2 = Q * {extra} = {Q2:,}")

            M_d6_2, targets2, d6_cov2 = build_d6_covering(Q2)
            d6_uncov2 = targets2 - d6_cov2
            print(f"    D6: {len(d6_cov2):,}/{len(targets2):,} = {100*len(d6_cov2)/len(targets2):.4f}%")

            dp_congs2 = enumerate_dp_extended(Q2, max_delta=50000)
            dp_cov2, dp_wit2 = add_dp_coverage(Q2, targets2, d6_cov2, dp_congs2)
            combined2 = d6_cov2 | dp_cov2
            uncov2 = targets2 - combined2
            print(f"    D6+DP: {len(combined2):,}/{len(targets2):,} = {100*len(combined2)/len(targets2):.6f}%")
            print(f"    Still uncovered: {len(uncov2):,}")

            if not uncov2:
                print(f"\n    *** COMPLETE COVERING at Q = {Q2:,} ***")
                Q = Q2
                M_d6_data = M_d6_2
                targets = targets2
                d6_covered = d6_cov2
                dp_covered = dp_cov2
                dp_witness = dp_wit2
                combined = combined2
                final_uncov = set()
                break

            if len(uncov2) < len(final_uncov):
                analyze_uncovered(Q2, uncov2)

    # ──────────────────────────────────────────────────────────
    # Phase 4: Prime verification
    # ──────────────────────────────────────────────────────────
    complete = (len(final_uncov) == 0)

    print(f"\n{'=' * 80}")
    print(f"PHASE 4: Verifying primes up to 500,000")
    print("=" * 80)

    checked, by_d6, by_dp, by_search, failures = verify_primes(
        Q, M_d6_data, dp_witness, max_P=500_000
    )

    print(f"Checked: {checked:,} primes")
    print(f"  By D6:     {by_d6:,}")
    print(f"  By DP:     {by_dp:,}")
    print(f"  By search: {by_search:,}")
    if failures:
        print(f"  FAILURES:  {len(failures)}: {failures[:20]}")
    else:
        print(f"  ALL {checked:,} PRIMES VERIFIED!")

    # ──────────────────────────────────────────────────────────
    # Summary
    # ──────────────────────────────────────────────────────────
    print(f"\n{'=' * 80}")
    print("SUMMARY")
    print("=" * 80)
    print(f"Q = {Q:,}")
    facs = factorize(Q)
    print(f"  = " + " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(facs.items())))
    print(f"Target classes (coprime, ≡1 mod 24): {len(targets):,}")
    print(f"D6 covered: {len(d6_covered):,}")
    print(f"DP covered: {len(dp_covered):,}")
    print(f"Total covered: {len(combined):,}")
    print(f"Uncovered: {len(final_uncov):,}")
    print(f"Complete: {'YES' if complete else 'NO'}")

    if complete:
        # Count distinct DP witnesses
        dp_mods_used = set()
        dp_deltas_used = set()
        for x, (mod, res, delta, u, v) in dp_witness.items():
            dp_mods_used.add(mod)
            dp_deltas_used.add(delta)
        print(f"\nDP details:")
        print(f"  Distinct moduli used: {len(dp_mods_used)}")
        print(f"  Distinct deltas used: {len(dp_deltas_used)}")

        # Non-coprime primes
        print(f"\nNon-coprime primes (P | Q, P ≡ 1 mod 24):")
        for p in sorted(facs.keys()):
            if p >= 5 and is_prime(p) and p % 24 == 1:
                print(f"  P = {p}")

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
