#!/usr/bin/env python3
"""
Covering search v4: Find minimal modulus N for complete case-split proof.

Strategy: For each candidate modulus N, check if EVERY residue class
p ≡ r (mod N) with r ≡ 1 (mod 24) and gcd(r,N)=1 can be handled by
either Lemma D.6 or the divisor-pair construction.

For each class, record the explicit witness construction.

Key insight from v3: The divisor-pair method with parameters (alpha, beta)
gives p = 4*alpha*beta*m - alpha - beta, yielding:
  offset = alpha + beta, b = beta*m, c = alpha*m
where m = (p + alpha + beta) / (4*alpha*beta).

This works when 4*alpha*beta | (p + alpha + beta).
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
    small = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            small.append(i)
            if i != n // i:
                small.append(n // i)
        i += 1
    return sorted(small)


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def get_d6_residues_for_M(M, max_alpha=20, max_s=40, max_r=40):
    """Get all D6 residues mod M."""
    residues = set()
    # M = 4*alpha*s*r - 1, so alpha*s*r = (M+1)/4
    if (M + 1) % 4 != 0:
        return residues
    target = (M + 1) // 4
    # Find all factorizations alpha*s*r = target
    for alpha in divisors(target):
        if alpha > max_alpha:
            continue
        rem = target // alpha
        for s in divisors(rem):
            if s > max_s:
                continue
            r = rem // s
            if r > max_r:
                continue
            res = (-4 * alpha * s * s) % M
            residues.add(res)
    return residues


def get_dp_congruences(max_sum=200, max_product=5000):
    """
    Get all divisor-pair congruences with small moduli.

    DP pair (alpha, beta) with gcd(alpha,beta)=1, one even, alpha+beta ≡ 7 (mod 8):
    Modulus = 4*alpha*beta
    Residue = -(alpha+beta) mod (4*alpha*beta)
    """
    congruences = []  # (modulus, residue, alpha, beta)
    seen_mod_res = set()

    for s in range(7, max_sum + 1, 8):  # s = alpha + beta ≡ 7 (mod 8)
        for alpha in range(2, s, 2):  # alpha even
            beta = s - alpha
            if beta <= 0:
                continue
            if gcd(alpha, beta) != 1:
                continue
            prod = alpha * beta
            if prod > max_product:
                continue
            modulus = 4 * prod
            residue = (-s) % modulus
            key = (modulus, residue)
            if key not in seen_mod_res:
                seen_mod_res.add(key)
                congruences.append((modulus, residue, alpha, beta))

    # Also include odd-odd pairs with alpha+beta ≡ 3 (mod 4)
    # But both odd means sum is even, can't be ≡ 3 mod 4. Skip.

    return congruences


def check_coverage_mod_N(N, d6_data, dp_congruences, verbose=False):
    """
    Check if all target classes mod N are covered by D6 or DP.

    Returns (is_complete, coverage_details).
    """
    # Target: r ≡ 1 (mod 24), gcd(r, N) = 1
    targets = set()
    for r in range(1, N, 24):
        if gcd(r, N) == 1:
            targets.add(r)

    if not targets:
        return True, {}

    covered = {}  # r -> construction info

    # Check D6 coverage
    oN = odd_part(N)
    M_values = [d for d in divisors(oN) if d % 4 == 3 and d >= 3]

    for r in targets:
        for M in M_values:
            residues = d6_data.get(M)
            if residues is None:
                residues = get_d6_residues_for_M(M)
                d6_data[M] = residues
            if r % M in residues:
                covered[r] = ('D6', M, r % M)
                break

    # Check DP coverage for remaining
    uncovered = targets - set(covered.keys())

    for r in list(uncovered):
        for modulus, residue, alpha, beta in dp_congruences:
            if N % modulus == 0 or modulus % N == 0 or True:
                # Check if r ≡ residue (mod gcd(N, modulus))
                g = gcd(N, modulus)
                if r % g == residue % g:
                    # More precise: check if there's x with x ≡ r (mod N) and x ≡ residue (mod modulus)
                    # This exists iff r ≡ residue (mod gcd(N, modulus))
                    if modulus % N == 0:
                        # modulus is multiple of N, so x ≡ r (mod N) and x ≡ residue (mod modulus)
                        # exists iff residue ≡ r (mod N)
                        if residue % N == r:
                            covered[r] = ('DP', modulus, residue, alpha, beta)
                            uncovered.discard(r)
                            break
                    elif N % modulus == 0:
                        # N is multiple of modulus
                        if r % modulus == residue:
                            covered[r] = ('DP', modulus, residue, alpha, beta)
                            uncovered.discard(r)
                            break
                    else:
                        # General case: use CRT compatibility
                        if r % g == residue % g:
                            # Compatible - this DP covers some primes in class r mod N
                            # But does it cover ALL primes in this class?
                            # Only if modulus | N (so every p ≡ r mod N also satisfies the DP cong)
                            # Otherwise it only covers a SUBSET.
                            # For a case-split proof, we need modulus | N.
                            pass

    uncovered = targets - set(covered.keys())

    if verbose and uncovered:
        print(f"  Mod {N}: {len(targets)} targets, {len(covered)} covered, "
              f"{len(uncovered)} uncovered")
        if len(uncovered) <= 20:
            for r in sorted(uncovered):
                factors = []
                for p in [5, 7, 11, 13, 17, 19]:
                    if N % p == 0:
                        factors.append(f"mod {p}={r % p}")
                print(f"    r={r}: {', '.join(factors)}")

    return len(uncovered) == 0, covered


def find_minimal_N_with_dp(max_N=10_000_000):
    """
    Find smallest N where all target classes are covered.

    Strategy: N must be divisible by 24. Add prime factors systematically.
    For DP coverage, N must be divisible by the DP moduli (4*alpha*beta).
    """
    print("=" * 78)
    print("PHASE 1: Finding minimal covering modulus")
    print("=" * 78)

    d6_data = {}  # cache
    dp_congruences = get_dp_congruences(max_sum=200, max_product=2000)

    print(f"Generated {len(dp_congruences)} DP congruences")
    print(f"Smallest DP moduli: {sorted(set(c[0] for c in dp_congruences))[:20]}")

    # Build N by starting with 24 and adding factors
    # For DP pairs with modulus M_dp to work, need M_dp | N
    # DP moduli: 4*alpha*beta where alpha+beta ≡ 7 (mod 8)
    # Smallest: (2,5)->40, (2,13)->104, (2,21)->168, (4,11)->176, ...

    # Strategy: try N = lcm(24, dp_modulus_1, dp_modulus_2, ...)
    # Start with D6-only coverage, then add DP moduli

    # First, find D6-only coverage for small N
    base = 24
    prime_factors = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

    # Build N incrementally
    N = base
    for pf in prime_factors:
        new_N = lcm2(N, pf)
        if new_N <= max_N:
            N = new_N

    print(f"\nD6-only check with N = {N}")
    complete, covered = check_coverage_mod_N(N, d6_data, [], verbose=True)

    if complete:
        print("D6 alone covers everything!")
        return N, covered

    # Find uncovered classes
    targets = set()
    for r in range(1, N, 24):
        if gcd(r, N) == 1:
            targets.add(r)
    uncovered = targets - set(covered.keys())

    print(f"\nUncovered: {len(uncovered)} / {len(targets)} classes")

    # Now try adding DP moduli
    # For each uncovered class r, find which DP congruences could cover it
    # if their modulus divides N

    # First check: which DP moduli already divide N?
    dp_divides_N = [(m, res, a, b) for m, res, a, b in dp_congruences if N % m == 0]
    print(f"\nDP congruences with modulus | N={N}: {len(dp_divides_N)}")

    for r in sorted(uncovered):
        for modulus, residue, alpha, beta in dp_divides_N:
            if r % modulus == residue:
                covered[r] = ('DP', modulus, residue, alpha, beta)
                break

    uncovered2 = targets - set(covered.keys())
    print(f"After DP (modulus | N): {len(uncovered2)} uncovered")

    if not uncovered2:
        return N, covered

    # Try extending N with DP moduli
    print(f"\nTrying to extend N with DP moduli to cover remaining {len(uncovered2)} classes...")

    for r in sorted(uncovered2)[:10]:
        print(f"\n  Analyzing r={r} mod {N}:")
        for modulus, residue, alpha, beta in sorted(dp_congruences, key=lambda x: x[0]):
            if r % gcd(N, modulus) == residue % gcd(N, modulus):
                new_N = lcm2(N, modulus)
                if new_N <= max_N:
                    # Check if r mod new_N gives a match
                    # r is mod N; need to check which residues mod new_N
                    # correspond to r mod N and match the DP
                    matching = False
                    for x in range(r, new_N, N):
                        if x % modulus == residue:
                            matching = True
                            break
                    if matching:
                        print(f"    DP ({alpha},{beta}), mod={modulus}: "
                              f"covers r={r} in N'={new_N}")
                        break

    return N, covered


def find_direct_dp_for_residue(r, N, max_sum=500):
    """
    For a specific residue r mod N with r ≡ 1 (mod 24),
    find a DP pair whose modulus divides N and whose residue matches r.
    """
    results = []
    for s in range(7, max_sum + 1, 8):
        for alpha in range(2, s, 2):
            beta = s - alpha
            if beta <= 0 or gcd(alpha, beta) != 1:
                continue
            modulus = 4 * alpha * beta
            if N % modulus != 0:
                continue
            residue = (-s) % modulus
            if r % modulus == residue:
                results.append((modulus, residue, alpha, beta, s))
    return results


def comprehensive_search(verbose=True):
    """
    Comprehensive search: for each target N, check full coverage
    using both D6 and DP where DP moduli must divide N.
    """
    print("=" * 78)
    print("COMPREHENSIVE COVERING SEARCH")
    print("=" * 78)

    d6_data = {}

    # Generate candidate N values by multiplying 24 with small products
    # N must be divisible by 24 and by any DP moduli we want to use
    # DP modulus = 4*alpha*beta, so N must be divisible by 4*alpha*beta
    # Simplest DP: (2,5) -> modulus 40. lcm(24, 40) = 120.

    candidates = set()

    # Start with multiples of 24 that include useful DP moduli
    base_dps = [
        (2, 5, 40), (2, 13, 104), (2, 21, 168), (4, 11, 176),
        (2, 29, 232), (4, 19, 304), (6, 9, 216), (6, 17, 408),
        (2, 37, 296), (4, 27, 432), (6, 25, 600), (8, 7, 224),
        (8, 15, 480), (8, 23, 736), (10, 5, 200), (10, 13, 520),
        (10, 21, 840), (2, 45, 360), (2, 53, 424),
        (10, 29, 1160), (14, 1, 56), (6, 1, 24),
        (14, 9, 504), (14, 17, 952),
    ]

    # Filter valid DP pairs
    valid_dps = []
    for alpha, beta, mod in base_dps:
        if gcd(alpha, beta) == 1 and (alpha + beta) % 8 == 7:
            valid_dps.append((alpha, beta, mod))

    print(f"Valid DP pairs: {len(valid_dps)}")
    for a, b, m in sorted(valid_dps, key=lambda x: x[2])[:15]:
        print(f"  ({a},{b}): modulus={m}, residue={-(a+b) % m}")

    # Build candidate N values
    N_base = 24
    # Add prime factors
    for extra_primes in [
        [], [5], [7], [5,7], [5,7,11], [5,7,11,13],
        [5,7,11,13,17], [5,7,11,13,17,19],
    ]:
        N = N_base
        for p in extra_primes:
            N = lcm2(N, p)
        # For each N, also try adding DP moduli
        for a, b, m in valid_dps:
            N2 = lcm2(N, m)
            if N2 <= 50_000_000:
                candidates.add(N2)
        candidates.add(N)

    # Also try specific combinations
    for a1, b1, m1 in valid_dps:
        for a2, b2, m2 in valid_dps:
            N = lcm2(24, lcm2(m1, m2))
            if N <= 10_000_000:
                candidates.add(N)

    candidates = sorted(candidates)
    print(f"\nTesting {len(candidates)} candidate N values (up to {max(candidates):,})")

    best_N = None
    best_coverage = 0
    best_details = None

    for N in candidates:
        targets = set()
        for r in range(1, N, 24):
            if gcd(r, N) == 1:
                targets.add(r)

        if not targets:
            continue

        # D6 coverage
        covered = {}
        oN = odd_part(N)
        M_values = [d for d in divisors(oN) if d % 4 == 3 and d >= 3]

        for r in targets:
            for M in M_values:
                if M not in d6_data:
                    d6_data[M] = get_d6_residues_for_M(M)
                if r % M in d6_data[M]:
                    covered[r] = ('D6', M, r % M)
                    break

        # DP coverage (only pairs whose modulus divides N)
        uncov = targets - set(covered.keys())
        for r in list(uncov):
            for a, b, m in valid_dps:
                if N % m != 0:
                    continue
                residue = (-(a + b)) % m
                if r % m == residue:
                    covered[r] = ('DP', m, residue, a, b)
                    uncov.discard(r)
                    break

        uncov = targets - set(covered.keys())
        pct = 100 * len(covered) / len(targets)

        if pct > best_coverage or (pct == best_coverage and
                                    (best_N is None or N < best_N)):
            best_coverage = pct
            best_N = N
            best_details = (targets, covered, uncov)

        if len(uncov) == 0:
            print(f"\n*** COMPLETE COVERAGE at N = {N:,} ***")
            print(f"    {len(targets)} target classes, all covered")

            # Count by method
            d6_count = sum(1 for v in covered.values() if v[0] == 'D6')
            dp_count = sum(1 for v in covered.values() if v[0] == 'DP')
            print(f"    D6: {d6_count}, DP: {dp_count}")

            return N, targets, covered

        if verbose and N <= 1000:
            print(f"  N={N:>10,}: {len(covered)}/{len(targets)} = {pct:.1f}%, "
                  f"uncov={len(uncov)}")

    # Report best
    print(f"\nBest coverage: {best_coverage:.2f}% at N={best_N:,}")
    if best_details:
        targets, covered, uncov = best_details
        print(f"  {len(covered)}/{len(targets)} covered, {len(uncov)} uncovered")
        if len(uncov) <= 30:
            print("  Uncovered classes:")
            for r in sorted(uncov):
                info = []
                for p in [5, 7, 11, 13, 17, 19, 23]:
                    if best_N % p == 0:
                        info.append(f"mod{p}={r%p}")
                print(f"    r={r}: {', '.join(info)}")

    return best_N, best_details


def verify_with_primes(N, covered, max_P=500000):
    """Verify the covering against actual primes."""
    print(f"\n{'='*78}")
    print(f"VERIFICATION: checking primes up to {max_P:,}")
    print(f"{'='*78}")

    checked = 0
    verified_d6 = 0
    verified_dp = 0
    failures = []

    for P in range(25, max_P + 1, 24):
        if not is_prime(P):
            continue
        checked += 1

        r = P % N
        if r in covered:
            info = covered[r]
            if info[0] == 'D6':
                # Verify D6 construction works
                M = info[1]
                # Find (r, s, alpha) for this M and residue
                target_prod = (M + 1) // 4
                found = False
                for alpha in divisors(target_prod):
                    if alpha > 20:
                        continue
                    rem = target_prod // alpha
                    for s in divisors(rem):
                        if s > 40:
                            continue
                        r_val = rem // s
                        if r_val > 40:
                            continue
                        res = (-4 * alpha * s * s) % M
                        if P % M != res:
                            continue
                        # Try construction
                        val = 4 * alpha * s * s + P
                        if val % M != 0:
                            continue
                        m = val // M
                        c_prime = m * r_val - s
                        if c_prime <= 0:
                            continue
                        A = alpha * s * c_prime
                        offset = 4 * A - P
                        if offset <= 0 or offset % 4 != 3:
                            continue
                        g = alpha * r_val
                        b = g * s
                        c = g * c_prime
                        if (P + offset) * (b + c) == 4 * offset * b * c:
                            verified_d6 += 1
                            found = True
                            break
                    if found:
                        break
                if not found:
                    failures.append(('D6_fail', P, r))

            elif info[0] == 'DP':
                modulus, residue, alpha, beta = info[1], info[2], info[3], info[4]
                s = alpha + beta
                m_val = (P + s) // (4 * alpha * beta)
                if (P + s) % (4 * alpha * beta) != 0:
                    failures.append(('DP_div_fail', P, r, alpha, beta))
                    continue
                offset = s
                b = beta * m_val
                c = alpha * m_val
                if b <= 0 or c <= 0:
                    failures.append(('DP_pos_fail', P, r))
                    continue
                if (P + offset) * (b + c) != 4 * offset * b * c:
                    failures.append(('DP_eq_fail', P, r))
                    continue
                if offset % 4 != 3:
                    failures.append(('DP_mod_fail', P, r, offset))
                    continue
                verified_dp += 1
        else:
            # Class not in covering - try exhaustive search
            # (This handles classes where gcd(r, N) > 1, meaning P | N,
            #  which is finite)
            found = False
            for delta in range(3, 201, 4):
                if (P + delta) % 4 != 0:
                    continue
                A = (P + delta) // 4
                divs = divisors(A)
                dset = set(divs)
                for u in divs:
                    if u >= delta:
                        break
                    v = delta - u
                    if v > 0 and v in dset:
                        b = A // u
                        c = A // v
                        if (P + delta) * (b + c) == 4 * delta * b * c:
                            found = True
                            break
                if found:
                    break
            if found:
                verified_dp += 1
            else:
                failures.append(('no_cover', P, r))

    print(f"Checked {checked} primes")
    print(f"  D6 verified: {verified_d6}")
    print(f"  DP verified: {verified_dp}")
    print(f"  Failures: {len(failures)}")
    if failures:
        for f in failures[:20]:
            print(f"    {f}")
    else:
        print("  ALL PRIMES VERIFIED!")


def main():
    t0 = time.time()

    result = comprehensive_search()

    if result and len(result) == 3:
        N, targets, covered = result
        verify_with_primes(N, covered, max_P=200000)

        # Print covering details for Lean
        print(f"\n{'='*78}")
        print(f"COVERING DETAILS FOR LEAN (N = {N:,})")
        print(f"{'='*78}")

        d6_cases = [(r, info) for r, info in sorted(covered.items()) if info[0] == 'D6']
        dp_cases = [(r, info) for r, info in sorted(covered.items()) if info[0] == 'DP']

        print(f"\nD6 cases ({len(d6_cases)}):")
        for r, info in d6_cases[:20]:
            print(f"  r={r:>8} (mod {N}): M={info[1]}, residue={info[2]}")
        if len(d6_cases) > 20:
            print(f"  ... and {len(d6_cases)-20} more")

        print(f"\nDP cases ({len(dp_cases)}):")
        for r, info in dp_cases[:20]:
            print(f"  r={r:>8} (mod {N}): alpha={info[3]}, beta={info[4]}, "
                  f"offset={info[3]+info[4]}")
        if len(dp_cases) > 20:
            print(f"  ... and {len(dp_cases)-20} more")

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
