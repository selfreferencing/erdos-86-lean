#!/usr/bin/env python3
"""
Correct QR gap analysis: work at Q = lcm(840, all M values used).

Previous analysis was WRONG because it checked cls%M at Q=840,
but M values like 11, 19, 23 don't divide 840. When 11 ∤ 840,
the class p ≡ 121 (mod 840) doesn't constrain p mod 11 at all.

Correct approach: grow Q by adding M values, then check coverage
of the lifted QR gap targets.
"""

from math import gcd
from collections import defaultdict
import time


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
    result = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            result.append(i)
            if i != n // i:
                result.append(n // i)
        i += 1
    return sorted(result)


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


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def get_d6_residues_for_M(M):
    """Get all P residues mod M covered by Lemma D.6."""
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


def get_qr_gap_targets(Q):
    """Get QR gap target classes mod Q: p ≡ 1 (mod 24), gcd(p,Q)=1,
    p%7 ∈ {1,2,4}, p%5 ∈ {1,4}."""
    targets = set()
    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        if x % 7 in (1, 2, 4) and x % 5 in (1, 4):
            targets.add(x)
    return targets


def build_d6_coverage(Q):
    """Build D.6 coverage at given Q, restricted to QR gap targets."""
    targets = get_qr_gap_targets(Q)
    if not targets:
        return targets, set(), {}

    oQ = odd_part(Q)
    M_values = [d for d in divisors(oQ) if d % 4 == 3 and d >= 3]

    M_data = {}
    covered = set()
    witness = {}

    for M in M_values:
        residues = get_d6_residues_for_M(M)
        if not residues:
            continue
        M_data[M] = residues
        for x in targets:
            if x not in covered and x % M in residues:
                covered.add(x)
                # Find the specific triple
                k = (M + 1) // 4
                for a in divisors(k):
                    rem = k // a
                    for s in divisors(rem):
                        r = rem // s
                        if (-4 * a * s * s) % M == x % M:
                            witness[x] = (M, r, s, a, x % M)
                            break
                    else:
                        continue
                    break

    return targets, covered, witness


def main():
    t0 = time.time()

    print("=" * 78)
    print("CORRECT QR GAP ANALYSIS: Incremental Q growth")
    print("=" * 78)

    # Start at Q = 840 (QR gap base)
    Q = 840
    targets = get_qr_gap_targets(Q)
    print(f"Q = {Q}, QR gap targets: {len(targets)}")

    # D.6 coverage at Q=840 (only M=3,7 divide 840's odd part)
    _, d6_covered, _ = build_d6_coverage(Q)
    print(f"D.6 at Q={Q}: {len(d6_covered)}/{len(targets)}")

    # Incrementally add prime factors via M values
    # M = 4*alpha*s*r - 1
    # New M values introduce new prime factors when M has primes not in Q
    # Key M values: 11, 19, 23, 27(=3^3), 31, 43, 47, 59, ...

    # Build incrementally
    best_Q = Q
    best_targets = targets
    best_covered = d6_covered
    best_pct = 100 * len(d6_covered) / len(targets) if targets else 100

    # Try adding factors one at a time
    extra_factors = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                     53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

    Q_running = 840
    for factor in extra_factors:
        Q_new = lcm2(Q_running, factor)
        if Q_new == Q_running:
            continue
        if Q_new > 500_000_000:
            print(f"  Q would exceed 500M with factor {factor}, stopping")
            break

        targets_new = get_qr_gap_targets(Q_new)
        if not targets_new:
            Q_running = Q_new
            continue

        # Build D.6 coverage at new Q
        _, d6_cov_new, _ = build_d6_coverage(Q_new)
        pct = 100 * len(d6_cov_new) / len(targets_new)

        print(f"  + {factor:>3} → Q={Q_new:>12,}: D.6={len(d6_cov_new):>8,}/{len(targets_new):>8,} ({pct:.4f}%)")

        Q_running = Q_new

        if pct > best_pct:
            best_Q = Q_new
            best_targets = targets_new
            best_covered = d6_cov_new
            best_pct = pct

        if len(d6_cov_new) == len(targets_new):
            print(f"\n*** COMPLETE D.6 COVERING AT Q = {Q_new:,} ***")
            break

    # Summary
    print(f"\n{'=' * 78}")
    print("SUMMARY")
    print("=" * 78)
    print(f"Best Q = {best_Q:,}")
    facs = factorize(best_Q)
    print(f"  = " + " * ".join(f"{p}^{e}" if e > 1 else str(p)
                                 for p, e in sorted(facs.items())))
    print(f"QR gap targets: {len(best_targets)}")
    print(f"D.6 covered: {len(best_covered)}")
    print(f"Coverage: {best_pct:.4f}%")

    if best_covered < best_targets:
        uncov = best_targets - best_covered
        print(f"Uncovered: {len(uncov)}")

        # Analyze uncovered residue distribution
        print(f"\nUncovered residue distribution:")
        for m in sorted(factorize(best_Q).keys()):
            if m <= 2:
                continue
            dist = defaultdict(int)
            for x in uncov:
                dist[x % m] += 1
            if dist:
                print(f"  mod {m}: {dict(sorted(dist.items()))}")

    # Verify with actual primes
    print(f"\n{'=' * 78}")
    print(f"PRIME VERIFICATION up to 2,000,000")
    print("=" * 78)

    checked = 0
    by_d6 = 0
    by_dp = 0
    failures = []
    max_delta = 0

    for P in range(25, 2_000_001, 24):
        if not is_prime(P):
            continue
        if P % 7 not in (1, 2, 4) or P % 5 not in (1, 4):
            continue
        checked += 1

        found = False

        # Try D.6 with expanded parameters
        for alpha in range(1, 20):
            if found:
                break
            for s in range(1, 60):
                if found:
                    break
                for r in range(1, 60):
                    M = 4 * alpha * s * r - 1
                    val = 4 * alpha * s * s + P
                    if val % M != 0:
                        continue
                    m = val // M
                    c_prime = m * r - s
                    if c_prime <= 0:
                        continue
                    A = alpha * s * c_prime
                    L = (P + 3) // 4
                    U = (3 * P - 3) // 4
                    if A < L or A > U:
                        continue
                    offset = 4 * A - P
                    g = alpha * r
                    b = g * s
                    c = g * c_prime
                    if offset % 4 != 3 or b <= 0 or c <= 0:
                        continue
                    if (P + offset) * (b + c) == 4 * offset * b * c:
                        found = True
                        by_d6 += 1
                        break

        # Fallback: divisor-pair
        if not found:
            for delta in range(3, 2001, 4):
                if (P + delta) % 4 != 0:
                    continue
                A = (P + delta) // 4
                divs = divisors(A)
                divs_set = set(divs)
                for u in divs:
                    if u >= delta:
                        break
                    v = delta - u
                    if v > 0 and v in divs_set:
                        bb = A // u
                        cc = A // v
                        if (P + delta) * (bb + cc) == 4 * delta * bb * cc:
                            found = True
                            by_dp += 1
                            if delta > max_delta:
                                max_delta = delta
                            break
                if found:
                    break

        if not found:
            failures.append(P)

    print(f"Checked: {checked}")
    print(f"  By D.6: {by_d6}")
    print(f"  By DP:  {by_dp}")
    print(f"  Max delta (DP): {max_delta}")
    print(f"  Failures: {len(failures)}")
    if failures:
        print(f"  Failed: {failures[:20]}")
    else:
        print(f"  ALL VERIFIED!")

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
