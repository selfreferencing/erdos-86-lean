#!/usr/bin/env python3
"""
Efficient QR gap covering via divisor-pair congruences.

Strategy: incrementally grow Q by adding prime factors.
At each Q, enumerate DP congruences with moduli dividing Q,
check coverage of QR gap targets.

DP congruence: P ≡ -(u+v) (mod 4*lcm(u,v)) where u+v ≡ 3 (mod 4).
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


def get_qr_gap_targets(Q):
    """Get all QR gap target classes mod Q."""
    targets = set()
    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        if x % 7 in (1, 2, 4) and x % 5 in (1, 4):
            targets.add(x)
    return targets


def get_dp_coverage(Q, targets):
    """
    Find all DP congruences with modulus | Q, and compute coverage.
    DP: P ≡ -(u+v) (mod 4*lcm(u,v)), u+v ≡ 3 (mod 4).
    Need 4*lcm(u,v) | Q, i.e., lcm(u,v) | Q/4.
    """
    Q4 = Q // 4
    divs_Q4 = divisors(Q4)

    covered = set()
    witness = {}  # target -> (delta, u, v, modulus, res)

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

            # Check compatibility with P ≡ 1 (mod 24)
            g = gcd(modulus, 24)
            if res % g != 1 % g:
                continue

            # Cover targets
            for x in targets:
                if x not in covered and x % modulus == res:
                    covered.add(x)
                    witness[x] = (delta, u, v, modulus, res)

    return covered, witness


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


def get_d6_coverage(Q, targets):
    """Compute D.6 coverage of targets at given Q."""
    oQ = Q
    while oQ % 2 == 0:
        oQ //= 2
    M_values = [d for d in divisors(oQ) if d % 4 == 3 and d >= 3]

    covered = set()
    for M in M_values:
        residues = get_d6_residues_for_M(M)
        if not residues:
            continue
        for x in targets:
            if x not in covered and x % M in residues:
                covered.add(x)

    return covered


def main():
    t0 = time.time()

    print("=" * 78)
    print("QR GAP COVERING: Incremental Q growth with D.6 + DP")
    print("=" * 78)

    # Base: Q = 840 = 2^3 * 3 * 5 * 7
    # QR gap: 6 classes mod 840
    Q = 840
    targets = get_qr_gap_targets(Q)
    print(f"Q = {Q}, QR gap targets: {len(targets)}")
    print(f"Targets: {sorted(targets)}")

    # Check D.6 coverage at base Q
    d6_covered = get_d6_coverage(Q, targets)
    print(f"\nD.6 coverage: {len(d6_covered)}/{len(targets)}")

    # Check DP coverage at base Q
    dp_covered, dp_witness = get_dp_coverage(Q, targets)
    combined = d6_covered | dp_covered
    print(f"DP coverage: {len(dp_covered)}/{len(targets)}")
    print(f"Combined: {len(combined)}/{len(targets)}")

    if combined == targets:
        print("COMPLETE at base Q!")
    else:
        remaining = targets - combined
        print(f"Remaining: {remaining}")

    # Incrementally add prime factors
    for extra_prime in [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]:
        Q_new = lcm2(Q, 4 * extra_prime)  # Ensure 4*p | Q for DP moduli
        if Q_new == Q:
            continue

        targets_new = get_qr_gap_targets(Q_new)

        # D.6 + DP coverage at new Q
        d6_cov_new = get_d6_coverage(Q_new, targets_new)
        dp_cov_new, dp_wit_new = get_dp_coverage(Q_new, targets_new)
        combined_new = d6_cov_new | dp_cov_new

        pct = 100.0 * len(combined_new) / len(targets_new) if targets_new else 100.0
        print(f"\nQ * {extra_prime} = {Q_new:,}: "
              f"D6={len(d6_cov_new)}, DP={len(dp_cov_new)}, "
              f"combined={len(combined_new)}/{len(targets_new)} ({pct:.4f}%)")

        if combined_new == targets_new:
            Q = Q_new
            targets = targets_new
            dp_witness = dp_wit_new
            print(f"\n*** COMPLETE COVERING AT Q = {Q:,} ***")
            facs = factorize(Q)
            print(f"Q = " + " * ".join(f"{p}^{e}" if e > 1 else str(p)
                                         for p, e in sorted(facs.items())))
            break

        uncov = targets_new - combined_new
        # Show residue distribution of uncovered
        for m in [extra_prime]:
            dist = defaultdict(int)
            for x in uncov:
                dist[x % m] += 1
            print(f"  Uncovered mod {m}: {dict(sorted(dist.items()))}")

        # Update Q if this helps
        if len(combined_new) / len(targets_new) > len(combined) / len(targets):
            Q = Q_new
            targets = targets_new
            combined = combined_new
            d6_covered = d6_cov_new
            dp_covered = dp_cov_new
            dp_witness = dp_wit_new

    # Print DP witness summary
    if dp_witness:
        print(f"\n{'=' * 78}")
        print("DP WITNESS SUMMARY")
        print("=" * 78)

        # Group by (delta, u, v)
        by_construction = defaultdict(list)
        for x, (delta, u, v, mod, res) in dp_witness.items():
            by_construction[(delta, u, v, mod, res)].append(x)

        print(f"Distinct DP constructions used: {len(by_construction)}")
        for (delta, u, v, mod, res), classes in sorted(by_construction.items(),
                                                         key=lambda x: -len(x[1])):
            print(f"  delta={delta}, u={u}, v={v}, mod={mod}, P≡{res}(mod {mod}): "
                  f"{len(classes)} classes")

    # Verify with actual primes
    if dp_witness:
        print(f"\n{'=' * 78}")
        print(f"PRIME VERIFICATION up to 2,000,000")
        print("=" * 78)

        checked = 0
        by_cov = 0
        by_search = 0
        failures = []

        # Build lookup: for each residue mod Q, get DP construction
        all_witness = {}
        for x, w in dp_witness.items():
            all_witness[x] = w

        for P in range(25, 2_000_001, 24):
            if not is_prime(P):
                continue
            if P % 7 not in (1, 2, 4) or P % 5 not in (1, 4):
                continue
            checked += 1

            found = False
            r = P % Q

            # Try DP witness for this residue class
            if r in all_witness:
                delta, u, v, mod, res = all_witness[r]
                if (P + delta) % 4 == 0:
                    A = (P + delta) // 4
                    if A % u == 0 and A % v == 0:
                        b = A // u
                        c = A // v
                        if b > 0 and c > 0 and (P + delta) * (b + c) == 4 * delta * b * c:
                            found = True
                            by_cov += 1

            # Fallback: direct search
            if not found:
                for delta in range(3, 2001, 4):
                    if (P + delta) % 4 != 0:
                        continue
                    A = (P + delta) // 4
                    divs = divisors(A)
                    divs_set = set(divs)
                    for uu in divs:
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

        print(f"Checked: {checked} QR gap primes")
        print(f"  By covering: {by_cov}")
        print(f"  By search:   {by_search}")
        print(f"  Failures:    {len(failures)}")
        if failures:
            print(f"  Failed: {failures[:20]}")
        else:
            print(f"  ALL VERIFIED!")

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
