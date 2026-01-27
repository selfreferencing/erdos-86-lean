#!/usr/bin/env python3
"""
Build a FINITE divisor-pair covering for the 6 QR gap classes mod 840.

Key finding: Lemma D.6 cannot cover any of these classes (QR obstruction).
The divisor-pair method CAN cover them. This script builds the explicit
finite covering needed for the Lean formalization.

DP construction: delta ≡ 3 (mod 4), u + v = delta, u | A, v | A, A = (P+delta)/4.
Congruence: P ≡ -delta (mod 4*lcm(u,v)).

We need to cover all P ≡ 1 (mod 24) in the 6 QR gap classes mod 840,
i.e., P in 6 specific classes mod 840 = lcm(24, 35).
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
    small, large = [], []
    i = 1
    while i * i <= n:
        if n % i == 0:
            small.append(i)
            if i != n // i:
                large.append(n // i)
        i += 1
    return small + large[::-1]


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
# Core: Build DP covering
# ═══════════════════════════════════════════════════════════════════

def build_dp_covering(max_Q=10_000_000, max_delta=5000):
    """
    Build a finite DP covering for the 6 QR gap classes.

    Approach:
    - Start with Q_base = 840
    - Targets: all x ≡ 1 (mod 24) with x%35 in QR_gap, gcd(x, Q) = 1
    - For each DP construction, compute which targets it covers
    - Greedily add until all covered or Q exceeds limit
    """
    Q = 840
    qr_gap_mod35 = {1, 4, 9, 11, 16, 29}  # p%7 in {1,2,4} AND p%5 in {1,4}

    # Enumerate target classes mod Q
    targets = set()
    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        if x % 35 in qr_gap_mod35:
            targets.add(x)

    print(f"Initial Q = {Q}")
    print(f"QR gap targets mod {Q}: {len(targets)}")
    print(f"Target classes: {sorted(targets)}")

    # Enumerate DP congruences
    print(f"\nEnumerating DP congruences with delta up to {max_delta}...")
    dp_list = []
    seen = set()

    for delta in range(3, max_delta + 1, 4):
        for u in range(1, delta):
            v = delta - u
            if v <= 0:
                continue
            L = lcm2(u, v)
            modulus = 4 * L
            if modulus > max_Q:
                continue
            res = (-delta) % modulus

            # Check basic compatibility with P ≡ 1 (mod 24)
            g = gcd(modulus, 24)
            if res % g != 1 % g:
                continue

            key = (modulus, res)
            if key in seen:
                continue
            seen.add(key)
            dp_list.append((modulus, res, delta, u, v))

    print(f"Total DP congruences: {len(dp_list)}")

    # Greedy covering
    print(f"\nGreedy covering search...")
    covered = set()
    selected = []

    for iteration in range(500):
        if covered == targets:
            break

        best = None
        best_gain = 0
        best_new_Q = None

        for dp in dp_list:
            modulus, res, delta, u, v = dp
            new_Q = lcm2(Q, modulus)
            if new_Q > max_Q:
                continue

            # Lift targets and coverage to new_Q
            new_targets = set()
            new_covered = set()
            new_dp_covers = set()

            for x in range(new_Q):
                if x % 24 != 1:
                    continue
                if gcd(x, new_Q) != 1:
                    continue
                if x % 840 not in targets:
                    continue
                new_targets.add(x)
                if x % Q in covered:
                    # Already covered at current Q level
                    # But need to check if the lift is consistent
                    pass  # will handle below

            # For existing coverage: lift
            for x in new_targets:
                if x % Q in covered:
                    new_covered.add(x)
                if x % modulus == res:
                    new_dp_covers.add(x)

            gain = len((new_covered | new_dp_covers) & new_targets) - len(new_covered & new_targets)
            if gain > best_gain:
                best_gain = gain
                best = dp
                best_new_Q = new_Q
                best_new_targets = new_targets
                best_new_covered = new_covered | new_dp_covers

        if best is None or best_gain == 0:
            break

        selected.append(best)
        modulus, res, delta, u, v = best
        Q = best_new_Q
        targets = best_new_targets
        covered = best_new_covered

        pct = 100.0 * len(covered) / len(targets) if targets else 100.0
        print(f"  #{iteration+1}: delta={delta}, u={u}, v={v}, mod={modulus}, "
              f"P≡{res}(mod {modulus}), "
              f"covered {len(covered)}/{len(targets)} ({pct:.2f}%) Q={Q:,}")

        if covered == targets:
            print(f"\n*** COMPLETE DP COVERING! Q = {Q:,} ***")
            print(f"*** {len(selected)} DP constructions needed ***")
            break

    if covered != targets:
        remaining = targets - covered
        print(f"\nIncomplete: {len(remaining)} classes uncovered mod {Q}")
        # Analyze remaining
        print(f"Sample uncovered classes: {sorted(remaining)[:20]}")

    return selected, Q, covered == targets


# ═══════════════════════════════════════════════════════════════════
# Simpler approach: just find small set of DP congruences
# ═══════════════════════════════════════════════════════════════════

def simple_dp_search():
    """
    Simpler approach: for each small delta, check how many
    QR gap primes it covers by itself.
    """
    print("=" * 78)
    print("SIMPLE DP SEARCH: Coverage by individual deltas")
    print("=" * 78)

    # Check which deltas handle the most QR gap primes
    qr_gap_primes = []
    for P in range(25, 100001, 24):
        if not is_prime(P):
            continue
        if P % 7 in (1, 2, 4) and P % 5 in (1, 4):
            qr_gap_primes.append(P)

    print(f"QR gap primes up to 100,000: {len(qr_gap_primes)}")

    delta_coverage = {}
    for delta in range(3, 201, 4):
        count = 0
        for P in qr_gap_primes:
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
                    b = A // u
                    c = A // v
                    if (P + delta) * (b + c) == 4 * delta * b * c:
                        count += 1
                        break
        if count > 0:
            delta_coverage[delta] = count

    print(f"\nDelta coverage (sorted by coverage):")
    for delta, count in sorted(delta_coverage.items(), key=lambda x: -x[1])[:20]:
        pct = 100.0 * count / len(qr_gap_primes)
        print(f"  delta={delta:>4}: {count}/{len(qr_gap_primes)} = {pct:.1f}%")

    # Cumulative coverage with best deltas
    print(f"\nCumulative coverage with best deltas:")
    uncov = set(qr_gap_primes)
    used_deltas = []
    for _ in range(20):
        if not uncov:
            break
        best_delta = None
        best_count = 0
        for delta in range(3, 501, 4):
            count = 0
            for P in uncov:
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
                        b = A // u
                        c = A // v
                        if (P + delta) * (b + c) == 4 * delta * b * c:
                            count += 1
                            break
            if count > best_count:
                best_count = count
                best_delta = delta

        if best_delta is None or best_count == 0:
            break

        used_deltas.append(best_delta)
        newly_covered = set()
        for P in uncov:
            delta = best_delta
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
                    b = A // u
                    c = A // v
                    if (P + delta) * (b + c) == 4 * delta * b * c:
                        newly_covered.add(P)
                        break
        uncov -= newly_covered
        pct = 100.0 * (len(qr_gap_primes) - len(uncov)) / len(qr_gap_primes)
        print(f"  delta={best_delta:>4}: +{len(newly_covered)}, "
              f"total {len(qr_gap_primes) - len(uncov)}/{len(qr_gap_primes)} ({pct:.1f}%)")

    if uncov:
        print(f"\n  Uncovered primes: {sorted(uncov)[:20]}")
    else:
        print(f"\n  ALL COVERED with deltas: {used_deltas}")


# ═══════════════════════════════════════════════════════════════════
# For each (delta, u, v), compute the exact congruence on P
# and check if a small set covers all 6 QR gap classes mod 840
# ═══════════════════════════════════════════════════════════════════

def find_covering_congruences():
    """
    For each DP (delta, u, v), the congruence is P ≡ -delta (mod 4*lcm(u,v)).
    We need these to cover all P ≡ cls (mod 840) for cls in QR gap.

    Strategy: work modulo a growing Q. Start with Q=840.
    For each DP congruence with modulus dividing Q or extending Q,
    check how many new targets it covers.
    """
    print("\n" + "=" * 78)
    print("COVERING CONGRUENCE SEARCH")
    print("=" * 78)

    Q = 840
    qr_gap_mod35 = {1, 4, 9, 11, 16, 29}

    targets = set()
    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        if x % 35 in qr_gap_mod35:
            targets.add(x)

    print(f"Base Q = {Q}, targets: {len(targets)} classes")
    print(f"Targets: {sorted(targets)}")

    # Pre-compute all DP congruences with small moduli
    dp_congs = []
    seen = set()
    for delta in range(3, 10001, 4):
        for u in range(1, delta):
            v = delta - u
            if v <= 0:
                continue
            L = lcm2(u, v)
            modulus = 4 * L
            res = (-delta) % modulus

            # Quick compatibility with P ≡ 1 (mod 24)
            g = gcd(modulus, 24)
            if res % g != 1 % g:
                continue

            # Quick compatibility with some QR gap class
            g2 = gcd(modulus, 840)
            compatible = False
            for cls in targets:
                if cls % g2 == res % g2:
                    compatible = True
                    break
            if not compatible:
                continue

            key = (modulus, res)
            if key in seen:
                continue
            seen.add(key)
            dp_congs.append((modulus, res, delta, u, v))

    print(f"Compatible DP congruences: {len(dp_congs)}")

    # Sort by modulus for efficiency
    dp_congs.sort(key=lambda x: x[0])

    # Greedy covering with Q growth
    max_Q = 50_000_000
    covered = set()
    selected = []

    for iteration in range(200):
        if covered >= targets:
            break

        best = None
        best_gain = 0
        best_new_Q = None
        best_covered = None

        for dp in dp_congs:
            modulus, res, delta, u, v = dp
            new_Q = lcm2(Q, modulus)
            if new_Q > max_Q:
                continue

            if new_Q == Q:
                # No Q growth needed, just check coverage
                new_covered = set()
                for x in targets:
                    if x in covered:
                        continue
                    if x % modulus == res:
                        new_covered.add(x)
                gain = len(new_covered)
            else:
                # Q grows - need to lift
                new_targets = set()
                for x in range(new_Q):
                    if x % 24 != 1:
                        continue
                    if gcd(x, new_Q) != 1:
                        continue
                    if x % 840 in [c % 840 for c in targets]:
                        new_targets.add(x)

                lift_covered = set()
                for x in new_targets:
                    if x % Q in covered:
                        lift_covered.add(x)

                dp_new = set()
                for x in new_targets:
                    if x % modulus == res:
                        dp_new.add(x)

                gain = len((lift_covered | dp_new) & new_targets) - len(lift_covered & new_targets)

            if gain > best_gain or (gain == best_gain and best_new_Q is not None and
                                     lcm2(Q, modulus) < best_new_Q):
                best_gain = gain
                best = dp
                best_new_Q = lcm2(Q, modulus)

        if best is None or best_gain == 0:
            break

        modulus, res, delta, u, v = best
        selected.append(best)
        new_Q = lcm2(Q, modulus)

        if new_Q != Q:
            # Lift everything to new_Q
            new_targets = set()
            for x in range(new_Q):
                if x % 24 != 1:
                    continue
                if gcd(x, new_Q) != 1:
                    continue
                x_840 = x % 840
                if x_840 in [1, 121, 169, 289, 361, 529]:
                    new_targets.add(x)

            new_covered = set()
            for x in new_targets:
                if x % Q in covered:
                    new_covered.add(x)
                if x % modulus == res:
                    new_covered.add(x)

            Q = new_Q
            targets = new_targets
            covered = new_covered
        else:
            for x in targets:
                if x % modulus == res:
                    covered.add(x)

        pct = 100.0 * len(covered) / len(targets) if targets else 100.0
        print(f"  #{iteration+1}: delta={delta}, u={u}, v={v}, mod={modulus}, "
              f"P≡{res}(mod {modulus}), "
              f"{len(covered)}/{len(targets)} ({pct:.2f}%) Q={Q:,}")

        if covered >= targets:
            print(f"\n*** COMPLETE DP COVERING! ***")
            print(f"*** Q = {Q:,} = ", end="")
            facs = factorize(Q)
            print(" * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(facs.items())))
            print(f"*** {len(selected)} DP constructions ***")
            break

    if covered < targets:
        remaining = targets - covered
        pct = 100.0 * len(covered) / len(targets)
        print(f"\nIncomplete: {len(remaining)} / {len(targets)} uncovered ({pct:.2f}%)")

        # Analyze
        print("Uncovered residue distribution:")
        for m in [7, 5, 11, 13, 17, 19, 23]:
            if Q % m == 0:
                dist = defaultdict(int)
                for x in remaining:
                    dist[x % m] += 1
                print(f"  mod {m}: {dict(sorted(dist.items()))}")

    return selected, Q, covered >= targets


# ═══════════════════════════════════════════════════════════════════
# Verify covering with actual primes
# ═══════════════════════════════════════════════════════════════════

def verify_dp_covering(selected, max_P=2_000_000):
    """Verify that the selected DP constructions cover all QR gap primes."""
    print(f"\n{'=' * 78}")
    print(f"VERIFICATION: QR gap primes up to {max_P:,}")
    print("=" * 78)

    checked = 0
    by_covering = 0
    by_search = 0
    failures = []

    for P in range(25, max_P + 1, 24):
        if not is_prime(P):
            continue
        if P % 7 not in (1, 2, 4) or P % 5 not in (1, 4):
            continue
        checked += 1

        found = False

        # Try selected DP constructions
        for modulus, res, delta, u, v in selected:
            if P % modulus != res:
                continue
            if (P + delta) % 4 != 0:
                continue
            A = (P + delta) // 4
            if A % u != 0 or A % v != 0:
                continue
            b = A // u
            c = A // v
            if b > 0 and c > 0 and (P + delta) * (b + c) == 4 * delta * b * c:
                found = True
                by_covering += 1
                break

        # Fallback: exhaustive search
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
    print(f"  By covering: {by_covering}")
    print(f"  By search:   {by_search}")
    print(f"  Failures:    {len(failures)}")

    if not failures:
        print(f"  ALL VERIFIED!")
    else:
        print(f"  FAILURES: {failures[:20]}")

    return failures


# ═══════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    simple_dp_search()
    selected, Q, complete = find_covering_congruences()

    if complete:
        print(f"\n{'=' * 78}")
        print(f"COVERING SET SUMMARY")
        print("=" * 78)
        print(f"Q = {Q:,}")
        print(f"Constructions: {len(selected)}")
        for i, (modulus, res, delta, u, v) in enumerate(selected):
            print(f"  #{i+1}: delta={delta}, u={u}, v={v}, mod={modulus}, P≡{res}(mod {modulus})")

        verify_dp_covering(selected)

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
