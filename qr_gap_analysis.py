#!/usr/bin/env python3
"""
Targeted analysis of the QR gap: 6 residue classes mod 840 where
p%7 in {1,2,4} AND p%5 in {1,4}, with p ≡ 1 (mod 24).

The 6 classes mod 840 are: {1, 121, 169, 289, 361, 529}.

Goal: find a finite set of Lemma D.6 triples OR divisor-pair constructions
that cover ALL 6 classes, or prove this is impossible and we need
a different approach.

Strategy:
  1. For each QR gap class, find ALL M values (from Lemma D.6) that cover it
  2. Check if the divisor-pair method covers any that D.6 misses
  3. Determine the minimum Q needed for complete coverage
  4. Verify with actual primes
"""

from math import gcd, isqrt
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


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def get_residues_for_M(M):
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


# =================================================================
# Phase 1: Identify which M values from D.6 can cover each QR class
# =================================================================

def analyze_d6_coverage_of_qr_gap(max_M=2000):
    """For each QR gap class mod 840, find which M values cover it."""
    qr_classes = [1, 121, 169, 289, 361, 529]

    print("=" * 78)
    print("PHASE 1: D.6 coverage of QR gap classes mod 840")
    print("=" * 78)

    # For each M, compute which QR classes it covers
    M_covers = {}  # M -> set of QR classes covered

    for M in range(3, max_M + 1, 4):  # M ≡ 3 mod 4
        residues = get_residues_for_M(M)
        if not residues:
            continue
        covered_classes = set()
        for cls in qr_classes:
            if cls % M in residues:
                covered_classes.add(cls)
        if covered_classes:
            M_covers[M] = covered_classes

    # For each class, list M values that cover it
    class_to_M = defaultdict(list)
    for M, classes in M_covers.items():
        for cls in classes:
            class_to_M[cls].append(M)

    print(f"\nSearched M values up to {max_M}")
    print(f"M values covering at least one QR class: {len(M_covers)}")

    for cls in qr_classes:
        M_list = sorted(class_to_M[cls])
        print(f"\n  Class {cls} (mod 840):")
        print(f"    Covered by {len(M_list)} M values")
        if M_list:
            print(f"    Smallest M values: {M_list[:15]}")
        else:
            print(f"    *** NOT COVERED by any M ≤ {max_M} ***")

    # Check if we can cover ALL 6 classes with compatible M values
    # (i.e., M values whose LCM is manageable)
    return M_covers, class_to_M


# =================================================================
# Phase 2: Find minimal covering set
# =================================================================

def find_minimal_covering(M_covers, qr_classes):
    """Greedy search for minimal set of M values covering all 6 classes."""
    print("\n" + "=" * 78)
    print("PHASE 2: Finding minimal M-value covering set")
    print("=" * 78)

    uncovered = set(qr_classes)
    selected = []
    Q = 840  # base modulus

    for iteration in range(20):
        if not uncovered:
            break

        # Find M that covers the most uncovered classes
        best_M = None
        best_gain = 0
        best_Q = None

        for M, classes in M_covers.items():
            gain = len(classes & uncovered)
            if gain == 0:
                continue
            new_Q = lcm2(Q, M)
            # Prefer smaller Q, then more gain
            if gain > best_gain or (gain == best_gain and (best_Q is None or new_Q < best_Q)):
                best_gain = gain
                best_M = M
                best_Q = new_Q

        if best_M is None:
            break

        selected.append(best_M)
        covered_now = M_covers[best_M] & uncovered
        uncovered -= covered_now
        Q = lcm2(Q, best_M)

        print(f"  #{iteration+1}: M={best_M}, covers {covered_now}, "
              f"remaining={uncovered}, Q={Q:,}")

    if uncovered:
        print(f"\n*** INCOMPLETE: {uncovered} not covered by D.6 ***")
    else:
        print(f"\n*** ALL 6 CLASSES COVERED! Q = {Q:,} ***")

    return selected, Q, len(uncovered) == 0


# =================================================================
# Phase 3: Divisor-pair analysis for uncovered classes
# =================================================================

def analyze_dp_for_class(cls, max_delta=500):
    """
    For a QR gap class (e.g., P ≡ cls mod 840),
    find divisor-pair (delta, u, v) constructions.

    Divisor-pair: delta ≡ 3 (mod 4), A = (P+delta)/4.
    Need u | A, v | A, u + v = delta.
    Congruence: P ≡ -delta (mod 4*lcm(u,v)).
    """
    results = []
    for delta in range(3, max_delta + 1, 4):
        # For P ≡ cls (mod 840), check (P + delta) % 4 = 0
        if (cls + delta) % 4 != 0:
            continue

        # A = (P + delta)/4. For specific (u,v) pair:
        # u | A and v | A and u + v = delta
        # u | (P + delta)/4 means P ≡ -delta (mod 4u)
        # Similarly for v.

        # Enumerate valid (u, v) pairs
        for u in range(1, delta):
            v = delta - u
            if v <= 0:
                continue
            # Check: P ≡ -delta (mod 4u) and P ≡ -delta (mod 4v)
            # Combined: P ≡ -delta (mod 4*lcm(u,v))
            L = lcm2(u, v)
            modulus = 4 * L
            res = (-delta) % modulus

            # Check compatibility with P ≡ cls (mod 840)
            g = gcd(modulus, 840)
            if cls % g != res % g:
                continue

            # This (delta, u, v) can work for P ≡ cls (mod 840)
            results.append((delta, u, v, modulus, res))

    return results


def analyze_dp_coverage(qr_classes, uncovered_by_d6, max_delta=2000):
    """Check if divisor-pair method covers classes that D.6 misses."""
    print("\n" + "=" * 78)
    print("PHASE 3: Divisor-pair coverage analysis")
    print("=" * 78)

    for cls in sorted(uncovered_by_d6):
        print(f"\n  Class {cls} (mod 840):")
        dp_results = analyze_dp_for_class(cls, max_delta=max_delta)
        if dp_results:
            # Group by modulus
            by_mod = defaultdict(list)
            for delta, u, v, mod, res in dp_results:
                by_mod[mod].append((delta, u, v, res))
            print(f"    Found {len(dp_results)} DP constructions")
            print(f"    Smallest moduli: {sorted(by_mod.keys())[:10]}")
            for mod in sorted(by_mod.keys())[:5]:
                entries = by_mod[mod][:3]
                for delta, u, v, res in entries:
                    print(f"      mod={mod}: delta={delta}, u={u}, v={v}, P≡{res}(mod {mod})")
        else:
            print(f"    *** NO DP constructions found with delta ≤ {max_delta} ***")


# =================================================================
# Phase 4: Verify with actual primes in QR gap classes
# =================================================================

def verify_qr_gap_primes(max_P=2_000_000):
    """Verify all primes in QR gap classes have ED2 solutions."""
    print("\n" + "=" * 78)
    print(f"PHASE 4: Verifying QR gap primes up to {max_P:,}")
    print("=" * 78)

    checked = 0
    found_dp = 0
    found_d6 = 0
    max_delta_needed = 0
    failures = []
    delta_dist = defaultdict(int)

    for P in range(25, max_P + 1, 24):
        if not is_prime(P):
            continue
        if P % 7 not in (1, 2, 4) or P % 5 not in (1, 4):
            continue
        checked += 1

        found = False
        # Try divisor-pair method
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
                    b = A // u
                    c = A // v
                    if (P + delta) * (b + c) == 4 * delta * b * c:
                        found = True
                        found_dp += 1
                        delta_dist[delta] += 1
                        if delta > max_delta_needed:
                            max_delta_needed = delta
                        break
            if found:
                break

        if not found:
            # Try D.6 with expanded search
            for alpha in range(1, 15):
                if found:
                    break
                for s in range(1, 50):
                    if found:
                        break
                    for r in range(1, 50):
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
                            found_d6 += 1
                            break

        if not found:
            failures.append(P)

    print(f"\nChecked {checked} QR gap primes")
    print(f"  By divisor-pair: {found_dp}")
    print(f"  By D.6:          {found_d6}")
    print(f"  Max delta needed: {max_delta_needed}")
    print(f"  Failures:         {len(failures)}")

    if failures:
        print(f"  Failed: {failures[:20]}")
    else:
        print(f"  ALL QR GAP PRIMES VERIFIED!")

    print(f"\nDelta distribution (top 15):")
    for delta, count in sorted(delta_dist.items(), key=lambda x: -x[1])[:15]:
        print(f"  delta={delta:>5}: {count} primes")

    return failures, max_delta_needed


# =================================================================
# Phase 5: Check specific M values for QR gap
# =================================================================

def check_specific_M_combinations():
    """
    Check which combinations of M values from D.6 cover all 6 QR gap classes.
    Focus on M values involving primes 11, 13, 17, 19, 23, ...
    """
    print("\n" + "=" * 78)
    print("PHASE 5: Systematic M-combination search")
    print("=" * 78)

    qr_classes = {1, 121, 169, 289, 361, 529}

    # Collect M values and their coverage
    M_data = {}
    for M in range(3, 5000, 4):
        residues = get_residues_for_M(M)
        if not residues:
            continue
        covered = set()
        for cls in qr_classes:
            if cls % M in residues:
                covered.add(cls)
        if covered:
            M_data[M] = covered

    print(f"M values covering at least one QR class: {len(M_data)}")

    # Try to find a covering with small number of M values
    # Greedy: pick M covering most uncovered classes
    uncov = set(qr_classes)
    selected = []
    Q = 840

    for iteration in range(10):
        if not uncov:
            break

        best_M = None
        best_gain = 0
        best_Q = None

        for M, covered in M_data.items():
            gain = len(covered & uncov)
            if gain == 0:
                continue
            new_Q = lcm2(Q, M)
            if gain > best_gain or (gain == best_gain and new_Q < (best_Q or float('inf'))):
                best_gain = gain
                best_M = M
                best_Q = new_Q

        if best_M is None:
            break

        selected.append(best_M)
        newly_covered = M_data[best_M] & uncov
        uncov -= newly_covered
        Q = lcm2(Q, best_M)

        # Show triples for this M
        k = (best_M + 1) // 4
        print(f"\n  #{iteration+1}: M={best_M} (αsr={k})")
        print(f"    Covers: {newly_covered}, Q now = {Q:,}")

        # Show which triple covers each class
        for cls in sorted(newly_covered):
            for a in divisors(k):
                rem = k // a
                for s in divisors(rem):
                    r = rem // s
                    res = (-4 * a * s * s) % best_M
                    if cls % best_M == res:
                        print(f"    Class {cls}: (r={r}, s={s}, α={a}), P≡{res}(mod {best_M})")
                        break
                else:
                    continue
                break

    if uncov:
        print(f"\n  Uncovered after D.6 search: {uncov}")

        # Now try divisor-pair for remaining
        print(f"\n  Trying divisor-pair for uncovered classes...")
        for cls in sorted(uncov):
            dp = analyze_dp_for_class(cls, max_delta=5000)
            if dp:
                # Find smallest modulus DP construction
                best = min(dp, key=lambda x: x[3])
                delta, u, v, mod, res = best
                print(f"    Class {cls}: DP delta={delta}, u={u}, v={v}, mod={mod}")
                # Check compatibility
                new_Q = lcm2(Q, mod)
                print(f"      Adding mod={mod}: Q becomes {new_Q:,}")
            else:
                print(f"    Class {cls}: NO DP construction found!")
    else:
        print(f"\n  *** COMPLETE D.6 COVERING! Q = {Q:,} ***")

    return selected, Q, uncov


# =================================================================
# Main
# =================================================================

def main():
    t0 = time.time()

    qr_classes = [1, 121, 169, 289, 361, 529]
    print("QR gap classes mod 840:", qr_classes)
    print("These are P ≡ 1 (mod 24) with P%7 in {1,2,4} and P%5 in {1,4}")
    print()

    # Phase 1: D.6 analysis
    M_covers, class_to_M = analyze_d6_coverage_of_qr_gap(max_M=5000)

    # Phase 2: Minimal covering
    selected, Q, complete = find_minimal_covering(M_covers, qr_classes)

    if not complete:
        uncovered = set(qr_classes)
        for M in selected:
            uncovered -= M_covers.get(M, set())

        # Phase 3: DP analysis for uncovered
        analyze_dp_coverage(qr_classes, uncovered, max_delta=2000)

    # Phase 4: Verify primes
    failures, max_delta = verify_qr_gap_primes(max_P=1_000_000)

    # Phase 5: Systematic search
    check_specific_M_combinations()

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
