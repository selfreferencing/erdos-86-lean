#!/usr/bin/env python3
"""
Covering search v2: Systematic Q growth with full M-value enumeration.

Key improvements over v1:
  1. Dirichlet optimization: only target coprime residue classes
     (non-coprime classes contain at most finitely many primes, handled separately)
  2. Uses ALL M values dividing Q (both prime and composite)
  3. CRT-based enumeration for efficient coverage computation
  4. Incrementally grows Q by adding primes + prime powers

Mathematical setup (Dyachenko Lemma D.6 + Theorem D.14):
  - For (r, s, alpha) with M = 4*alpha*s*r - 1, if M | (4*alpha*s^2 + P),
    then P has an ED2 solution with A = alpha*s*(m*r - s).
  - The divisibility condition is: P ≡ -4*alpha*s^2 (mod M).
  - If a finite set of triples covers ALL residues P ≡ 1 (mod 24) mod Q,
    then every prime P ≡ 1 (mod 24) has a solution (for P > some bound;
    small P checked by native_decide).
"""

import sys
import time
from math import gcd
from functools import reduce
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
    """Return sorted list of all divisors of n."""
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


def ordered_factorizations_3(n):
    """All ordered (a, s, r) with a*s*r = n, a,s,r >= 1."""
    divs = divisors(n)
    result = []
    for a in divs:
        rem = n // a
        for s in divisors(rem):
            result.append((a, s, rem // s))
    return result


def get_residues_for_M(M):
    """All distinct residues (-4*alpha*s^2) mod M for Lemma D.6 triples with this M."""
    k = (M + 1) // 4
    if 4 * k - 1 != M:
        return set()
    seen = set()
    for alpha, s, r in ordered_factorizations_3(k):
        res = (-4 * alpha * s * s) % M
        seen.add(res)
    return seen


def get_triples_for_M(M):
    """All (r, s, alpha, residue) tuples for a given M."""
    k = (M + 1) // 4
    if 4 * k - 1 != M:
        return []
    seen = set()
    triples = []
    for alpha, s, r in ordered_factorizations_3(k):
        res = (-4 * alpha * s * s) % M
        if res not in seen:
            seen.add(res)
            triples.append((r, s, alpha, res))
    return triples


def ed2_check(P, r, s, alpha):
    """Try Lemma D.6 construction. Returns (offset, b, c, A) or None."""
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


def min_P_for_window(r, s, alpha):
    """Minimum P for the affine window condition A in [L(P), U(P)]."""
    bound1 = 4 * alpha * s * (3 * r - s) - 3
    num = 4 * alpha * s * s + 12 * alpha * s * r - 3
    den = 8 * alpha * s * r - 3
    if den > 0:
        bound2 = -(-num // den)
    else:
        bound2 = 0
    return max(bound1, bound2, 5)


# ══════════════════════════════════════════════════════════════════════════
# Phase 1: Build modular covering by incrementally growing Q
# ══════════════════════════════════════════════════════════════════════════

def build_covering(max_Q=50_000_000, verbose=True):
    """Systematically grow Q and compute coverage."""

    Q = 24

    # Factors to add: primes and small prime powers
    # Both p ≡ 1 (mod 4) and p ≡ 3 (mod 4) are useful:
    #   p ≡ 3 mod 4: creates prime M = p directly (e.g., 7, 11, 19, 23, ...)
    #   p ≡ 1 mod 4: creates composite M values (e.g., 5 -> M=15=3*5, M=35=5*7)
    #   prime powers: creates new M values (e.g., 9 -> M=27)
    factors_to_add = [5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 31, 37, 41,
                      43, 47, 49, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
                      101, 103, 107, 109, 113, 121, 125, 127, 131, 137, 139,
                      149, 151, 157, 163, 167, 169, 173, 179, 181, 191, 193, 197, 199]

    best_Q = Q
    best_pct = 0.0
    best_M_data = {}

    if verbose:
        print("=" * 78)
        print("PHASE 1: Building modular covering")
        print("=" * 78)
        print(f"{'Q':>14} | {'factor':>6} | {'M-vals':>6} | {'resids':>6} | "
              f"{'covered':>9} / {'target':>7} | {'pct':>7} | {'uncov':>6}")
        print("-" * 78)

    for factor in factors_to_add:
        new_Q = lcm2(Q, factor)
        if new_Q == Q:
            continue  # factor already divides Q
        if new_Q > max_Q:
            if verbose:
                print(f"  [skip factor {factor}: Q would be {new_Q:,}]")
            continue

        Q = new_Q

        # Find all M values ≡ 3 (mod 4) dividing odd part of Q
        oQ = odd_part(Q)
        M_values = [d for d in divisors(oQ) if d % 4 == 3 and d >= 3]

        # For each M, compute all available residues
        M_residue_map = {}
        total_residues = 0
        for M in M_values:
            residues = get_residues_for_M(M)
            if residues:
                M_residue_map[M] = residues
                total_residues += len(residues)

        # Compute coverage: coprime targets ≡ 1 (mod 24)
        target_count = 0
        covered_count = 0

        for x in range(1, Q, 24):  # x ≡ 1 (mod 24)
            if gcd(x, Q) != 1:
                continue
            target_count += 1
            for M in M_residue_map:
                if x % M in M_residue_map[M]:
                    covered_count += 1
                    break

        uncov = target_count - covered_count
        pct = 100.0 * covered_count / target_count if target_count > 0 else 0

        if verbose:
            print(f"{Q:>14,d} | {factor:>6} | {len(M_values):>6} | "
                  f"{total_residues:>6} | {covered_count:>9,d} / {target_count:>7,d} | "
                  f"{pct:>6.2f}% | {uncov:>6,d}")

        if pct > best_pct:
            best_pct = pct
            best_Q = Q
            best_M_data = dict(M_residue_map)

        if covered_count == target_count:
            if verbose:
                print()
                print("*" * 78)
                print("*** COMPLETE COVERING FOUND ***")
                print(f"*** Q = {Q:,} ***")
                print("*" * 78)
            return Q, M_residue_map, True

    if verbose:
        print()
        print(f"Covering incomplete at Q = {Q:,}")
        print(f"Best coverage: {best_pct:.4f}% at Q = {best_Q:,}")

    return best_Q, best_M_data, False


# ══════════════════════════════════════════════════════════════════════════
# Phase 2: Analyze uncovered classes
# ══════════════════════════════════════════════════════════════════════════

def analyze_uncovered(Q, M_residue_map, max_show=30):
    """Identify and analyze uncovered coprime target classes."""
    print(f"\n{'=' * 78}")
    print("PHASE 2: Analyzing uncovered classes")
    print(f"{'=' * 78}")

    uncovered = []
    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        covered = False
        for M in M_residue_map:
            if x % M in M_residue_map[M]:
                covered = True
                break
        if not covered:
            uncovered.append(x)

    print(f"Total uncovered coprime classes: {len(uncovered)}")

    if not uncovered:
        return uncovered

    # For each uncovered class, show its residues mod small M values
    small_Ms = sorted(M for M in M_residue_map if M <= 100)[:12]
    print(f"\nResidues of uncovered classes mod small M values:")
    print(f"  {'x':>10} | " + " | ".join(f"M={M}" for M in small_Ms[:8]))
    print("  " + "-" * 70)

    for x in uncovered[:max_show]:
        parts = [f"{x % M:>4}" for M in small_Ms[:8]]
        print(f"  {x:>10} | " + " | ".join(parts))

    if len(uncovered) > max_show:
        print(f"  ... ({len(uncovered) - max_show} more)")

    # Check pattern: are uncovered classes concentrated in certain residues?
    print(f"\nResidue distribution of uncovered classes:")
    for M in small_Ms[:8]:
        residues = M_residue_map.get(M, set())
        dist = defaultdict(int)
        for x in uncovered:
            dist[x % M] += 1
        uncov_residues = sorted(dist.keys())
        print(f"  mod {M:>3}: uncov residues = {uncov_residues[:15]}"
              f"{'...' if len(uncov_residues) > 15 else ''}"
              f"  (available: {sorted(residues)[:15]})")

    return uncovered


# ══════════════════════════════════════════════════════════════════════════
# Phase 3: Verify against actual primes
# ══════════════════════════════════════════════════════════════════════════

def verify_primes(M_residue_map, max_P=500000):
    """Verify every prime P ≡ 1 (mod 24) up to max_P."""
    print(f"\n{'=' * 78}")
    print(f"PHASE 3: Verifying primes P ≡ 1 (mod 24) up to {max_P:,}")
    print(f"{'=' * 78}")

    failures = []
    checked = 0
    verified_by_covering = 0
    verified_by_search = 0

    for P in range(25, max_P + 1, 24):
        if not is_prime(P):
            continue
        checked += 1

        # Try covering first
        found = False
        for M, residues in M_residue_map.items():
            if P % M not in residues:
                continue
            # Find the actual triple and verify construction
            triples = get_triples_for_M(M)
            for r, s, alpha, res in triples:
                if P % M == res:
                    result = ed2_check(P, r, s, alpha)
                    if result is not None:
                        found = True
                        verified_by_covering += 1
                        break
            if found:
                break

        if not found:
            # Exhaustive search with larger parameters
            for alpha in range(1, 20):
                if found: break
                for s in range(1, 60):
                    if found: break
                    for r in range(1, 60):
                        result = ed2_check(P, r, s, alpha)
                        if result is not None:
                            found = True
                            verified_by_search += 1
                            break

        if not found:
            failures.append(P)

    print(f"Checked: {checked} primes")
    print(f"  By covering: {verified_by_covering}")
    print(f"  By search:   {verified_by_search}")
    if failures:
        print(f"  FAILURES:    {len(failures)}: {failures[:30]}")
    else:
        print(f"  ALL {checked} PRIMES VERIFIED!")

    return failures


# ══════════════════════════════════════════════════════════════════════════
# Phase 4: For each failure, find what triple works and its M value
# ══════════════════════════════════════════════════════════════════════════

def diagnose_failures(failures, max_r=80, max_s=80, max_alpha=20):
    """For each failure, find a working triple and report its M value."""
    print(f"\n{'=' * 78}")
    print(f"PHASE 4: Diagnosing {len(failures)} failures")
    print(f"{'=' * 78}")

    extra_M_values = defaultdict(set)
    still_failed = []

    for P in failures:
        found = False
        for alpha in range(1, max_alpha + 1):
            if found: break
            for s in range(1, max_s + 1):
                if found: break
                for r in range(1, max_r + 1):
                    result = ed2_check(P, r, s, alpha)
                    if result is not None:
                        offset, b, c, A = result
                        M = 4 * alpha * s * r - 1
                        res = (-4 * alpha * s * s) % M
                        print(f"  P={P:>7}: (r={r}, s={s}, a={alpha}) "
                              f"M={M}, res={res}, offset={offset}, A={A}")
                        extra_M_values[M].add(res)
                        found = True
                        break
        if not found:
            still_failed.append(P)
            print(f"  P={P:>7}: NO SOLUTION FOUND")

    if extra_M_values:
        print(f"\nExtra M values needed (not in current Q):")
        for M in sorted(extra_M_values):
            print(f"  M={M}: residues {sorted(extra_M_values[M])}")

    return extra_M_values, still_failed


# ══════════════════════════════════════════════════════════════════════════
# Phase 5: Summary for Lean formalization
# ══════════════════════════════════════════════════════════════════════════

def print_lean_summary(Q, M_residue_map, complete):
    """Print results in a format useful for Lean formalization."""
    print(f"\n{'=' * 78}")
    print("SUMMARY FOR LEAN FORMALIZATION")
    print(f"{'=' * 78}")

    if complete:
        print(f"COMPLETE COVERING with Q = {Q:,}")
    else:
        print(f"PARTIAL COVERING with Q = {Q:,}")

    # Collect all triples
    all_triples = []
    for M in sorted(M_residue_map.keys()):
        triples = get_triples_for_M(M)
        for r, s, alpha, res in triples:
            all_triples.append((r, s, alpha, M, res))

    print(f"Total triples: {len(all_triples)}")
    print(f"Distinct M values: {len(M_residue_map)}")

    # Max window bound
    max_bound = 0
    for r, s, alpha, M, res in all_triples:
        b = min_P_for_window(r, s, alpha)
        if b > max_bound:
            max_bound = b

    print(f"Max window bound: P >= {max_bound}")
    print(f"  (need native_decide for primes below this)")

    # Print M values
    print(f"\nM values and residue counts:")
    for M in sorted(M_residue_map.keys()):
        res = sorted(M_residue_map[M])
        count = len(res)
        print(f"  M={M:>6}: {count:>3} residues: {res[:20]}{'...' if count > 20 else ''}")


# ══════════════════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    # Phase 1: Build covering
    Q, M_data, complete = build_covering(max_Q=50_000_000)

    # Phase 2: Analyze uncovered classes (if incomplete)
    if not complete:
        uncovered = analyze_uncovered(Q, M_data)

    # Phase 3: Verify against actual primes
    failures = verify_primes(M_data, max_P=500_000)

    # Phase 4: Diagnose any failures
    if failures:
        extra, still = diagnose_failures(failures)

    # Phase 5: Summary
    print_lean_summary(Q, M_data, complete)

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
