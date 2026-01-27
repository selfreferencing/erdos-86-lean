#!/usr/bin/env python3
"""
Phase 3 Coverage Analysis: Can D.6 cover ALL CRT classes in the sorry region?

The sorry region is defined by:
  p % 24 = 1
  p % 7 in {1, 2, 4}
  p % 5 in {1, 4}
  p % 11 not in {0, 7, 8, 10}  => {1,2,3,4,5,6,9}
  p % 19 not in {0, 14, 15, 18} => {1,2,3,4,5,6,7,8,9,10,11,12,13,16,17}
  p % 23 not in {0, 7,10,11,15,17,19,20,21,22} => {1,2,3,4,5,6,8,9,12,13,14,16,18}

Total CRT classes: 1 * 3 * 2 * 7 * 15 * 13 = 8,190

For each class, we check if any D.6 M-value provides coverage.
"""

import math
from itertools import product


def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def crt_solve(r1, m1, r2, m2):
    g, p, q = extended_gcd(m1, m2)
    if (r2 - r1) % g != 0:
        return None, None
    lcm_val = m1 * m2 // g
    sol = (r1 + m1 * ((r2 - r1) // g) * p) % lcm_val
    return sol, lcm_val


def ordered_factorizations_3(n):
    result = []
    for a in range(1, n + 1):
        if n % a != 0:
            continue
        rem = n // a
        for r in range(1, rem + 1):
            if rem % r != 0:
                continue
            s = rem // r
            result.append((a, r, s))
    return result


def compute_covered_residues(M):
    """Compute all residues mod M covered by D.6, filtered for CRT compatibility with p%24=1."""
    if (M + 1) % 4 != 0:
        return set()
    b_param = (M + 1) // 4
    facts = ordered_factorizations_3(b_param)

    covered = set()
    for alpha, r, s in facts:
        res = (-4 * alpha * s * s) % M
        # CRT compatibility: does p%24=1 and p%M=res have a solution?
        sol, mod = crt_solve(1, 24, res, M)
        if sol is not None:
            covered.add(res)
    return covered


def build_sorry_region_classes():
    """Build all CRT classes in the sorry region."""
    mod24_vals = [1]
    mod7_vals = [1, 2, 4]
    mod5_vals = [1, 4]
    mod11_vals = [1, 2, 3, 4, 5, 6, 9]
    mod19_vals = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17]
    mod23_vals = [1, 2, 3, 4, 5, 6, 8, 9, 12, 13, 14, 16, 18]

    classes = []
    for r24, r7, r5, r11, r19, r23 in product(
        mod24_vals, mod7_vals, mod5_vals, mod11_vals, mod19_vals, mod23_vals
    ):
        # Combine via CRT
        val, mod = r24, 24
        for r, m in [(r7, 7), (r5, 5), (r11, 11), (r19, 19), (r23, 23)]:
            val, mod = crt_solve(val, mod, r, m)
            if val is None:
                break
        if val is not None:
            classes.append(val)

    return classes, mod  # mod should be 4037880


def check_class_covered(class_val, Q, M, covered_residues):
    """Check if a CRT class (class_val mod Q) is FULLY covered by M.

    A class is covered if for ALL p in that class, p%M falls in covered_residues.
    Since p ranges over class_val, class_val+Q, class_val+2Q, ...,
    the residues p%M cycle through {(class_val + k*Q) % M : k = 0, ..., M/gcd(Q,M)-1}.

    The class is covered if ALL such residues are in covered_residues.
    """
    g = math.gcd(Q, M)
    period = M // g
    for k in range(period):
        r = (class_val + k * Q) % M
        if r not in covered_residues:
            return False
    return True


def check_class_covered_any(class_val, Q, M, covered_residues):
    """Check if ANY p in a CRT class is covered by M.
    Returns the set of sub-residues that ARE covered."""
    g = math.gcd(Q, M)
    period = M // g
    covered_sub = set()
    for k in range(period):
        r = (class_val + k * Q) % M
        if r in covered_residues:
            covered_sub.add(k)
    return covered_sub


def main():
    print("=" * 70)
    print("Phase 3 Coverage Analysis")
    print("=" * 70)

    # Build sorry-region classes
    classes, Q = build_sorry_region_classes()
    print(f"\nSorry region: {len(classes)} CRT classes mod {Q}")

    # Current M values (inline + helpers)
    inline_M = {
        11: {7, 8, 10},
        19: {14, 15, 18},
        23: {7, 10, 11, 15, 17, 19, 20, 21, 22},
    }
    helper_Ms = [39, 47, 119, 159, 71, 95, 111, 143, 79, 87, 151, 59,
                 191, 155, 199, 83, 127, 43, 99, 107, 131, 167]

    # Compute covered residues for all M values
    all_M_coverage = {}
    for M, residues in inline_M.items():
        all_M_coverage[M] = residues
    for M in helper_Ms:
        all_M_coverage[M] = compute_covered_residues(M)

    print(f"\nCurrent M values: {len(all_M_coverage)}")
    for M in sorted(all_M_coverage.keys()):
        print(f"  M={M}: {len(all_M_coverage[M])} covered residues")

    # Check which classes are FULLY covered
    # A class is fully covered if for EVERY prime p in that class,
    # at least one M value handles it.
    #
    # More precisely: class c is covered if for every p ≡ c (mod Q),
    # there exists M such that p%M is in covered_residues[M].
    #
    # This is equivalent to: the intersection of "uncovered sets"
    # across all M values is empty for this class.
    #
    # For each M, the class c generates residues {(c + k*Q) % M : k in range(M/gcd(Q,M))}.
    # The class is covered by M if ALL these residues are in covered_residues[M].
    # The class is covered by the UNION if for each k, SOME M covers (c+kQ)%M.
    #
    # Actually this is more subtle. Let me think again.
    #
    # A prime p ≡ c (mod Q) is covered if SOME M has p%M in covered[M].
    # The class c is "fully covered" if ALL primes p ≡ c (mod Q) are covered.
    # That means: for every p ≡ c (mod Q), exists M with p%M in covered[M].
    #
    # To check this, we need to work at the finer level of lcm(Q, M1, M2, ...).
    # But that's astronomically large. Instead, let's check a sufficient condition:
    # the class is fully covered if SOME SINGLE M covers it entirely.

    # First pass: check single-M full coverage
    fully_covered_single = set()
    for i, c in enumerate(classes):
        for M, cov in all_M_coverage.items():
            if check_class_covered(c, Q, M, cov):
                fully_covered_single.add(i)
                break

    n_covered_single = len(fully_covered_single)
    n_uncovered = len(classes) - n_covered_single
    print(f"\nClasses fully covered by a single M: {n_covered_single}/{len(classes)}")
    print(f"Classes NOT fully covered by any single M: {n_uncovered}")

    if n_uncovered == 0:
        print("\n*** ALL CLASSES COVERED! Sorry can be eliminated! ***")
        return

    # Collect uncovered class indices
    uncovered_indices = [i for i in range(len(classes)) if i not in fully_covered_single]

    # For uncovered classes, check what fraction is covered by combining M values
    # This requires checking at the sub-class level
    # Let's check: for each uncovered class, what's the best single M?
    print(f"\nAnalyzing {n_uncovered} uncovered classes...")

    # Try to find new M values that help
    print("\nSearching for additional M values (M up to 5000)...")

    # First, let's understand the uncovered classes better
    uncovered_classes = [classes[i] for i in uncovered_indices]

    # Greedy search for new M values
    best_new_Ms = []
    remaining = set(range(len(uncovered_classes)))

    for trial_round in range(50):  # up to 50 new M values
        if not remaining:
            break

        best_M = None
        best_count = 0
        best_covered = set()

        # Search M values from 3 to 5000 (must be ≡ 3 mod 4)
        for M_candidate in range(3, 5001, 4):
            if M_candidate in all_M_coverage:
                continue
            cov = compute_covered_residues(M_candidate)
            if not cov:
                continue

            # Count how many remaining uncovered classes this M fully covers
            newly_covered = set()
            for idx in remaining:
                c = uncovered_classes[idx]
                if check_class_covered(c, Q, M_candidate, cov):
                    newly_covered.add(idx)

            if len(newly_covered) > best_count:
                best_count = len(newly_covered)
                best_M = M_candidate
                best_covered = newly_covered

        if best_M is None or best_count == 0:
            print(f"  Round {trial_round + 1}: No M value found. {len(remaining)} classes remain uncovered.")
            break

        best_new_Ms.append((best_M, best_count))
        remaining -= best_covered
        all_M_coverage[best_M] = compute_covered_residues(best_M)
        print(f"  Round {trial_round + 1}: M={best_M} covers {best_count} new classes. "
              f"{len(remaining)} remain.")

    print(f"\nNew M values found: {len(best_new_Ms)}")
    for M, count in best_new_Ms:
        print(f"  M={M}: covers {count} classes")

    if not remaining:
        print(f"\n*** ALL CLASSES NOW COVERED with {len(best_new_Ms)} additional M values! ***")
        print(f"Total M values needed: {len(all_M_coverage)}")
        print(f"New M values to add: {[m for m, _ in best_new_Ms]}")
    else:
        print(f"\n{len(remaining)} classes STILL uncovered after greedy search up to M=5000.")
        print("These classes may require the asymptotic argument or larger M values.")

        # Print some example uncovered classes
        print("\nExample uncovered classes:")
        for idx in list(remaining)[:10]:
            c = uncovered_classes[idx]
            print(f"  class {c} mod {Q}: "
                  f"p%24={c%24}, p%7={c%7}, p%5={c%5}, "
                  f"p%11={c%11}, p%19={c%19}, p%23={c%23}")


if __name__ == "__main__":
    main()
