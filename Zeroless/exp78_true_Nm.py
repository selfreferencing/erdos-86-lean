"""
Exp 78: True N_m - Zeroless m-Prefixes at ALL n

Previous experiments used N_m = #{j ∈ [0, L_m) : 2^{m+j} has zeroless m-prefix}
But this misses witnesses at larger n values!

Let's compute the TRUE count of n values with zeroless m-prefix.
"""

import math


def get_digits_str(n):
    """Get digit string of 2^n."""
    return str(2 ** n)


def count_zeros(s):
    """Count zeros in string."""
    return s.count('0')


def has_zeroless_m_prefix(n, m):
    """Check if 2^n has a zeroless m-digit prefix."""
    s = get_digits_str(n)
    if len(s) < m:
        return False
    return count_zeros(s[:m]) == 0


def main():
    print("=" * 70)
    print("Exp 78: True N_m - Zeroless m-Prefixes at ALL n")
    print("=" * 70)

    log10_2 = math.log10(2)

    # Part A: Count ALL n with zeroless m-prefix up to n = 1000
    print("\n" + "=" * 70)
    print("PART A: True N_m for m = 30..50 (searching n up to 1000)")
    print("=" * 70)

    N_max = 1000

    print("\n  m  | Count | Witnesses (first 10)")
    print("-" * 70)

    for m in range(30, 51):
        witnesses = []
        for n in range(m, N_max + 1):  # n must be at least m for m digits
            if has_zeroless_m_prefix(n, m):
                witnesses.append(n)

        witness_str = str(witnesses[:10]) if len(witnesses) <= 10 else str(witnesses[:10]) + "..."
        print(f" {m:3} | {len(witnesses):5} | {witness_str}")

    # Part B: The key question - is there an m where NO witnesses exist?
    print("\n" + "=" * 70)
    print("PART B: Finding the True Threshold")
    print("=" * 70)

    print("\nSearching for smallest m with no witnesses in n ∈ [m, 2000]...")
    print()

    first_empty_m = None
    N_max = 2000

    for m in range(30, 80):
        has_witness = False
        for n in range(m, N_max + 1):
            if has_zeroless_m_prefix(n, m):
                has_witness = True
                break

        if not has_witness:
            if first_empty_m is None:
                first_empty_m = m
                print(f"*** m = {m}: NO witnesses found in [m, {N_max}] ***")
            elif m <= first_empty_m + 5:
                print(f"    m = {m}: NO witnesses (confirming)")
        elif first_empty_m is not None and m > first_empty_m:
            # Check if we found a witness after a gap
            witnesses = [n for n in range(m, N_max+1) if has_zeroless_m_prefix(n, m)]
            if witnesses:
                print(f"    m = {m}: witnesses found! {witnesses[:5]}")

    # Part C: Detailed analysis around the threshold
    print("\n" + "=" * 70)
    print("PART C: Detailed Analysis Near Threshold")
    print("=" * 70)

    if first_empty_m:
        for m in range(first_empty_m - 3, first_empty_m + 10):
            witnesses = [n for n in range(m, 3000) if has_zeroless_m_prefix(n, m)]
            count = len(witnesses)

            if count > 0:
                print(f"m = {m}: {count} witnesses, last = {max(witnesses)}")
                if count <= 10:
                    print(f"         All witnesses: {witnesses}")
            else:
                print(f"m = {m}: NO witnesses in [m, 3000)")

    # Part D: What is the TRUE threshold?
    print("\n" + "=" * 70)
    print("PART D: The True Threshold")
    print("=" * 70)

    # Find the actual threshold by extending the search
    print("\nExtending search to n = 5000...")

    threshold_candidates = []
    for m in range(50, 100):
        has_witness = any(has_zeroless_m_prefix(n, m) for n in range(m, 5001))
        if not has_witness:
            threshold_candidates.append(m)
            if len(threshold_candidates) <= 5:
                print(f"  m = {m}: no witness in [m, 5000]")

    if threshold_candidates:
        print(f"\nCandidate true threshold: m = {min(threshold_candidates)}")
    else:
        print("\nNo threshold found up to m = 99 with search up to n = 5000")

    # Part E: Implications
    print("\n" + "=" * 70)
    print("PART E: Implications for the Conjecture")
    print("=" * 70)

    print("""
The TRUE threshold M_0 is the smallest m such that:
  No n exists with 2^n having a zeroless m-digit prefix.

If M_0 exists and is finite, then:
  - All 2^n with n >= M_0 have at least one zero in first M_0 digits
  - Hence cannot be fully zeroless
  - Combined with exhaustive check for small n, proves the conjecture

The original N_m definition was too restrictive (only checked [m, m+L_m)).
The true count can be larger because witnesses can appear at any n >= m.
""")


if __name__ == "__main__":
    main()
