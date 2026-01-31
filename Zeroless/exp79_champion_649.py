"""
Exp 79: The Champion 2^649 and the True Threshold

2^649 has a zeroless 75-digit prefix, making it the last witness for m = 75.
What makes it special? And what is the true threshold M_0?
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


def max_zeroless_prefix_length(n):
    """Find the maximum m such that 2^n has a zeroless m-prefix."""
    s = get_digits_str(n)
    for m in range(1, len(s) + 1):
        if '0' in s[:m]:
            return m - 1
    return len(s)  # Fully zeroless


def main():
    print("=" * 70)
    print("Exp 79: The Champion 2^649 and the True Threshold")
    print("=" * 70)

    # Part A: Analyze 2^649
    print("\n" + "=" * 70)
    print("PART A: Analysis of 2^649")
    print("=" * 70)

    n = 649
    s = get_digits_str(n)
    d = len(s)

    print(f"\n2^{n} has {d} digits")
    print(f"Total zeros: {count_zeros(s)}")

    # Find zero positions
    zero_pos = [i for i, c in enumerate(s) if c == '0']
    print(f"Zero positions (MSB=0): {zero_pos}")

    # Max zeroless prefix
    max_prefix = max_zeroless_prefix_length(n)
    print(f"Maximum zeroless prefix length: {max_prefix}")

    print(f"\nFirst 80 digits of 2^{n}:")
    print(f"  {s[:80]}")
    print(f"  {''.join(['^' if c == '0' else ' ' for c in s[:80]])}")

    # Part B: Find ALL champions (n with large zeroless prefix)
    print("\n" + "=" * 70)
    print("PART B: All Champions with Zeroless Prefix ≥ 50")
    print("=" * 70)

    print("\nSearching n in [100, 10000] for max zeroless prefix ≥ 50...")
    print()

    champions = []
    for n in range(100, 10001):
        max_pf = max_zeroless_prefix_length(n)
        if max_pf >= 50:
            champions.append((n, max_pf))

    # Sort by prefix length
    champions.sort(key=lambda x: -x[1])

    print(f"Found {len(champions)} champions:")
    print()
    print("  n     | Max prefix | Digit count | Total zeros")
    print("-" * 55)

    for n, max_pf in champions[:30]:
        s = get_digits_str(n)
        total_zeros = count_zeros(s)
        print(f"  {n:5} | {max_pf:10} | {len(s):11} | {total_zeros:11}")

    # Part C: The TRUE threshold
    print("\n" + "=" * 70)
    print("PART C: Finding the TRUE Threshold M_0")
    print("=" * 70)

    # Find max prefix length among all n up to some limit
    max_prefixes = []
    search_limit = 10000

    print(f"\nSearching n in [1, {search_limit}] for maximum zeroless prefix...")

    global_max = 0
    global_max_n = 0

    for n in range(1, search_limit + 1):
        max_pf = max_zeroless_prefix_length(n)
        if max_pf > global_max:
            global_max = max_pf
            global_max_n = n

    print(f"\nGlobal maximum zeroless prefix in [1, {search_limit}]:")
    print(f"  n = {global_max_n}: {global_max}-digit zeroless prefix")

    s = get_digits_str(global_max_n)
    print(f"  2^{global_max_n} = {s[:50]}...")
    print(f"  First zero at position: {s.index('0')}")

    # Part D: Is there an n > 10000 with larger prefix?
    print("\n" + "=" * 70)
    print("PART D: Extended Search for Larger Prefixes")
    print("=" * 70)

    print("\nSearching n in [10000, 20000] for max prefix > 75...")

    found_larger = False
    for n in range(10001, 20001):
        max_pf = max_zeroless_prefix_length(n)
        if max_pf > 75:
            print(f"  n = {n}: {max_pf}-digit zeroless prefix!")
            found_larger = True
            if max_pf > global_max:
                global_max = max_pf
                global_max_n = n

    if not found_larger:
        print("  No prefix > 75 found")

    print(f"\nUpdated global max: n = {global_max_n}, prefix = {global_max}")

    # Part E: Density of champions
    print("\n" + "=" * 70)
    print("PART E: Density of Champions by Prefix Length")
    print("=" * 70)

    print("\nCount of n in [1, 10000] with max zeroless prefix = k:")
    print()

    prefix_counts = {}
    for n in range(1, 10001):
        max_pf = max_zeroless_prefix_length(n)
        prefix_counts[max_pf] = prefix_counts.get(max_pf, 0) + 1

    print("  k  | Count | Cumulative ≥ k")
    print("-" * 35)

    cumulative = 10000
    for k in sorted(prefix_counts.keys(), reverse=True):
        if k >= 50:
            print(f" {k:3} | {prefix_counts[k]:5} | {cumulative:14}")
        cumulative -= prefix_counts[k]

    # Part F: The true threshold
    print("\n" + "=" * 70)
    print("PART F: The True Threshold M_0")
    print("=" * 70)

    print(f"""
Based on the search up to n = {max(20000, search_limit)}:

The TRUE threshold M_0 = {global_max + 1}

This means:
1. For m ≤ {global_max}: there exists n with zeroless m-prefix
   (witness: 2^{global_max_n})

2. For m ≥ {global_max + 1}: NO n in [1, {max(20000, search_limit)}] has zeroless m-prefix
   (needs verification with larger search)

3. If M_0 = {global_max + 1} is the TRUE threshold:
   - Any 2^n with n ≥ {global_max + 1} has a zero in first {global_max + 1} digits
   - Hence cannot be fully zeroless
   - Combined with exhaustive verification for n < {global_max + 1}: proves conjecture

4. The proof structure:
   - Show M_0 ≤ some computable bound
   - Exhaustively verify 2^n for n up to that bound
""")


if __name__ == "__main__":
    main()
