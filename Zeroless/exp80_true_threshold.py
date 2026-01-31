"""
Exp 80: Finding the True Threshold M_0

Key findings so far:
- 2^649 has a 75-digit zeroless prefix
- 2^4201 has an 89-digit zeroless prefix!

We need to find the TRUE maximum and understand the threshold.
"""

import sys
sys.set_int_max_str_digits(50000)  # Allow very large numbers


def get_digits_str(n):
    """Get digit string of 2^n."""
    return str(2 ** n)


def max_zeroless_prefix_length(n):
    """Find the maximum m such that 2^n has a zeroless m-prefix."""
    s = get_digits_str(n)
    for m in range(1, len(s) + 1):
        if '0' in s[:m]:
            return m - 1
    return len(s)  # Fully zeroless


def main():
    print("=" * 70)
    print("Exp 80: Finding the True Threshold M_0")
    print("=" * 70)

    # Part A: Survey known champions
    print("\n" + "=" * 70)
    print("PART A: Known Champions and Their Prefix Lengths")
    print("=" * 70)

    # From previous experiment
    known_champions = [649, 4201, 8193, 4368, 8945, 4367, 5266, 7008, 3242, 6466]

    print("\n  n     | Max prefix | First zero position")
    print("-" * 50)

    for n in known_champions:
        max_pf = max_zeroless_prefix_length(n)
        s = get_digits_str(n)
        first_zero = s.index('0') if '0' in s else len(s)
        print(f"  {n:5} | {max_pf:10} | {first_zero}")

    # Part B: Search for larger prefixes in [1, 15000]
    print("\n" + "=" * 70)
    print("PART B: Search for Maximum Zeroless Prefix in [1, 15000]")
    print("=" * 70)

    global_max = 0
    global_max_n = 0
    champions_70_plus = []

    print("\nSearching...")

    for n in range(1, 15001):
        if n % 2000 == 0:
            print(f"  Progress: n = {n}, current max = {global_max} (at n={global_max_n})")

        max_pf = max_zeroless_prefix_length(n)
        if max_pf >= 70:
            champions_70_plus.append((n, max_pf))
        if max_pf > global_max:
            global_max = max_pf
            global_max_n = n

    print(f"\nGlobal max in [1, 15000]: n = {global_max_n}, prefix = {global_max}")

    # Sort champions
    champions_70_plus.sort(key=lambda x: -x[1])
    print(f"\nTop 20 champions (prefix ≥ 70):")
    for n, pf in champions_70_plus[:20]:
        print(f"  n = {n:5}: {pf}-digit zeroless prefix")

    # Part C: Analyze the champion
    print("\n" + "=" * 70)
    print(f"PART C: Analysis of Champion 2^{global_max_n}")
    print("=" * 70)

    s = get_digits_str(global_max_n)
    print(f"\n2^{global_max_n} has {len(s)} digits")
    print(f"Maximum zeroless prefix: {global_max}")
    print(f"First zero at position: {s.index('0')}")
    print(f"\nFirst 100 digits:")
    print(f"  {s[:100]}")

    # Part D: What is the distribution of max prefix lengths?
    print("\n" + "=" * 70)
    print("PART D: Distribution of Max Prefix Lengths")
    print("=" * 70)

    # Bucket by prefix length
    from collections import Counter
    prefix_dist = Counter()

    for n in range(1, 15001):
        max_pf = max_zeroless_prefix_length(n)
        # Bucket into ranges
        bucket = (max_pf // 10) * 10
        prefix_dist[bucket] += 1

    print("\n  Prefix range | Count")
    print("-" * 30)
    for bucket in sorted(prefix_dist.keys(), reverse=True):
        if bucket >= 40:
            print(f"  {bucket:3}-{bucket+9:3}      | {prefix_dist[bucket]}")

    # Part E: The threshold analysis
    print("\n" + "=" * 70)
    print("PART E: True Threshold Analysis")
    print("=" * 70)

    print(f"""
Based on search up to n = 15000:

Maximum zeroless prefix found: {global_max} (at n = {global_max_n})

This means:
- For m ≤ {global_max}: there exists n with zeroless m-prefix
- For m > {global_max}: no witness found in [1, 15000]

The TRUE threshold M_0 satisfies:
  {global_max + 1} ≤ M_0

To prove the conjecture, we need to either:
1. Show M_0 is finite (exists a computable upper bound)
2. Or show M_0 ≤ some specific value and verify exhaustively
""")

    # Part F: Check for witnesses at even larger n
    print("=" * 70)
    print("PART F: Extended Search [15000, 25000]")
    print("=" * 70)

    print("\nSearching for prefix > 89 in [15000, 25000]...")

    found_larger = False
    for n in range(15001, 25001):
        if n % 2000 == 0:
            print(f"  Progress: n = {n}")
        max_pf = max_zeroless_prefix_length(n)
        if max_pf > 89:
            print(f"  NEW CHAMPION: n = {n}, prefix = {max_pf}!")
            found_larger = True
            if max_pf > global_max:
                global_max = max_pf
                global_max_n = n

    if not found_larger:
        print("  No prefix > 89 found in this range")

    print(f"\nFinal global max: n = {global_max_n}, prefix = {global_max}")


if __name__ == "__main__":
    main()
