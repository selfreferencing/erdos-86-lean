"""
Exp 81: Extended Search for True Maximum

Current champion: n = 23305 with 98-digit zeroless prefix
Let's search further to find the true maximum.
"""

import sys
sys.set_int_max_str_digits(100000)


def max_zeroless_prefix_length(n):
    """Find the maximum m such that 2^n has a zeroless m-prefix."""
    s = str(2 ** n)
    for m in range(1, len(s) + 1):
        if s[m-1] == '0':
            return m - 1
    return len(s)


def main():
    print("=" * 70)
    print("Exp 81: Extended Search for True Maximum")
    print("=" * 70)

    global_max = 98
    global_max_n = 23305

    # Search in ranges
    search_ranges = [
        (25000, 50000),
        (50000, 75000),
        (75000, 100000),
    ]

    for start, end in search_ranges:
        print(f"\n{'='*70}")
        print(f"Searching [{start}, {end}]...")
        print("=" * 70)

        for n in range(start, end + 1):
            if n % 5000 == 0:
                print(f"  Progress: n = {n}, current max = {global_max} (at n={global_max_n})")

            max_pf = max_zeroless_prefix_length(n)
            if max_pf > global_max:
                print(f"  NEW CHAMPION: n = {n}, prefix = {max_pf}!")
                global_max = max_pf
                global_max_n = n

        print(f"  Range [{start}, {end}] complete. Max = {global_max}")

        # Stop if no new champion in last 25000
        if global_max == 98 and end >= 50000:
            print("\n  No new champions in extended search. Stopping.")
            break

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    print(f"\nFinal global maximum: n = {global_max_n}, prefix = {global_max}")

    s = str(2 ** global_max_n)
    print(f"\n2^{global_max_n} has {len(s)} digits")
    print(f"First zero at position: {s.index('0')}")

    print(f"\nFirst 110 digits of 2^{global_max_n}:")
    print(f"  {s[:110]}")

    # Count champions by prefix length in [1, min(end, 100000)]
    print("\n" + "=" * 70)
    print("Champions Summary (prefix ≥ 80)")
    print("=" * 70)

    search_limit = min(end, 100000)
    champions = []

    print(f"\nCollecting champions in [1, {search_limit}]...")
    for n in range(1, search_limit + 1):
        max_pf = max_zeroless_prefix_length(n)
        if max_pf >= 80:
            champions.append((n, max_pf))

    champions.sort(key=lambda x: -x[1])
    print(f"\nFound {len(champions)} champions with prefix ≥ 80:")
    for n, pf in champions[:20]:
        print(f"  n = {n:6}: {pf}-digit prefix")

    # Implication
    print("\n" + "=" * 70)
    print("IMPLICATION FOR THE CONJECTURE")
    print("=" * 70)

    print(f"""
The TRUE threshold M_0 satisfies: M_0 > {global_max}

For the conjecture to hold via the prefix approach:
1. Need to show M_0 is FINITE (no arbitrarily long zeroless prefixes exist)
2. Need to find M_0 explicitly
3. Need to verify 2^n for all n up to some bound

Current status:
- Maximum found: {global_max}-digit prefix at n = {global_max_n}
- The search suggests M_0 might be large (>100?) or potentially unbounded

If M_0 is unbounded, the prefix approach cannot directly prove the conjecture.
Alternative approach: work with the full zeroless condition, not just prefixes.
""")


if __name__ == "__main__":
    main()
